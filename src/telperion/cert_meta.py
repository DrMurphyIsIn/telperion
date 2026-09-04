"""Structured proof metadata + a content-addressed cert index (AXLE ``extract_decls``).

This is the metadata sibling of :mod:`telperion.verify`.  Where ``verify`` answers
"does this Lean elaborate cleanly?", ``cert_meta`` answers "what IS this proof, and
have we seen its statement before?".  Two capabilities:

1.  :func:`extract_cert_meta` parses ONE emitted ``theorem <name> : <stmt> := by <proof>``
    block into a :class:`CertMeta` record — normalized statement, a stable content
    hash (so cosmetically-different-but-equal statements collide), proof length/lines,
    and per-tactic counts.  This lets Telperion regression-track proof COMPLEXITY over
    time (did a route get longer/heavier after an edit?).

2.  :class:`CertIndex` is a content-addressed index keyed by ``type_hash``.  Its
    :meth:`~CertIndex.duplicates` surfaces SHARED ATOMS — the same statement proved
    under different names across cells/families — which is the dedup target for a future
    ``merge`` (prove once, reuse everywhere).

Optionally, :func:`measure_heartbeats` runs Mathlib's ``count_heartbeats in`` against a
built environment (cf. :func:`telperion.verify.verify_lean`) to attach a real elaboration
cost to a cert.  It degrades gracefully to ``None`` when the count can't be parsed.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

# Tactics we count for the complexity fingerprint.  Word-boundary regex counts in the
# proof body (so `linarith` inside `nlinarith` is NOT double-counted — see the ordering
# and \b anchors below).
_TACTICS = (
    "rw", "simp", "norm_num", "nlinarith", "linarith", "positivity",
    "ring", "push_cast", "field_simp", "exact", "gcongr", "calc", "have",
)

# Parse `theorem <name> : <stmt> := by <proof>`.  <stmt> ends at the FIRST `:=`.
# DOTALL so multi-line statements/proofs are captured.  Name allows Lean's dotted /
# primed identifiers (e.g. `R3Cert.BGSCL.log74_le_4fstar`, `foo'`).
_THEOREM_RE = re.compile(
    r"\btheorem\s+([A-Za-z_][A-Za-z0-9_.']*)\s*"   # name
    r"(.*?)"                                         # everything up to the first :=  (may include binders + `: stmt`)
    r":=\s*by\b(.*)",                                # proof body after `:= by`
    re.DOTALL,
)


def _normalize_statement(stmt: str) -> str:
    """Normalize a statement for content hashing.

    Strips ``: ℝ`` type ascriptions (both the unicode ``ℝ`` and the ascii ``Real``
    spelling) and collapses all whitespace, so two statements that differ only
    cosmetically hash to the SAME value.
    """
    s = stmt
    # Drop `: ℝ` / `:ℝ` ascriptions (unicode reals) and the `: Real` ascii spelling.
    s = re.sub(r":\s*ℝ\b", "", s)
    s = re.sub(r":\s*Real\b", "", s)
    # Collapse all whitespace to nothing so `a + b` == `a+b` == `a  +\n b`.
    s = re.sub(r"\s+", "", s)
    return s


def _type_hash(stmt: str) -> str:
    norm = _normalize_statement(stmt)
    return hashlib.sha256(norm.encode("utf-8")).hexdigest()[:16]


def _tactic_counts(proof_body: str) -> dict:
    counts = {}
    for tac in _TACTICS:
        counts[tac] = len(re.findall(r"\b" + re.escape(tac) + r"\b", proof_body))
    return counts


@dataclass
class CertMeta:
    """Structured metadata for one emitted Lean theorem."""

    name: str
    statement: str            # the type: text after `:` up to `:=`
    type_hash: str            # stable content hash of the normalized statement (16 hex)
    proof_length: int         # chars in the proof body after `:= by`
    n_lines: int              # lines spanned by the theorem block
    tactic_counts: dict       # tactic -> word-boundary count in the proof body
    heartbeats: object = None  # int | None — elaboration cost if measured

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "statement": self.statement,
            "type_hash": self.type_hash,
            "proof_length": self.proof_length,
            "n_lines": self.n_lines,
            "tactic_counts": dict(self.tactic_counts),
            "heartbeats": self.heartbeats,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "CertMeta":
        return cls(
            name=d["name"],
            statement=d["statement"],
            type_hash=d["type_hash"],
            proof_length=d["proof_length"],
            n_lines=d["n_lines"],
            tactic_counts=dict(d.get("tactic_counts", {})),
            heartbeats=d.get("heartbeats"),
        )


def extract_cert_meta(theorem_text: str, *, heartbeats=None) -> CertMeta:
    """Parse ONE ``theorem <name> : <stmt> := by <proof>`` block into a :class:`CertMeta`.

    The statement is everything between the name and the first ``:=`` (leading binders
    and the ``:`` colon are stripped so ``statement`` is the bare type).  All fields
    except ``heartbeats`` are computed from the text; ``heartbeats`` is attached if
    measured (see :func:`measure_heartbeats`).
    """
    m = _THEOREM_RE.search(theorem_text)
    if not m:
        raise ValueError("no `theorem <name> ... := by <proof>` block found")
    name = m.group(1)
    raw_type = m.group(2).strip()
    proof_body = m.group(3)

    # Strip a single leading `:` (and any binders before it) so `statement` is the type.
    # Binders like `(h : P)` may contain colons; split on the FIRST top-level `:` that is
    # not inside parentheses/brackets/braces.
    statement = _strip_to_type(raw_type)

    n_lines = theorem_text.strip().count("\n") + 1
    return CertMeta(
        name=name,
        statement=statement,
        type_hash=_type_hash(statement),
        proof_length=len(proof_body),
        n_lines=n_lines,
        tactic_counts=_tactic_counts(proof_body),
        heartbeats=heartbeats,
    )


def _strip_to_type(raw_type: str) -> str:
    """Given the text between the theorem name and ``:=``, return the bare type.

    Skips leading binders `(...)`, `{...}`, `[...]` and returns whatever follows the
    first top-level `:`.  If there is no top-level `:` (unusual), returns the input
    stripped.
    """
    depth = 0
    for i, ch in enumerate(raw_type):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            return raw_type[i + 1:].strip()
    return raw_type.strip()


# --------------------------------------------------------------------------------------
# Heartbeat measurement (optional, needs a built env)
# --------------------------------------------------------------------------------------

_HEARTBEATS_RE = re.compile(r"[Uu]sed\s+([0-9]+)\s+heartbeats")


def measure_heartbeats(
    theorem_text: str,
    *,
    env_dir,
    name: str,
    prelude: str = "",
    lean_path_bin=None,
    timeout: int = 600,
) -> object:
    """Measure elaboration heartbeats for ``theorem_text`` against a built env.

    Wraps the theorem with Mathlib's ``#count_heartbeats in`` (from
    ``Mathlib.Util.CountHeartbeats``), elaborates it with ``lake env lean`` inside
    ``env_dir`` (same subprocess pattern as :func:`telperion.verify.verify_lean`), and
    parses the ``"Used N heartbeats"`` info message.

    Returns the integer heartbeat count, or ``None`` if it can't be parsed (missing
    env, elaboration error, or no such info message) — never raises for that case.
    """
    env_dir = Path(env_dir)
    if not env_dir.exists():
        return None

    # `#count_heartbeats in` (Mathlib.Util.CountHeartbeats) emits the info message
    # "Used N heartbeats".  It needs Mathlib imported; imports must be the FIRST lines
    # of the file, so we synthesize an `import Mathlib` when the caller's prelude /
    # theorem don't already carry one.
    header = prelude.rstrip()
    combined = header + "\n" + theorem_text
    if not re.search(r"^\s*import\b", combined, re.MULTILINE):
        header = ("import Mathlib\n" + header).rstrip()
    if header:
        header += "\n"
    body = header + "#count_heartbeats in\n" + theorem_text.rstrip() + "\n"

    fd, tmp = tempfile.mkstemp(suffix=".lean", dir=str(env_dir))
    os.close(fd)
    Path(tmp).write_text(body, encoding="utf-8")
    try:
        env = os.environ.copy()
        elan = lean_path_bin or str(Path.home() / ".elan" / "bin")
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
        proc = subprocess.run(
            ["lake", "env", "lean", tmp],
            cwd=str(env_dir), capture_output=True, text=True, env=env, timeout=timeout,
        )
        out = (proc.stdout or "") + (proc.stderr or "")
    except Exception:
        return None
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass

    m = _HEARTBEATS_RE.search(out)
    if not m:
        return None
    return int(m.group(1))


# --------------------------------------------------------------------------------------
# Content-addressed cert index
# --------------------------------------------------------------------------------------


class CertIndex:
    """A content-addressed index of :class:`CertMeta` records.

    Keyed by ``type_hash``: :meth:`duplicates` surfaces the shared atoms (one statement
    proved under >1 name), which a future ``merge`` can dedup.
    """

    def __init__(self):
        self.metas: dict = {}                # name -> CertMeta
        self.by_type_hash: dict = {}         # type_hash -> [names]

    def add(self, meta: CertMeta) -> None:
        self.metas[meta.name] = meta
        names = self.by_type_hash.setdefault(meta.type_hash, [])
        if meta.name not in names:
            names.append(meta.name)

    def duplicates(self) -> dict:
        """Return ``{type_hash: [names]}`` for every type_hash with >1 distinct name."""
        return {h: list(ns) for h, ns in self.by_type_hash.items() if len(ns) > 1}

    def to_json(self) -> str:
        return json.dumps(
            {"metas": [m.to_dict() for m in self.metas.values()]},
            indent=2,
            sort_keys=True,
        )

    @classmethod
    def from_json(cls, s: str) -> "CertIndex":
        data = json.loads(s)
        idx = cls()
        for d in data.get("metas", []):
            idx.add(CertMeta.from_dict(d))
        return idx
