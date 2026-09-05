"""Structured proof metadata + a content-addressed cert index (AXLE ``extract_decls``).

This is the metadata sibling of :mod:`telperion.verify`.  Where ``verify`` answers
"does this Lean elaborate cleanly?", ``cert_meta`` answers "what IS this proof, and
have we seen its statement before?".  Two capabilities:

1.  :func:`extract_cert_meta` parses ONE emitted ``theorem <name> : <stmt> := by <proof>``
    block into a :class:`CertMeta` record — normalized statement, a stable content
    hash (so cosmetically-different-but-equal statements collide), a stable PROOF-body
    hash (so cosmetic churn in the proof doesn't move it but a real tactic change does),
    proof length/lines, and per-tactic counts.  This lets Telperion regression-track proof
    COMPLEXITY over time (did a route get longer/heavier after an edit?).

2.  :class:`CertIndex` is a content-addressed index keyed by ``type_hash``.  Its
    :meth:`~CertIndex.duplicates` surfaces SHARED ATOMS — the same statement proved
    under different names across cells/families — which is the dedup target for a future
    ``merge`` (prove once, reuse everywhere).  Its :meth:`~CertIndex.proof_regressions`
    surfaces the complementary signal: the SAME statement (``type_hash``) now carrying a
    DIFFERENT proof body (``proof_hash``) — e.g. a route that got rewritten / heavier
    after a Mathlib bump.

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

# Lean block comment `/- ... -/` (non-greedy, DOTALL so it spans lines) and a line
# comment `-- ... <eol>`.  Block comments are stripped FIRST so a `--` inside a block
# comment is not mistaken for a line comment.
_BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT_RE = re.compile(r"--[^\n]*")


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


def type_hash(stmt: str) -> str:
    """Public content hash of a statement (16 hex).  Two statements that differ only
    cosmetically (whitespace, ``: ℝ``/``: Real`` ascriptions) hash equal — the
    structural key ``bundle`` uses to dedup shared atoms (AXLE ``merge`` by
    type_hash, not text)."""
    return _type_hash(stmt)


# A Lean identifier reference (dotted / primed allowed: `Real.log_le_sub_one_of_pos`,
# `foo'`, `R3Cert.BGSCL.log74`).  Used to recover which OTHER indexed certs a proof
# references — the AXLE ``extract_decls`` dependency set, offline: an identifier only
# counts as a DEP when it matches another cert's NAME in the index, so Mathlib lemmas
# and tactic keywords are filtered out naturally by the intersection.
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def _refs(text: str) -> frozenset:
    """The set of identifier tokens appearing in ``text`` (proof body + statement)."""
    return frozenset(_IDENT_RE.findall(text))


def _normalize_proof_body(proof_body: str) -> str:
    """Conservatively normalize a PROOF body for content hashing.

    Unlike :func:`_normalize_statement` (which deletes *all* whitespace — fine for a
    single expression, but catastrophic for a proof, where it would fuse adjacent
    tactic tokens such as ``rw`` and ``exact`` into ``rwexact`` and thereby erase the
    very structure we want to track), this keeps token boundaries intact.  It:

    1. strips Lean block comments ``/- ... -/`` (first, so an inner ``--`` is safe),
    2. strips Lean line comments ``-- ... <eol>``,
    3. collapses every run of whitespace to a SINGLE space, and
    4. trims leading/trailing whitespace.

    The result is: cosmetic churn (reindentation, added/removed comments, blank
    lines, a trailing newline) does NOT change the hash, but any real proof change
    (a different tactic, a changed lemma name, an extra step) DOES.
    """
    s = proof_body
    s = _BLOCK_COMMENT_RE.sub(" ", s)
    s = _LINE_COMMENT_RE.sub(" ", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def _proof_hash(proof_body: str) -> str:
    norm = _normalize_proof_body(proof_body)
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
    proof_hash: object = None  # str | None — stable content hash of the normalized proof body (16 hex)
    refs: frozenset = field(default_factory=frozenset)  # identifier tokens referenced (deps candidates)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "statement": self.statement,
            "type_hash": self.type_hash,
            "proof_length": self.proof_length,
            "n_lines": self.n_lines,
            "tactic_counts": dict(self.tactic_counts),
            "heartbeats": self.heartbeats,
            "proof_hash": self.proof_hash,
            "refs": sorted(self.refs),
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
            # `d.get` (not `d[...]`) so OLD records written before proof_hash existed
            # still load — they simply come back with proof_hash=None.
            proof_hash=d.get("proof_hash"),
            refs=frozenset(d.get("refs", ())),
        )


def extract_cert_meta(theorem_text: str, *, heartbeats=None) -> CertMeta:
    """Parse ONE ``theorem <name> : <stmt> := by <proof>`` block into a :class:`CertMeta`.

    The statement is everything between the name and the first ``:=`` (leading binders
    and the ``:`` colon are stripped so ``statement`` is the bare type).  All fields
    except ``heartbeats`` are computed from the text; ``heartbeats`` is attached if
    measured (see :func:`measure_heartbeats`).  ``proof_hash`` is a stable hash of the
    conservatively-normalized proof body (see :func:`_normalize_proof_body`).
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
    # Referenced identifiers (statement + proof), minus the theorem's own name — the
    # raw dependency candidates; the index narrows these to OTHER indexed certs.
    refs = _refs(statement + " " + proof_body) - {name}
    return CertMeta(
        name=name,
        statement=statement,
        type_hash=_type_hash(statement),
        proof_length=len(proof_body),
        n_lines=n_lines,
        tactic_counts=_tactic_counts(proof_body),
        heartbeats=heartbeats,
        proof_hash=_proof_hash(proof_body),
        refs=refs,
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
    proved under >1 name), which a future ``merge`` can dedup.  :meth:`proof_regressions`
    surfaces the complementary signal — the SAME statement now carrying a DIFFERENT proof
    body (e.g. a route rewritten / made heavier after a Mathlib bump).
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

    def proof_regressions(self) -> dict:
        """Flag same-statement / different-proof drift.

        For each ``type_hash`` whose records carry MORE THAN ONE distinct ``proof_hash``,
        return ``{type_hash: [(name, proof_hash), ...]}``.  This is the real regression
        signal: an identical statement (``type_hash`` collides) proved by two different
        proof bodies — the classic "same theorem, heavier/rewritten proof after a Mathlib
        bump" case, or two cells that ought to share one atom but currently don't.

        Records with ``proof_hash is None`` (old records lacking the field) are IGNORED
        for the distinct-count so an old+new pair for the same statement is not mistaken
        for drift on the strength of a missing hash alone; if a group has fewer than two
        distinct non-None proof hashes it is not reported.
        """
        out: dict = {}
        for h, names in self.by_type_hash.items():
            pairs = [(n, self.metas[n].proof_hash) for n in names]
            distinct = {ph for (_, ph) in pairs if ph is not None}
            if len(distinct) > 1:
                out[h] = [(n, ph) for (n, ph) in pairs]
        return out

    def dependencies(self, name: str) -> set:
        """The set of OTHER indexed cert names that ``name``'s block references — the
        AXLE ``extract_decls`` dependency set restricted to the cert graph (a ref only
        counts when it is another cert's name, so Mathlib lemmas/tactics are filtered).
        """
        if name not in self.metas:
            return set()
        return {r for r in self.metas[name].refs if r in self.metas and r != name}

    def dependents(self, name: str) -> set:
        """The set of indexed certs whose block references ``name`` (reverse edges)."""
        return {n for n in self.metas if name in self.dependencies(n)}

    def dead_atoms(self, roots=()) -> list:
        """Indexed certs that NO other indexed cert references and are not in ``roots``
        — atoms safe to drop (or that should be wired up).  ``roots`` are the
        top-level goals you keep regardless (e.g. the assembled theorem)."""
        roots = set(roots)
        return sorted(n for n in self.metas
                      if n not in roots and not self.dependents(n))

    def impacted_by(self, name: str) -> set:
        """Transitive dependents of ``name`` — every cert to RE-VERIFY when the shared
        atom ``name`` changes (impact analysis).  Excludes ``name`` itself."""
        out: set = set()
        frontier = {name}
        while frontier:
            cur = frontier.pop()
            for d in self.dependents(cur):
                if d not in out:
                    out.add(d)
                    frontier.add(d)
        out.discard(name)
        return out

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
