"""Reference values read from the artefact they belong to, never from a literal (the cross-wiring rule).

conjecture1_proved = False.  Tooling.

THE BUG CLASS.  WALL-3 T's b_twist_real_g.py was a parametrised copy of b_twist_real.py.  The copy kept the
comparison literal B_float = 1.0376701213616086, which is track B's residue for gamma0 = 14.134725, so the
gamma0 = 21.02204 certificate compared its Arb residue against the wrong object's value (found by bb; fixed in
545b21697).  The fix: a comparison against a reference value reads that value from the referenced artefact, and the
certificate records which artefact (path, key, sha256).

  ref = read_reference(path, "A")                      # Reference(value, path, key, sha256)
  row = compare_ball(arb_value, ref)                   # {"contains": ..., "reference": ref.provenance()}
  hits = scan_stale_literals(script_source, refs)      # float literals in a script equal to a reference value

``scan_stale_literals`` is the regression net: a script that compares against a value it should have read flags
the literal and names the artefact the literal came from (in the bug above, the 14.13 file, not the 21.02 one).
"""
from __future__ import annotations

import hashlib
import io
import json
import math
import tokenize
from dataclasses import dataclass
from pathlib import Path

__all__ = ["Reference", "read_reference", "compare_ball", "scan_stale_literals", "references_in"]


@dataclass(frozen=True)
class Reference:
    value: object
    path: str
    key: str
    sha256: str

    def provenance(self) -> dict:
        return {"path": self.path, "key": self.key, "sha256": self.sha256}


def _dig(obj, key: str):
    cur = obj
    for part in key.split("."):
        if isinstance(cur, list):
            cur = cur[int(part)]
        else:
            if part not in cur:
                raise KeyError(f"reference key {key!r}: no {part!r}")
            cur = cur[part]
    return cur


def read_reference(path, key: str, display_root=None) -> Reference:
    """The value at dotted ``key`` in the JSON artefact ``path``.  ``display_root``: record the path relative to it
    (so certificates carry no absolute home paths)."""
    p = Path(path)
    raw = p.read_bytes()
    val = _dig(json.loads(raw), key)
    shown = str(p)
    if display_root is not None:
        try:
            shown = str(p.resolve().relative_to(Path(display_root).resolve()))
        except ValueError:
            pass
    return Reference(val, shown, key, hashlib.sha256(raw).hexdigest())


def compare_ball(ball, ref: Reference, slack: float = 0.0) -> dict:
    """Does the arb ``ball`` (widened by ``slack``) contain the reference value?  ARB comparison."""
    from flint import arb
    v = arb(repr(float(ref.value))) if not isinstance(ref.value, str) else arb(ref.value)
    contains = bool(abs(ball - v).upper() <= ball.rad() + slack)
    return {"contains": contains, "reference_value": ref.value, "reference": ref.provenance()}


def _sig_digits(lit: str) -> int:
    mant = lit.lower().split("e")[0].replace("_", "").lstrip("+-").replace(".", "").lstrip("0")
    return len(mant)


def scan_stale_literals(source: str, refs, min_digits: int = 8, rel: float = 1e-12) -> list[dict]:
    """Float literals (NUMBER tokens, and numeric STRING tokens) in ``source`` with at least ``min_digits``
    significant digits that equal some reference value to relative ``rel``.  Each hit is a comparison value that
    should be read with read_reference instead."""
    vals = []
    for r in refs:
        try:
            vals.append((float(r.value), r))
        except (TypeError, ValueError):
            continue
    hits = []
    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type == tokenize.NUMBER:
            lit = tok.string
        elif tok.type == tokenize.STRING:
            lit = tok.string.strip("rRbBuU").strip("'\"")
        else:
            continue
        try:
            x = float(lit)
        except ValueError:
            continue
        if _sig_digits(lit) < min_digits or not math.isfinite(x):
            continue
        for v, r in vals:
            if v != 0 and abs(x - v) <= rel * abs(v):
                hits.append({"line": tok.start[0], "literal": lit, "reference": r.provenance()})
    return hits


def references_in(paths, key: str, display_root=None) -> list[Reference]:
    """read_reference(p, key) for every artefact in ``paths`` that has ``key``."""
    out = []
    for p in paths:
        try:
            out.append(read_reference(p, key, display_root))
        except (KeyError, IndexError, TypeError):
            continue
    return out
