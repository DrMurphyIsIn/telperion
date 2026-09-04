"""Mechanical proof-repair passes for Mathlib-version drift (AXLE `repair_proofs`).

Emitted Lean is hand-tuned to compile against the pinned Mathlib, but breaks on
version churn — this session hit `div_le_iff` → `div_le_iff₀` and the like. AXLE's
`repair_proofs` exposes named mechanical passes (`replace_unsafe_tactics`,
`relax_defeq_transparency`, …); this is the Telperion analog: a small, SAFE set of
lemma-rename substitutions plus a verify → repair → re-verify loop, so a proof that
fails only on a known rename is auto-fixed and re-checked against the kernel rather
than needing a source edit.

The passes are conservative (word-boundary, idempotent, no semantic change) and are
applied only as a *fallback* after a verification failure — never speculatively.
conjecture1_proved = False.
"""
from __future__ import annotations

import re

# (name, [(pattern, replacement)]) — Mathlib v4.3x renames seen in the wild.
# `(?![₀'])` guards against re-applying to an already-renamed `_iff₀` / a `'` variant.
_PASSES = {
    "div_iff_renames": [
        (re.compile(r"\bdiv_le_iff\b(?![₀'])"), "div_le_iff₀"),
        (re.compile(r"\ble_div_iff\b(?![₀'])"), "le_div_iff₀"),
        (re.compile(r"\bdiv_lt_iff\b(?![₀'])"), "div_lt_iff₀"),
        (re.compile(r"\blt_div_iff\b(?![₀'])"), "lt_div_iff₀"),
        (re.compile(r"\bdiv_le_one\b(?![₀'])"), "div_le_one₀"),
    ],
}

PASS_NAMES = tuple(_PASSES)


def repair_lean(content: str, *, passes=None):
    """Apply mechanical repair passes. Returns ``(repaired, applied)`` where
    ``applied`` is a list of ``(pass, from, to, count)`` records."""
    passes = list(passes) if passes is not None else list(_PASSES)
    applied = []
    for name in passes:
        for pat, rep in _PASSES.get(name, ()):
            new, n = pat.subn(rep, content)
            if n:
                applied.append((name, pat.pattern, rep, n))
                content = new
    return content, applied


def verify_with_repair(content, *, env_dir, decls=(), allow_axioms=(), passes=None):
    """Verify; on failure apply repair passes and re-verify. Returns
    ``(result, final_content, applied)``. Repair is a FALLBACK only — a first-pass
    success is returned untouched."""
    from .verify import verify_lean

    r = verify_lean(content, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
    if r.okay and r.axioms_clean:
        return r, content, []
    repaired, applied = repair_lean(content, passes=passes)
    if not applied:
        return r, content, []
    r2 = verify_lean(repaired, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
    return r2, repaired, applied
