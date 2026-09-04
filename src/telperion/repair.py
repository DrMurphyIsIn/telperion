"""Mechanical proof-repair passes for Mathlib-version drift (AXLE `repair_proofs`).

Emitted Lean is hand-tuned to compile against the pinned Mathlib, but breaks on
version churn - this session hit `div_le_iff` -> `div_le_iff0` and the like. AXLE's
`repair_proofs` exposes named mechanical passes (`replace_unsafe_tactics`,
`relax_defeq_transparency`, ...); this is the Telperion analog: a small, SAFE set of
lemma-rename substitutions plus a verify -> repair -> re-verify loop, so a proof that
fails only on a known rename is auto-fixed and re-checked against the kernel rather
than needing a source edit.

The rename table is DATA-driven: it is loaded from the committed
``deprecations.json`` (produced offline by :mod:`telperion.deprecations`, which
harvests Mathlib's ``@[deprecated (since := ...)] alias OLD := NEW`` attributes).
When that file is absent, a small built-in SEED is used instead - the seed still
contains the five ``div_iff`` renames this session relied on, so repair keeps
working on a bare checkout.

The passes are conservative (word-boundary, idempotent, no semantic change) and are
applied only as a *fallback* after a verification failure - never speculatively.
On a verify failure that is NOT a known rename, :func:`collect_rename_candidates`
mines the error text for ``unknown identifier 'X'`` and surfaces ``X`` as a rename
CANDIDATE for a human / the offline extractor - it is never auto-applied.

conjecture1_proved = False.
"""
from __future__ import annotations

import json
import logging
import re
from pathlib import Path
from typing import Dict, List, Tuple

_LOG = logging.getLogger(__name__)

_DEPRECATIONS_JSON = Path(__file__).with_name("deprecations.json")

# Built-in SEED: the renames this session relied on, used when deprecations.json
# is absent so a bare checkout still repairs the known div_iff drift.
_SEED_RENAMES: Dict[str, str] = {
    "div_le_iff": "div_le_iff0".replace("0", "₀"),
    "le_div_iff": "le_div_iff0".replace("0", "₀"),
    "div_lt_iff": "div_lt_iff0".replace("0", "₀"),
    "lt_div_iff": "lt_div_iff0".replace("0", "₀"),
    "div_le_one": "div_le_one0".replace("0", "₀"),
}

# `unknown identifier 'X'` - the EXACT Lean v4.32.0 shape (confirmed from
# tests/test_batch_adgh.py: "error: R3Cert/Y.lean:10:1: unknown identifier 'foo'").
# It is `unknown identifier`, NOT `unknown constant`.
_UNKNOWN_IDENT = re.compile(r"unknown identifier ['‘]([^'’]+)['’]")


def _load_rename_table() -> Dict[str, str]:
    """Load ``old -> new`` renames from deprecations.json, else the built-in seed."""
    try:
        raw = json.loads(_DEPRECATIONS_JSON.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return dict(_SEED_RENAMES)
    renames = raw.get("renames") if isinstance(raw, dict) else None
    if not isinstance(renames, dict) or not renames:
        return dict(_SEED_RENAMES)
    # Merge seed underneath the JSON so the div_iff renames are always present
    # even if a future extraction happens to drop them.
    merged = dict(_SEED_RENAMES)
    merged.update({str(k): str(v) for k, v in renames.items()})
    return merged


def _compile_passes(renames: Dict[str, str]) -> List[Tuple[str, str, str]]:
    """Build ``(compiled_pattern, from_name, to_name)`` records.

    Each pattern is word-boundary anchored and REFUSES to fire when the token is
    already followed by the subscript-zero / prime that the renamed form carries,
    which keeps the substitution IDEMPOTENT (re-running never double-applies).
    Only renames whose new name genuinely differs from the old are kept.
    """
    passes: List[Tuple[str, str, str]] = []
    for old, new in renames.items():
        if not old or not new or old == new:
            continue
        pat = re.compile(r"\b" + re.escape(old) + r"\b(?![₀'])")
        passes.append((pat, old, new))
    return passes


# Loaded once at import; a compiled list of (pattern, from, to).
_RENAMES = _load_rename_table()
_PASSES = _compile_passes(_RENAMES)

# Public view of the currently-loaded renames (old -> new).
RENAME_TABLE: Dict[str, str] = dict(_RENAMES)


def reload_rename_table() -> Dict[str, str]:
    """Re-read deprecations.json (or seed) and rebuild the compiled passes.

    Returns the freshly-loaded ``old -> new`` map.  Mainly for tests and for
    picking up a regenerated JSON without reimporting the module.
    """
    global _RENAMES, _PASSES, RENAME_TABLE
    _RENAMES = _load_rename_table()
    _PASSES = _compile_passes(_RENAMES)
    RENAME_TABLE = dict(_RENAMES)
    return dict(_RENAMES)


def repair_lean(content: str) -> Tuple[str, List[Tuple[str, str, int]]]:
    """Apply mechanical rename passes to ``content``.

    Returns ``(repaired, applied)`` where ``applied`` is a list of
    ``(from_name, to_name, count)`` records for the renames that fired.  Safe to
    run repeatedly: the idempotence guard means a second pass over already-repaired
    text produces no further substitutions.
    """
    applied: List[Tuple[str, str, int]] = []
    for pat, old, new in _PASSES:
        content, n = pat.subn(new, content)
        if n:
            applied.append((old, new, n))
    return content, applied


def collect_rename_candidates(verify_result_or_text) -> List[str]:
    """Mine an ``unknown identifier 'X'`` failure for rename CANDIDATES.

    Accepts either a :class:`telperion.verify.VerifyResult` (its ``errors`` list
    and ``raw`` transcript are both scanned) or a raw string.  Returns the
    de-duplicated identifiers Lean reported as unknown, in first-seen order.

    These are CANDIDATES only - they are logged and returned for a human or the
    offline extractor to promote into the rename table, NEVER auto-applied (the
    new name is unknown from the error alone).
    """
    texts: List[str] = []
    if isinstance(verify_result_or_text, str):
        texts.append(verify_result_or_text)
    else:
        errors = getattr(verify_result_or_text, "errors", None)
        if errors:
            texts.extend(str(e) for e in errors)
        raw = getattr(verify_result_or_text, "raw", None)
        if raw:
            texts.append(str(raw))
    seen: Dict[str, None] = {}
    for text in texts:
        for m in _UNKNOWN_IDENT.finditer(text):
            name = m.group(1)
            if name not in seen:
                seen[name] = None
    candidates = list(seen)
    if candidates:
        _LOG.info(
            "repair: %d unknown-identifier rename candidate(s) (not auto-applied): %s",
            len(candidates), candidates,
        )
    return candidates


def verify_with_repair(content, *, env_dir, decls=(), allow_axioms=()):
    """Verify; on failure apply repair passes and re-verify.

    Returns ``(result, final_content, applied)``.  Repair is a FALLBACK only - a
    first-pass clean verification is returned untouched.  If the failure is not a
    known rename (no pass fired), the original result is returned unchanged; the
    caller may then use :func:`collect_rename_candidates` on it.
    """
    from .verify import verify_lean

    r = verify_lean(content, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
    if r.okay and r.axioms_clean:
        return r, content, []
    repaired, applied = repair_lean(content)
    if not applied:
        return r, content, []
    r2 = verify_lean(repaired, env_dir=env_dir, decls=decls, allow_axioms=allow_axioms)
    return r2, repaired, applied
