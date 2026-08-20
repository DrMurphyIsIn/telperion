"""Lean-side support: the user's project profile and a minimal template renderer.

The tool never owns the user's Lean project.  Everything project-specific —
namespace, imports, prelude definitions (e.g. domain functions like Fw/zw and
the box combinator lemma), unfold-lemma lists, per-kind tactic skeleton
overrides — lives in a LeanProfile the user supplies.

Templates are plain strings with «hole» markers.  The renderer checks holes
exhaustively: an unfilled hole is an error, an unknown filler is an error.
No third-party template engine — audit surface stays small (see METHODOLOGY).
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Mapping

_HOLE = re.compile(r"«([a-zA-Z0-9_]+)»")


class TemplateError(ValueError):
    pass


_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
_EMPTY_BINDER = re.compile(r"\(\s*:")


def _validate_fill(hole: str, value: str) -> None:
    """Typed hole contracts (REVIEW_20260816_TELPERION_G1: the empty binder
    `( : ℝ)` must be UNCONSTRUCTIBLE, not merely lintable).  Types are
    inferred from the hole name: *name* holes must be Lean identifiers;
    *binder* holes must be empty or well-formed (never `( :`); every fill must
    be hole-marker-free."""
    if "«" in value or "»" in value:
        raise TemplateError(f"hole {hole!r}: fill contains hole markers")
    if hole.endswith("name") or hole == "base":
        if not _IDENT.match(value):
            raise TemplateError(f"hole {hole!r}: {value!r} is not a Lean identifier")
    if "binder" in hole:
        if _EMPTY_BINDER.search(value):
            raise TemplateError(
                f"hole {hole!r}: EMPTY BINDER in {value!r} — the symbol list "
                "is empty; omit the binder entirely"
            )
        if value and value.count("(") != value.count(")"):
            raise TemplateError(f"hole {hole!r}: unbalanced binder {value!r}")


def render(template: str, fills: Mapping[str, str]) -> str:
    """Fill every «hole» (typed contracts applied per hole name); error on
    unfilled holes and on unused fillers."""
    holes = set(_HOLE.findall(template))
    missing = holes - set(fills)
    unused = set(fills) - holes
    if missing:
        raise TemplateError(f"unfilled holes: {sorted(missing)}")
    if unused:
        raise TemplateError(f"unknown fillers: {sorted(unused)}")
    for hole, value in fills.items():
        _validate_fill(hole, value)
    return _HOLE.sub(lambda m: fills[m.group(1)], template)


@dataclass(frozen=True)
class LeanProfile:
    """Everything about the user's Lean project the emitted file must respect."""

    namespace: tuple[str, ...] = ()
    imports: tuple[str, ...] = ("Mathlib",)
    prelude: str = ""                      # user defs emitted after the namespace
    unfold_lemmas: tuple[str, ...] = ()    # the `simp only [...]` list for identities
    options: tuple[str, ...] = ()          # e.g. ("set_option maxHeartbeats 1000000",)
    skeletons: Mapping[str, str] = field(default_factory=dict)  # per-kind overrides
    # Lint policy (not content — not part of the provenance hash, like the
    # sorry/axiom lint): by default `emit()` refuses a reflexive/trivial theorem
    # (`X = X`, `0 ≤ 0`) as VACUOUS.  A family that INTENTIONALLY emits reference
    # identities or degenerate boundary cases opts out here, declaring that intent.
    allow_reflexive: bool = False

    def skeleton(self, kind: str) -> str:
        return self.skeletons.get(kind, DEFAULT_SKELETONS[kind])

    def file_shell(self, header: str, body: str) -> str:
        parts = [header]
        parts.extend(f"import {i}" for i in self.imports)
        parts.append("")
        parts.extend(self.options)
        if self.options:
            parts.append("")
        for ns in self.namespace:
            parts.append(f"namespace {ns}")
        if self.namespace:
            parts.append("")
        if self.prelude.strip():
            parts.append(self.prelude.rstrip())
            parts.append("")
        parts.append(body.rstrip())
        parts.append("")
        for ns in reversed(self.namespace):
            parts.append(f"end {ns}")
        return "\n".join(parts) + "\n"


# --- default tactic skeletons (see docs/TACTIC_CONTRACT.md) -------------------
# Tactic contract: simp only, push_cast, field_simp, ring, positivity.
# `hyp_lines` are `have hdN : atom ≠ 0 := by positivity` lines (may be empty).
# `simp_clause` is `simp only [...]\n  ` or empty when there is nothing to unfold.

DEFAULT_SKELETONS: dict[str, str] = {
    # 0 ≤ body, via body = num/den then positivity
    "polya_nonneg": """theorem «name» «binders» :
    0 ≤ «body» := by
«hyp_lines»  have hkey : «body»
      = («num»)
        / («den») := by
    «simp_clause»field_simp
    try ring
  rw [hkey]
  positivity
""",
    # 0 ≤ body where body is already a polynomial (den = 1)
    "polya_nonneg_poly": """theorem «name» «binders» :
    0 ≤ «body» := by
  have hkey : «body» = «num» := by
    «simp_clause»ring
  rw [hkey]
  positivity
""",
    # afterE - beforeE = c1 + c2 q + c3 r + c4 (q r)
    "bilinear_identity": """theorem «name»_bilinear «binders» :
    «after» - «before»
      = «name»c1 «args» + «name»c2 «args» * «q» + «name»c3 «args» * «r»
        + «name»c4 «args» * («q» * «r») := by
«hyp_lines»  simp only [«unfold»]
  push_cast
  field_simp
  try ring
""",
    # the assembled box theorem via the user's corner combinator
    "box_assemble": """theorem «name»_cell «binders»
    (hQ0 : «hyp_q0») (hQ1 : «q» ≤ «q_hi»)
    (hS0 : «hyp_r0») (hS1 : «r» ≤ «r_hi») :
    «before» ≤ «after» := by
  rw [← sub_nonneg, «name»_bilinear «binder_names»]
  exact «combinator» hQ0 hQ1 hS0 hS1 («c00») («c01») («c10») («c11»)
""",
}
