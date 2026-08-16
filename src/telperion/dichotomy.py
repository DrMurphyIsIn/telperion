"""Dichotomy glue: classification, not surgery.

The campaign's late-phase structural pattern: partition by an exact sign
condition and conquer each class by a DIFFERENT method — the interpolation
lemma's dichotomy on ``23z − 3 − 3Tz`` (heavy-top vs light-top), the (L)/(B)
layer's "everything outside the certified family falls to the rate bound".

`DichotomyGlueEmitter` emits the case-split theorem: ``rcases le_total lhs
rhs`` with each branch closed by a user-named branch theorem that RECEIVES
the branch hypothesis.  The branch theorems come from whatever tool fits each
side — a Polya family on the bounded branch, a symbolic tail or variable-map
family on the unbounded one; this emitter only contributes the exhaustive
glue (le_total IS the coverage proof) plus naming/provenance/lint.
"""
from __future__ import annotations

from dataclasses import dataclass

from .certify import CertifiedFamily
from .lean import LeanProfile, render
from .workflow import Emitter

DICHOTOMY_SKELETON = """theorem «name» «binders» :
    «claim» := by
  rcases le_total «lhs» «rhs» with h | h
  · exact «left_call»
  · exact «right_call»
"""


@dataclass
class DichotomyGlueEmitter(Emitter):
    """One glue theorem: the claim under `lhs ≤ rhs ∨ rhs ≤ lhs` (exhaustive
    by le_total), each branch delegated to its own theorem with `h` bound to
    the branch hypothesis."""

    theorem_name: str = "dichotomy"
    binders: str = ""
    claim: str = ""
    lhs: str = ""
    rhs: str = ""
    left_call: str = ""            # e.g. "below_thm u h hu"
    right_call: str = ""           # e.g. "above_thm u h hu"

    def __post_init__(self):
        self.kind = "dichotomy_glue"

    def emit_units(self, fam: CertifiedFamily, profile: LeanProfile):
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam: CertifiedFamily, profile: LeanProfile) -> tuple[str, int]:
        text = render(
            profile.skeletons.get("dichotomy_glue", DICHOTOMY_SKELETON),
            {
                "name": self.theorem_name,
                "binders": self.binders,
                "claim": self.claim,
                "lhs": self.lhs,
                "rhs": self.rhs,
                "left_call": self.left_call,
                "right_call": self.right_call,
            },
        )
        return text, 1
