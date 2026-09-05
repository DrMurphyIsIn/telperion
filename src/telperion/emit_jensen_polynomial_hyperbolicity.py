"""JensenPolynomialHyperbolicityEmitter: d=2 box hyperbolicity, compile-gated.

conjecture1_proved = False. This emitter does NOT prove RH. It generates a Lean
theorem asserting that EVERY degree-2 Jensen polynomial whose rational
coefficient box `[(lo0,hi0),(lo1,hi1),(lo2,hi2)]` (c_k = C(2,k)*alpha(n+k)) is
real-rooted (hyperbolic): its real-root multiset has cardinality 2. The proof
chains a box-positivity discriminant bound into the Task-4 bridge lemma
`hyperbolic_deg2_of_discrim_nonneg` (in JensenBridge.lean).

The Jensen quadratic is `C c2 * X^2 + C c1 * X + C c0` with a=c2, b=c1, c=c0, so
the bridge discriminant `b^2 - 4*a*c` is `c1^2 - 4*c2*c0`.

Refusal gates (the negative-control discipline):
  - if disc2_margin(box) <= 0: not certifiably hyperbolic -> ValueError.
  - if the leading-coefficient box `box[2]` straddles zero (cannot prove
    c2 != 0, which the bridge requires): ValueError.

The emitted proof is a genuine nlinarith box-positivity argument, warm-verified
to build GREEN sorry-free (axioms {propext, Classical.choice, Quot.sound}).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from .expr import rat_lean
from .workflow import Emitter

# Lean skeleton for one box-hyperbolicity theorem. Placeholders are filled by
# render_box. The proof: derive c2 != 0 from the (all-positive or all-negative)
# leading-coefficient box, derive 0 <= c1^2 - 4*c2*c0 by nlinarith fed the four
# box-corner product nonnegativities plus the margin fact, then invoke the
# Task-4 bridge.
THEOREM_TEMPLATE = """theorem {name} :
    forall c0 c1 c2 : Real,
      {lo0} <= c0 -> c0 <= {hi0} ->
      {lo1} <= c1 -> c1 <= {hi1} ->
      {lo2} <= c2 -> c2 <= {hi2} ->
      (Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0).roots.card = 2 := by
  intro c0 c1 c2 h0lo h0hi h1lo h1hi h2lo h2hi
  have ha : c2 ≠ 0 := {ha_proof}
  have hdisc : (0:Real) ≤ c1^2 - 4*c2*c0 := by
    nlinarith [mul_nonneg (by linarith : (0:Real) ≤ c0 - {lo0}) (by linarith : (0:Real) ≤ c2 - {lo2}),
               mul_nonneg (by linarith : (0:Real) ≤ {hi0} - c0) (by linarith : (0:Real) ≤ {hi2} - c2),
               mul_nonneg (by linarith : (0:Real) ≤ c0 - {lo0}) (by linarith : (0:Real) ≤ {hi2} - c2),
               mul_nonneg (by linarith : (0:Real) ≤ {hi0} - c0) (by linarith : (0:Real) ≤ c2 - {lo2}),
               sq_nonneg (c1 - {lo1}), sq_nonneg ({hi1} - c1),
               (by norm_num : (0:Real) ≤ {margin})]
  have hcard := hyperbolic_deg2_of_discrim_nonneg c2 c1 c0 ha hdisc
  simpa using hcard
"""


@dataclass
class JensenPolynomialHyperbolicityEmitter(Emitter):
    """Emit a Lean box-hyperbolicity theorem for a degree-2 Jensen polynomial.

    Only degree=2 is supported (the d=2 base case of the hyperbolicity ladder).
    The public entry point is `render_box(n, box) -> (lean_text, n_theorems)`.
    """

    degree: int = 2
    requires_prelude: tuple[str, ...] = field(
        default=("hyperbolic_deg2_of_discrim_nonneg",), init=False
    )

    def __post_init__(self):
        self.kind = "jensen_polynomial_hyperbolicity"
        if self.degree != 2:
            raise ValueError(
                f"JensenPolynomialHyperbolicityEmitter only supports degree=2, "
                f"got degree={self.degree}"
            )

    def render_box(
        self, n: int, box: list[tuple[Fraction, Fraction]]
    ) -> tuple[str, int]:
        """Render the Lean box-hyperbolicity theorem for offset `n`.

        Raises ValueError if the box is not certifiably hyperbolic
        (disc2_margin(box) <= 0) or if the leading coefficient c2 straddles zero.
        Returns (lean_text, 1).
        """
        # Lazy import to avoid a hard module-load dependency cycle.
        from .rh_jensen.jensen import disc2_margin

        if len(box) != 3:
            raise ValueError(
                f"render_box requires a degree-2 box of length 3, got {len(box)}"
            )

        # --- Refusal gate 1: certified real-rootedness (positive discriminant). ---
        margin = disc2_margin(box)
        if margin <= 0:
            raise ValueError(
                f"non-hyperbolic box (disc2_margin = {margin} <= 0): the "
                f"discriminant lower bound c1^2 - 4*c0*c2 is not positive, so "
                f"real-rootedness is not certifiable. Refusing to emit."
            )

        (lo0, hi0), (lo1, hi1), (lo2, hi2) = box

        # --- Refusal gate 2: leading coefficient c2 must be provably nonzero. ---
        if lo2 > 0:
            # all-positive box: c2 >= lo2 > 0.
            ha_proof = (
                f"ne_of_gt (lt_of_lt_of_le (by norm_num : (0:Real) < {rat_lean(lo2)}) h2lo)"
            )
        elif hi2 < 0:
            # all-negative box: c2 <= hi2 < 0.
            ha_proof = (
                f"ne_of_lt (lt_of_le_of_lt h2hi (by norm_num : ({rat_lean(hi2)} : Real) < 0))"
            )
        else:
            raise ValueError(
                f"leading-coefficient box [{lo2}, {hi2}] straddles zero: cannot "
                f"prove c2 != 0 (the bridge lemma requires a nonzero leading "
                f"coefficient). Refusing to emit."
            )

        name = f"jensen_box_hyperbolic_deg2_{n}"
        text = THEOREM_TEMPLATE.format(
            name=name,
            lo0=rat_lean(lo0), hi0=rat_lean(hi0),
            lo1=rat_lean(lo1), hi1=rat_lean(hi1),
            lo2=rat_lean(lo2), hi2=rat_lean(hi2),
            ha_proof=ha_proof,
            margin=rat_lean(margin),
        )
        return text, 1
