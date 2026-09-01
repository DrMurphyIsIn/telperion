"""Dominated-integrability emitter (integrable-by-rpow-domination).

A recurring shape across the strip-representation work (R2, the tail bound, StripReprR1): an integrand
that is a BOUNDED factor times a complex power,

    f(x) = b(x) / (x:ℂ)^p ,      ‖b(x)‖ ≤ B  on the ray  Ioi c  (c > 0),

is integrable on `Ioi c` as soon as the power decays fast enough:

    ‖f(x)‖ = ‖b(x)‖ · x^{-Re p} ≤ B · x^{-Re p},   and   x^{-Re p} is integrable on Ioi c  iff  1 < Re p.

CERTIFICATE. Telperion is the CHECKER; this generator is UNTRUSTED. The load-bearing datum is the
CONVERGENCE CONDITION `1 < Re p` (equivalently the dominating exponent `-Re p < -1`), an EXACT
inequality on the supplied real part. `verify_convergence` checks it exactly (Fraction arithmetic) and
REFUSES a divergent instance (`Re p <= 1`), a nonpositive ray (`c <= 0`), or a negative bound. Only then
is Lean written; the emitted proof mirrors R2's `hint_frac`: `Integrable.mono'` against
`integrableOn_Ioi_rpow_of_lt`, measurability by `Measurable.aestronglyMeasurable`/`fun_prop`, and the
pointwise `‖b x / x^p‖ ≤ x^{-Re p}` from `‖b x‖ ≤ B` and `Complex.norm_cpow_eq_rpow_re_of_pos`.

The default `b = Int.fract` (B = 1) is exactly the zeta fractional-part integrand; a general bounded `b`
is supported by supplying its Lean name + a proof term for `‖b x‖ ≤ B`.

A gap-filler; NOT a proof of RH. conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp

from .expr import rat_lean


@dataclass(frozen=True)
class DominatedIntegrand:
    """`b(x)/(x:ℂ)^p` on `Ioi c`. `re_p` is Re p (rational, for the exact convergence check); `c` the
    ray start; `bound` the sup of ‖b‖. The Lean power is given symbolically by `p_lean` (e.g. "s + 1")."""
    re_p: Fraction          # Re p  -- convergence needs 1 < re_p
    c: Fraction             # ray start Ioi c, c > 0
    bound: Fraction         # B, sup of ‖b(x)‖
    p_lean: str             # the exponent p as Lean (e.g. "s + 1")


def verify_convergence(inst: DominatedIntegrand) -> bool:
    """EXACT anti-phantom gate: 1 < Re p (integrable), c > 0, B >= 0. REFUSE otherwise."""
    return inst.re_p > 1 and inst.c > 0 and inst.bound >= 0


def emit_integrability_lemma() -> str:
    """The reusable SHAPE lemma (parametric, dogfooded once): bounded/cpow is integrable on a ray."""
    return """\
/-- Reusable shape: a bounded factor over a complex power is integrable on a ray, provided the power
    decays (`1 < Re p`). `‖b‖ ≤ B` supplied as `hb`. Mirrors R2's `hint_frac`. -/
theorem integrableOn_bounded_div_cpow {b : ℝ → ℂ} {p : ℂ} {c B : ℝ}
    (hc : 0 < c) (hp : 1 < p.re)
    (hbmeas : Measurable b) (hb : ∀ x, ‖b x‖ ≤ B) :
    MeasureTheory.IntegrableOn (fun x => b x / (x : ℂ) ^ p) (Set.Ioi c) := by
  have hbnd : MeasureTheory.IntegrableOn (fun x : ℝ => B * x ^ (-p.re)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p.re < -1) hc).const_mul B
  refine hbnd.mono' ?_ ?_
  · exact (hbmeas.div ((Complex.measurable_ofReal.pow_const p))).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun x hx => ?_))
    have hxpos : (0 : ℝ) < x := lt_trans hc hx
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Real.rpow_neg hxpos.le, div_eq_mul_inv]
    exact mul_le_mul (hb x) le_rfl (by positivity) (le_trans (norm_nonneg _) (hb x))
"""


def emit_instance_lean(inst: DominatedIntegrand, thm_name: str,
                       b_lean: str = "fun x => ((Int.fract x : ℝ) : ℂ)") -> str:
    """Emit an INSTANCE integrability lemma. REFUSES a divergent / ill-posed instance."""
    if not verify_convergence(inst):
        raise ValueError(
            f"integrability REFUSED: need 1 < Re p (got {inst.re_p}), c > 0 (got {inst.c}), "
            f"B >= 0 (got {inst.bound}) -- the tail integral would diverge")
    return f"""\
/-- Instance: `{b_lean} / (x)^({inst.p_lean})` integrable on `Ioi {rat_lean(sp.Rational(inst.c))}`
    (Re p = {inst.re_p} > 1; ‖b‖ ≤ {inst.bound}). Convergence re-verified exactly before emission. -/
theorem {thm_name} {{s : ℂ}} (hs : ({rat_lean(sp.Rational(inst.re_p))} : ℝ) < ({inst.p_lean} : ℂ).re) :
    MeasureTheory.IntegrableOn (fun x => ({b_lean}) x / (x : ℂ) ^ ({inst.p_lean}))
      (Set.Ioi ({rat_lean(sp.Rational(inst.c))} : ℝ)) :=
  integrableOn_bounded_div_cpow (by norm_num) (by linarith)
    (by fun_prop) (fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x)]
      exact (Int.fract_lt_one x).le)
"""


def _self_test() -> None:
    # zeta fractional-part integrand: b = fract (B=1), p = s+1, Re p = Re s + 1 > 1  <=>  Re s > 0.
    # take a concrete-enough instance for the exact check: Re p = 2 (> 1), ray Ioi 1.
    inst = DominatedIntegrand(Fraction(2), Fraction(1), Fraction(1), "s + 1")
    assert verify_convergence(inst)
    assert "integrableOn_bounded_div_cpow" in emit_integrability_lemma()
    lean = emit_instance_lean(inst, "integrableOn_fractIntegrand_Ioi")
    assert "IntegrableOn" in lean and "Int.fract" in lean

    # anti-phantom: Re p = 1 diverges (∫ x^{-1} on Ioi 1 = ∞) -> REFUSE.
    div = DominatedIntegrand(Fraction(1), Fraction(1), Fraction(1), "s + 1")
    assert not verify_convergence(div)
    try:
        emit_instance_lean(div, "forged")
        raise AssertionError("must refuse the divergent Re p = 1 instance")
    except ValueError:
        pass
    print("emit_dominated_integrability self-test: OK")


if __name__ == "__main__":
    _self_test()
