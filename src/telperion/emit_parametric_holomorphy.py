"""Parametric-holomorphy emitter — analyticity of a parametric tail integral.

The strip-representation work needs more than *existence* of the fractional-part
tail integral

    fractIntegral_c s = ∫ x in Ioi c, {x} · (x:ℂ)^{-(s+1)} dx        (c > 0)

it needs that integral to be COMPLEX-DIFFERENTIABLE in the parameter `s` on the
open right half-plane `{σ₀ < Re s}` (σ₀ > 0).  This is the (R2) discharge
`differentiableAt_fractIntegral` (examples/zero_free_bridge/lean/StripReprR2.lean),
proved by differentiation under the integral sign via
`hasDerivAt_integral_of_dominated_loc_of_lip` — the parameter-derivative
`F'(x) = {x}·(−log x)·x^{-(s+1)}`, dominated on the neighbourhood `{z.re/2 < Re w}`
by `log x · x^{-(z.re/2 + 1)}`, integrable on `(c,∞)`.

This emitter is the STRONGER companion to `emit_dominated_integrability`
(integrable-by-rpow-domination): that one certifies mere existence of the SAME
fract integrand (the decay-exponent gate `1 < Re p`); this one certifies
holomorphy in the parameter.  The heavy analysis is the two decay inequalities
that make the DOMINATING functions integrable on the ray:

    (int-gate)  −σ₀ − 1 < −1              [`h_int`: ‖F z‖ ≤ x^{-(z.re+1)}, integrable]
    (bint-gate) −(σ₀/2) − 1 < −1          [`h_bint`: log-corrected derivative bound]

Both reduce to σ₀ > 0.  (In the proof the cut point is `z.re/2`; with `σ₀ < z.re`
the companion gate is `−(z.re/2)−1 < −1`, again `z.re/2 > 0`.  The certificate
carries σ₀ as the CONSERVATIVE floor: any `z` with `σ₀ < z.re` inherits the gates.)

CERTIFICATE.  Telperion is the CHECKER; this generator is UNTRUSTED.  The
load-bearing datum is `(c > 0, σ₀ > 0)` together with the fract-integrand shape.
`parametric_holomorphy_certificate` EXACTLY (Fraction/sympy) checks the two decay
inequalities and the ray positivity, and RAISES `ValueError` (the anti-phantom
negative control) if `σ₀ ≤ 0` (the derivative-domination integral would diverge —
no holomorphy) or `c ≤ 0` (empty/ill-posed ray).

There is essentially ONE integrand instance in the corpus (the fract integrand),
so the "family" is thin by construction — that is expected; the emitter emits
that instance faithfully as a `(c, σ₀)`-parameterized copy of
`differentiableAt_fractIntegral`.

A gap-filler FEEDING input (R); NOT a proof of RH.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python -m telperion.emit_parametric_holomorphy`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _frac(x) -> Fraction:
    """Exact rational coercion (int / Fraction / sympy Rational / str)."""
    if isinstance(x, Fraction):
        return x
    r = sp.Rational(sp.nsimplify(x))
    return Fraction(int(r.p), int(r.q))


@dataclass(frozen=True)
class ParametricHolomorphyCertificate:
    """A verified parametric-holomorphy certificate for the fract tail integral.

    `c` is the ray start (`Ioi c`, `c > 0`); `sigma0` is the half-plane floor
    (`σ₀ < Re s`, `σ₀ > 0`).  The load-bearing facts are the two exact decay
    inequalities that make the dominating functions integrable on `(c,∞)`:

        int_gate  :  −σ₀ − 1      < −1     (existence of the integrand F z)
        bint_gate :  −(σ₀/2) − 1  < −1     (integrability of the derivative bound)

    Both are equivalent to σ₀ > 0; carried explicitly so the emitted Lean's two
    `linarith`/`integrableOn_Ioi_rpow_of_lt` gates are re-derivable byte-for-byte.
    `integrand` names the integrand shape (only the fract integrand ships).
    """

    c: Fraction               # ray start, > 0
    sigma0: Fraction          # half-plane floor σ₀, > 0
    int_gate: Fraction        # −σ₀ − 1  (must be < −1)
    bint_gate: Fraction       # −(σ₀/2) − 1  (must be < −1)
    integrand: str            # integrand identifier ("fract")


def parametric_holomorphy_certificate(
    c, sigma0, *, integrand: str = "fract"
) -> ParametricHolomorphyCertificate:
    """Build and EXACTLY self-check a parametric-holomorphy certificate.

    Refuses (`ValueError`) a ray with `c < 1` (the log-corrected derivative bound
    `log x · x^{...}` needs `log x ≥ 0`, i.e. `x ≥ 1`, which the ray `Ioi c` with
    `c ≥ 1` guarantees — this is exactly why the shipped `differentiableAt_fractIntegral`
    fixes the ray at `Ioi 1`) or a nonpositive half-plane floor (`σ₀ ≤ 0` — the
    derivative-domination integral diverges, so there is no holomorphy to certify),
    and re-verifies the two decay gates `−σ₀−1 < −1` and `−(σ₀/2)−1 < −1` exactly."""
    cf = _frac(c)
    s0 = _frac(sigma0)
    if cf < 1:
        raise ValueError(
            f"parametric-holomorphy REFUSED: need c ≥ 1 (got c = {cf}); the "
            f"log-corrected derivative bound log x · x^(-(σ₀/2)-1) needs log x ≥ 0 "
            f"(x ≥ 1) — the shipped proof fixes the ray at Ioi 1 for exactly this")
    if s0 <= 0:
        raise ValueError(
            f"parametric-holomorphy REFUSED: need σ₀ > 0 (got σ₀ = {s0}); the "
            f"derivative-domination integral log x · x^(-(σ₀/2)-1) DIVERGES on "
            f"Ioi c, so fractIntegral is NOT provably holomorphic there")
    if integrand != "fract":
        raise ValueError(
            f"parametric-holomorphy: only the fract integrand ships (got "
            f"{integrand!r}); supply a Lean derivation for a new integrand first")

    int_gate = -s0 - 1
    bint_gate = -(s0 / 2) - 1
    # EXACT anti-phantom re-check of the two decay inequalities.
    if not (int_gate < -1):
        raise ValueError(
            f"parametric-holomorphy REFUSED: int-gate −σ₀−1 = {int_gate} is NOT "
            f"< −1; the integrand fails to decay (σ₀ = {s0} ≤ 0)")
    if not (bint_gate < -1):
        raise ValueError(
            f"parametric-holomorphy REFUSED: bint-gate −(σ₀/2)−1 = {bint_gate} is "
            f"NOT < −1; the derivative bound fails to decay (σ₀ = {s0} ≤ 0)")

    return ParametricHolomorphyCertificate(
        c=cf, sigma0=s0, int_gate=int_gate, bint_gate=bint_gate, integrand=integrand
    )


def certify_parametric_holomorphy_point(family, pt, name):
    """Certify one parametric-holomorphy instance from ``family.special[1](pt)``.

    ``spec`` is either ``(c, sigma0)`` or
    ``{"c": ..., "sigma0": ..., "integrand": "fract"}``.  Returns
    ``(CertifiedInstance, n_checks)`` — n_checks = 3 (ray positivity + the two
    exact decay gates)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = parametric_holomorphy_certificate(
            spec["c"], spec["sigma0"], integrand=spec.get("integrand", "fract")
        )
    else:
        c, sigma0 = spec[0], spec[1]
        integrand = spec[2] if len(spec) > 2 else "fract"
        cert = parametric_holomorphy_certificate(c, sigma0, integrand=integrand)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 3


# The parameterized (c, σ₀) copy of `differentiableAt_fractIntegral`
# (examples/zero_free_bridge/lean/StripReprR2.lean).  The ONLY changes from the
# shipped proof are: the ray `Ioi 1` -> `Ioi c` (with `hc : 0 < c`, threaded into
# the `x > c => x > 0` steps and the `integrableOn_Ioi_rpow_of_lt _ hc` calls),
# the hypothesis `0 < z.re` -> `σ₀ < z.re` (with `hσ0 : 0 < σ₀` giving `0 < z.re`),
# and the local `fractIntegrand`/`fractIntegral` renamed with a `_c` suffix so the
# example is self-contained (import Mathlib, defs in the prelude).  Everything
# else — `hasDerivAt_integral_of_dominated_loc_of_lip`, the 7 sub-obligations,
# `convex_halfSpace_re_gt`, `HasDerivAt.const_cpow` — is copied verbatim; it
# compiles against Mathlib v4.32.0.
def _emit_instance(cert: ParametricHolomorphyCertificate, thm_name: str) -> str:
    if cert.integrand != "fract":
        raise ValueError("only the fract integrand is emittable")
    c_lean = rat_lean(sp.Rational(cert.c))
    s0_lean = rat_lean(sp.Rational(cert.sigma0))
    return f"""\
/-- (parametric R2) `fractIntegral_c` is differentiable at every `z` with
    `{s0_lean} < Re z` (ray `Ioi {c_lean}`, `c ≥ 1`).  A `(c, σ₀)`-parameterized copy of
    `differentiableAt_fractIntegral` (StripReprR2.lean).  Decay gates re-verified
    exactly before emission: −σ₀−1 = {rat_lean(sp.Rational(cert.int_gate))} < −1 and
    −(σ₀/2)−1 = {rat_lean(sp.Rational(cert.bint_gate))} < −1. -/
theorem {thm_name} {{z : ℂ}} (hz : ({s0_lean} : ℝ) < z.re) :
    DifferentiableAt ℂ fractIntegral_c z := by
  have hσ0 : (0 : ℝ) < ({s0_lean} : ℝ) := by norm_num
  have hzpos : (0 : ℝ) < z.re := lt_trans hσ0 hz
  have hc1 : (1 : ℝ) ≤ ({c_lean} : ℝ) := by norm_num
  have hσ : (0 : ℝ) < z.re / 2 := by linarith
  -- The parameter neighbourhood on which we dominate the derivative.
  set S : Set ℂ := {{w : ℂ | z.re / 2 < w.re}} with hSdef
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSmem : S ∈ 𝓝 z := hSopen.mem_nhds (by rw [hSdef]; simp only [Set.mem_setOf_eq]; linarith)
  -- Integrand `F`, its w-derivative `F'`, and the dominating function `bound`.
  set F : ℂ → ℝ → ℂ := fun w x => fractIntegrand_c w x with hFdef
  set F' : ℝ → ℂ := fun x => ((Int.fract x : ℝ) : ℂ) * (-Complex.log x) / (x : ℂ) ^ (z + 1) with hF'def
  set bound : ℝ → ℝ := fun x => Real.log x * x ^ (-(z.re / 2) - 1) with hbdef
  -- (meas) `F w` is a.e.-strongly-measurable for every `w`, uniformly near `z`.
  have h_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Set.Ioi ({c_lean} : ℝ))) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hFdef, fractIntegrand_c]
    fun_prop
  -- (int) `F z` is integrable on `(c,∞)`: `‖F z x‖ ≤ x^{{-(z.re+1)}}` and `-(z.re+1) < -1`.
  have h_int : Integrable (F z) (volume.restrict (Set.Ioi ({c_lean} : ℝ))) := by
    have hbase : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-(z + 1))‖) (Set.Ioi ({c_lean} : ℝ)) := by
      have : (-(z + 1)).re < -1 := by simp [Complex.add_re]; linarith
      exact integrableOn_Ioi_norm_cpow_of_lt this (by linarith)
    refine (Integrable.mono' hbase ?_ ?_)
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hFdef, fractIntegrand_c]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := lt_of_le_of_lt hc1 hx
      have hxpos : (0 : ℝ) < x := by linarith
      have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
      have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
      have hpow : ‖(x : ℂ) ^ (-(z + 1))‖ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := by
        rw [Complex.cpow_neg, norm_inv]
      have hcnn : (0 : ℝ) ≤ ‖(x : ℂ) ^ (z + 1)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      simp only [hFdef, fractIntegrand_c, norm_div, Complex.norm_real, Real.norm_of_nonneg hf0]
      rw [hpow, div_eq_mul_inv]
      calc Int.fract x * ‖(x : ℂ) ^ (z + 1)‖⁻¹
          ≤ 1 * ‖(x : ℂ) ^ (z + 1)‖⁻¹ := mul_le_mul_of_nonneg_right hf1 hcnn
        _ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := one_mul _
  -- (meas') `F'` is a.e.-strongly-measurable.
  have h_meas' : AEStronglyMeasurable F' (volume.restrict (Set.Ioi ({c_lean} : ℝ))) := by
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hF'def]; fun_prop
  -- (lip) Lipschitz-in-parameter, uniformly a.e.: from the derivative bound on the convex `S`.
  have h_lip : ∀ᵐ x ∂(volume.restrict (Set.Ioi ({c_lean} : ℝ))),
      LipschitzOnWith (Real.nnabs (bound x)) (fun w => F w x) S := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := lt_of_le_of_lt hc1 hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have hlogx : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hxpos.le).symm
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
    -- the w-derivative of `fun w => F w x` at any point w
    have hderiv : ∀ w : ℂ, HasDerivAt (fun v => F v x)
        (((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))) w := by
      intro w
      have hlin : HasDerivAt (fun v : ℂ => -(v + 1)) (-1 : ℂ) w :=
        ((hasDerivAt_id w).add_const (1 : ℂ)).neg
      have hcpow : HasDerivAt (fun v : ℂ => (x : ℂ) ^ (-(v + 1)))
          ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1)) w :=
        hlin.const_cpow (Or.inl hxne)
      have hmul := hcpow.const_mul ((Int.fract x : ℝ) : ℂ)
      have hfun : (fun v => F v x) = (fun v : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(v + 1))) := by
        funext v; simp only [hFdef, fractIntegrand_c, div_eq_mul_inv, ← Complex.cpow_neg]
      rw [hfun]; exact hmul
    -- the derivative norm is ≤ bound x on S
    have hbd : ∀ w ∈ S, ‖((Int.fract x : ℝ) : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))‖ ≤ bound x := by
      intro w hw
      rw [hSdef, Set.mem_setOf_eq] at hw
      have e1 : ‖((Int.fract x : ℝ) : ℂ)‖ = Int.fract x := by
        rw [Complex.norm_real, Real.norm_of_nonneg hf0]
      have e2 : ‖(x : ℂ) ^ (-(w + 1))‖ = x ^ (-(w.re + 1)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]; congr 1
      have e3 : ‖Complex.log (x : ℂ)‖ = Real.log x := by
        rw [hlogx, Complex.norm_real, Real.norm_of_nonneg hlog0]
      rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one, e1, e2, e3, hbdef]
      have hpow_le : x ^ (-(w.re + 1)) ≤ x ^ (-(z.re / 2) - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have hpow_pos : 0 < x ^ (-(w.re + 1)) := Real.rpow_pos_of_pos hxpos _
      have step1 : Int.fract x * (x ^ (-(w.re + 1)) * Real.log x)
          ≤ x ^ (-(w.re + 1)) * Real.log x :=
        mul_le_of_le_one_left (mul_nonneg hpow_pos.le hlog0) hf1
      have step2 : x ^ (-(w.re + 1)) * Real.log x ≤ Real.log x * x ^ (-(z.re / 2) - 1) := by
        rw [mul_comm (x ^ (-(w.re + 1)))]
        exact mul_le_mul_of_nonneg_left hpow_le hlog0
      exact le_trans step1 step2
    have hScvx : Convex ℝ S := by rw [hSdef]; exact convex_halfSpace_re_gt (z.re / 2)
    refine hScvx.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun w _ => (hderiv w).hasDerivWithinAt) (fun w hw => ?_)
    have hbnn : (0 : ℝ) ≤ bound x := by
      rw [hbdef]; exact mul_nonneg hlog0 (Real.rpow_pos_of_pos hxpos _).le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hbnn]
    exact hbd w hw
  -- (bint) the dominating function is integrable on `(c,∞)`.
  have h_bint : Integrable bound (volume.restrict (Set.Ioi ({c_lean} : ℝ))) := by
    have hzne : z.re ≠ 0 := hzpos.ne'
    have hq : (-(z.re / 4) - 1) < -1 := by linarith
    have hg : Integrable (fun x : ℝ => (4 / z.re) * x ^ (-(z.re / 4) - 1))
        (volume.restrict (Set.Ioi ({c_lean} : ℝ))) :=
      (integrableOn_Ioi_rpow_of_lt hq (by linarith)).const_mul _
    refine Integrable.mono' hg ?_ ?_
    · simp only [hbdef]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := lt_of_le_of_lt hc1 hx
      have hxpos : (0 : ℝ) < x := by linarith
      have hσ4 : (0 : ℝ) < z.re / 4 := by linarith
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      have hp1 : (0 : ℝ) < x ^ (-(z.re / 2) - 1) := Real.rpow_pos_of_pos hxpos _
      have hlogb : Real.log x ≤ x ^ (z.re / 4) / (z.re / 4) := by
        have h1 : Real.log (x ^ (z.re / 4)) ≤ x ^ (z.re / 4) - 1 :=
          Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos _)
        rw [Real.log_rpow hxpos] at h1
        rw [le_div_iff₀ hσ4]; nlinarith [h1]
      have hbnn : (0 : ℝ) ≤ bound x := by rw [hbdef]; exact mul_nonneg hlog0 hp1.le
      rw [Real.norm_of_nonneg hbnn, hbdef]
      calc Real.log x * x ^ (-(z.re / 2) - 1)
          ≤ (x ^ (z.re / 4) / (z.re / 4)) * x ^ (-(z.re / 2) - 1) := by gcongr
        _ = (4 / z.re) * x ^ (-(z.re / 4) - 1) := by
            rw [div_mul_eq_mul_div, ← Real.rpow_add hxpos,
              show z.re / 4 + (-(z.re / 2) - 1) = -(z.re / 4) - 1 by ring]
            field_simp
  -- (diff) the a.e. w-derivative of `F` at `z` is `F'`.
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi ({c_lean} : ℝ))),
      HasDerivAt (fun w => F w x) (F' x) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := lt_of_le_of_lt hc1 hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have hlin : HasDerivAt (fun w : ℂ => -(w + 1)) (-1 : ℂ) z :=
      ((hasDerivAt_id z).add_const (1 : ℂ)).neg
    have hcpow : HasDerivAt (fun w : ℂ => (x : ℂ) ^ (-(w + 1)))
        ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) z :=
      hlin.const_cpow (Or.inl hxne)
    have hmul := hcpow.const_mul ((Int.fract x : ℝ) : ℂ)
    have hfun : (fun w => F w x) = (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) := by
      funext w; simp only [hFdef, fractIntegrand_c, div_eq_mul_inv, ← Complex.cpow_neg]
    have hval : ((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) = F' x := by
      simp only [hF'def, div_eq_mul_inv, ← Complex.cpow_neg]; ring
    rw [hfun, ← hval]
    exact hmul
  -- Assemble.
  have key := hasDerivAt_integral_of_dominated_loc_of_lip hSmem h_meas h_int h_meas' h_lip h_bint h_diff
  have hd : DifferentiableAt ℂ (fun w => ∫ x in Set.Ioi ({c_lean} : ℝ), F w x) z := key.2.differentiableAt
  have hfe : (fun w => ∫ x in Set.Ioi ({c_lean} : ℝ), F w x) = fractIntegral_c := by
    funext w; simp only [hFdef, fractIntegral_c]
  rwa [hfe] at hd
"""


@dataclass
class ParametricHolomorphyEmitter(Emitter):
    """Emit `DifferentiableAt ℂ fractIntegral_c z` for `σ₀ < Re z` — a
    `(c, σ₀)`-parameterized copy of `differentiableAt_fractIntegral`
    (StripReprR2.lean), proved by differentiation under the integral sign
    (`hasDerivAt_integral_of_dominated_loc_of_lip`).  One theorem per instance;
    the fract-integrand defs live in the profile prelude."""

    def __post_init__(self):
        self.kind = "parametric_holomorphy"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: ParametricHolomorphyCertificate = inst.payload  # type: ignore[assignment]
            lines.append(_emit_instance(cert, inst.lean_name))
            nthm += 1
        return "\n".join(lines), nthm


def parametric_holomorphy_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a parametric-holomorphy family (kind='parametric_holomorphy').

    ``spec``: a callable ``pt -> (c, sigma0)`` or
    ``pt -> {"c": ..., "sigma0": ..., "integrand": "fract"}``.  Refuses (at
    certification) a nonpositive ray `c`, a nonpositive floor `σ₀`, or a decay
    gate that fails."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("parametric_holomorphy", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid cert, negative control, build instance + emit --------
    print("=== positive: fract integrand, ray Ioi 1, floor σ₀ = 1/2 ===")
    cert = parametric_holomorphy_certificate(1, sp.Rational(1, 2))
    print(f"  cert OK: c={cert.c}, σ₀={cert.sigma0}, "
          f"int_gate={cert.int_gate} (<-1), bint_gate={cert.bint_gate} (<-1)")

    print("\n=== positive: ray Ioi 2, floor σ₀ = 1 ===")
    cert2 = parametric_holomorphy_certificate(2, 1)
    print(f"  cert OK: c={cert2.c}, σ₀={cert2.sigma0}")

    print("\n=== NEGATIVE CONTROL: σ₀ = 0 (derivative integral diverges) ===")
    try:
        parametric_holomorphy_certificate(1, 0)
        raise SystemExit("FAIL: σ₀ = 0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: σ₀ = -1/2 (< 0) ===")
    try:
        parametric_holomorphy_certificate(1, sp.Rational(-1, 2))
        raise SystemExit("FAIL: σ₀ < 0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: c = 0 (empty ray) ===")
    try:
        parametric_holomorphy_certificate(0, 1)
        raise SystemExit("FAIL: c = 0 was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (fract instance, ray Ioi 1, σ₀ = 1/2) ===")
    inst = CertifiedInstance(point={"case": 0}, lean_name="differentiableAt_fractIntegral_c",
                             corners=(), payload=cert)

    class _View:
        instances = [inst]

    body, nthm = ParametricHolomorphyEmitter().emit_body(
        _View(), LeanProfile(namespace=("ParametricHolomorphy",))
    )
    print(f"\n-- {nthm} theorem(s) --\n")
    print(body)
