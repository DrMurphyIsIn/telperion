"""GevreyFactorialMajorant emitter — the Gevrey-2 majorant calculus distilled
from the OpenAI Euler finite-time-blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``Euler/EulerProof.lean``,
Apache-2.0; lemma chain ``le_choose_of_interior`` … ``triangular_inverse_majorant``).

The Euler corpus runs on ONE arithmetic engine: the factorial-squared majorant

    majorant R d n := R^(n+d) · ((n+d)!)²

with five kernel-cheap laws — (1) shift: ``R·majorant R d n ≤ majorant R (d+1) n``;
(2) Leibniz product term: ``C(n,k)·majorant R d₁ k · majorant R d₂ (n−k) ≤
majorant R (d₁+d₂) n / C(n,k)``; (3) convolution with the exact constant 3
(via ``Σ_k 1/C(n,k) ≤ 3``); (4) geometric coefficient gain for radius
``Rc ≤ q·R``; (5) the triangular-recurrence closure: if
``Z n ≤ A·(F n + Σ_{k<n} C(n,k+1)·Rc^(k+1)·((k+1)!)²·Z(n−k−1))`` and the radius
budget ``2A(Rc+1) ≤ R`` holds, then ``Z n ≤ majorant R (d+1) n`` for all n.
The round-1 mining sweep found this shape independently in SIX file families —
it is the largest genuine gap in Telperion's kind set (nothing touches
``Nat.choose``/``Nat.factorial`` arithmetic).

Three modes per instance:

* ``calculus``           — emit the fixed self-contained calculus (prelude +
  capstones), no numeric data;
* ``budget``             — concrete rationals ``(A, Rc, R)``: certify EXACTLY
  ``1 ≤ A``, ``0 ≤ Rc``, ``2A(Rc+1) ≤ R`` and emit the specialized closure
  theorem with the side conditions discharged by ``norm_num``;
* ``polynomial_radius``  — concrete rational ``P ≥ 2`` and shift ``c : ℕ``:
  the single polynomial radius ``P^(2c+2)`` specialization.

A violated budget (``2A(Rc+1) > R``, ``A < 1``, ``Rc < 0``, ``P < 2``) is
REFUSED — the negative control.

HONESTY SEAM (zeta-23 discipline): the recurrence hypothesis ``hZ`` (that the
actual solution obeys the triangular bound) and the source bound ``hF`` are
ANALYTIC-side hypotheses.  The kernel certifies only the arithmetic closure:
"budget + recurrence-shape ⟹ Gevrey-2 growth".  ``conjecture1_proved = False``.
Nothing here proves blowup — it is the reusable factorial spine of one.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --------------------------------------------------------------------------- #
# The fixed self-contained calculus (ported verbatim, Apache-2.0 attribution)  #
# --------------------------------------------------------------------------- #

GEVREY_PRELUDE = r"""
-- Gevrey-2 factorial-majorant calculus, ported from OpenAI's Euler blowup
-- formalization (github.com/openai/NavierStokesAndEuler, Euler/EulerProof.lean,
-- Apache-2.0).  Self-contained over Nat.choose / Nat.factorial / ℝ.
open Finset

theorem le_choose_of_interior (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hk1 : k = 1
      · simp [hk1]
      by_cases hkn' : k = n
      · subst k
        simp
      have hklt : k < n := by omega
      have hkp : 0 < k - 1 := by omega
      have hp := ih (k - 1) hkp (by omega)
      have hq := ih k hk hklt
      rw [Nat.choose_succ_left n k hk]
      omega

theorem choose_le_shifted (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    n.choose k ≤ (n + d₁ + d₂).choose (k + d₁) := by
  calc
    n.choose k = n.choose (n - k) := (Nat.choose_symm hkn).symm
    _ ≤ (n + d₁).choose (n - k) := Nat.choose_le_add n d₁ (n - k)
    _ = (n + d₁).choose (k + d₁) := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ ≤ (n + d₁ + d₂).choose (k + d₁) :=
      Nat.choose_le_add (n + d₁) d₂ (k + d₁)

theorem sum_inv_choose_le_three (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) ≤ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hsum : ∑ k ∈ range n, (1 : ℝ) / ((n + 1).choose (k + 1) : ℝ)
          ≤ n * (1 / (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ _k ∈ range n, (1 / (n + 1) : ℝ) := by
            apply sum_le_sum
            intro k hk
            apply one_div_le_one_div_of_le hn
            exact_mod_cast le_choose_of_interior (n + 1) (k + 1)
              (by omega) (by have := mem_range.mp hk; omega)
          _ = _ := by simp
      have hquot : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn]
        linarith
      rw [sum_range_succ', sum_range_succ]
      norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]
      linarith

theorem choose_ratio_le_inv (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2
      ≤ 1 / (n.choose k : ℝ) := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hle : (n.choose k : ℝ) ≤ (n + d₁ + d₂).choose (k + d₁) := by
    exact_mod_cast choose_le_shifted n k d₁ d₂ hkn
  apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hc hle)) hc).2
  nlinarith

theorem shifted_factorial_kernel_le (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
        ((n - k + d₂).factorial : ℝ) ^ 2
      ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 / (n.choose k : ℝ) := by
  have hlarge : k + d₁ ≤ n + d₁ + d₂ := by omega
  have hsub : n + d₁ + d₂ - (k + d₁) = n - k + d₂ := by omega
  have hfac : ((n + d₁ + d₂).choose (k + d₁) : ℝ) *
      ((k + d₁).factorial : ℝ) * ((n - k + d₂).factorial : ℝ) =
      ((n + d₁ + d₂).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hlarge
    rw [hsub] at h
    exact_mod_cast h
  have hC : ((n + d₁ + d₂).choose (k + d₁) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlarge
  calc
    _ = ((n + d₁ + d₂).factorial : ℝ) ^ 2 *
        ((n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2) := by
      rw [← hfac]
      field_simp
    _ ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 * (1 / (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left (choose_ratio_le_inv n k d₁ d₂ hkn) (sq_nonneg _)
    _ = _ := by ring

/-- The Gevrey-2 factorial majorant. -/
noncomputable def majorant (R : ℝ) (d n : ℕ) : ℝ :=
  R ^ (n + d) * ((n + d).factorial : ℝ) ^ 2

theorem majorant_nonneg (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    0 ≤ majorant R d n := by
  unfold majorant
  positivity

theorem majorant_product_term (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
  have hexp : k + d₁ + (n - k + d₂) = n + d₁ + d₂ := by omega
  have hpow : R ^ (k + d₁) * R ^ (n - k + d₂) = R ^ (n + d₁ + d₂) := by
    rw [← pow_add, hexp]
  have h := mul_le_mul_of_nonneg_left (shifted_factorial_kernel_le n k d₁ d₂ hkn)
    (pow_nonneg hR (n + d₁ + d₂))
  unfold majorant
  simp only [← Nat.add_assoc]
  calc
    _ = (R ^ (k + d₁) * R ^ (n - k + d₂)) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by ring
    _ = R ^ (n + d₁ + d₂) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by rw [hpow]
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using h

/-- The Leibniz convolution constant is exactly `3`, uniformly in order/shifts. -/
theorem majorant_convolution (R : ℝ) (hR : 0 ≤ R) (n d₁ d₂ : ℕ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ 3 * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact majorant_product_term R hR n k d₁ d₂ (by have := mem_range.mp hk; omega)
    _ = majorant R (d₁ + d₂) n *
        ∑ k ∈ range (n + 1), (1 / (n.choose k : ℝ)) := by rw [mul_sum]
    _ ≤ majorant R (d₁ + d₂) n * 3 :=
      mul_le_mul_of_nonneg_left (sum_inv_choose_le_three n) (majorant_nonneg R hR _ _)
    _ = _ := by ring

theorem majorant_product_term_le (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n := by
  have hc : (1 : ℝ) ≤ n.choose k := by
    exact_mod_cast Nat.choose_pos hkn
  have hi : (1 : ℝ) / (n.choose k : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc
  exact (majorant_product_term R hR n k d₁ d₂ hkn).trans
    (mul_le_of_le_one_right (majorant_nonneg R hR _ _) hi)

/-- One spare factorial shift supplies a factor of at least `R`. -/
theorem majorant_shift_le (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    R * majorant R d n ≤ majorant R (d + 1) n := by
  have hf : (((n + d).factorial : ℕ) : ℝ) ≤ ((n + (d + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show n + d ≤ n + (d + 1) by omega)
  have hs : ((n + d).factorial : ℝ) ^ 2 ≤ ((n + (d + 1)).factorial : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n + d).factorial by positivity]
  unfold majorant
  calc
    _ = R ^ (n + (d + 1)) * ((n + d).factorial : ℝ) ^ 2 := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (pow_nonneg hR _)

/-- The geometric tail is bounded uniformly in the truncation length. -/
theorem geometric_tail_le_two_mul (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (n : ℕ) : ∑ k ∈ range n, q ^ (k + 1) ≤ 2 * q := by
  have hgeom : ∀ m : ℕ, ∑ k ∈ range m, q ^ k ≤ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_range_succ']
        simp_rw [pow_succ]
        rw [← sum_mul]
        simp only [pow_zero]
        have hm := mul_le_mul_of_nonneg_right ih hq
        linarith
  simpa only [pow_succ, ← sum_mul] using mul_le_mul_of_nonneg_right (hgeom n) hq

/-- A coefficient of radius `Rc ≤ q R` has the geometric gain `q^k`. -/
theorem majorant_coefficient_term (R Rc q : ℝ)
    (hR : 0 ≤ R) (hRc : 0 ≤ Rc) (hq : 0 ≤ q) (hscale : Rc ≤ q * R)
    (n k d : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * Rc ^ k * (k.factorial : ℝ) ^ 2 * majorant R d (n - k)
      ≤ q ^ k * majorant R d n := by
  have hp : Rc ^ k ≤ (q * R) ^ k := pow_le_pow_left₀ hRc hscale k
  have hterm := majorant_product_term_le R hR n k 0 d hkn
  simp only [zero_add] at hterm
  have hscaled := mul_le_mul_of_nonneg_left hterm (pow_nonneg hq k)
  calc
    _ ≤ (n.choose k : ℝ) * (q * R) ^ k * (k.factorial : ℝ) ^ 2 *
        majorant R d (n - k) := by
      gcongr
      exact majorant_nonneg R hR d (n - k)
    _ = q ^ k * ((n.choose k : ℝ) * majorant R 0 k * majorant R d (n - k)) := by
      simp only [majorant, Nat.add_zero, mul_pow]
      ring
    _ ≤ _ := hscaled

/-- The triangular inverse rule with an explicit sufficient radius budget.
Trust seam: `hF` and the recurrence shape `hZ` are analytic-side HYPOTHESES. -/
theorem triangular_inverse_majorant (A Rc R : ℝ)
    (hA : 1 ≤ A) (hRc : 0 ≤ Rc) (hlarge : 2 * A * (Rc + 1) ≤ R)
    (d : ℕ) (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant R d n)
    (hZ : ∀ n, Z n ≤ A * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant R (d + 1) n := by
  have hA0 : 0 ≤ A := by linarith
  have hARc : 0 ≤ A * Rc := mul_nonneg hA0 hRc
  have hR : 0 < R := by nlinarith
  have hq0 : 0 ≤ Rc / R := div_nonneg hRc hR.le
  have hqhalf : Rc / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR).2
    nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hRc]
  have hscale : Rc ≤ (Rc / R) * R := by rw [div_mul_cancel₀ _ hR.ne']
  have hbudget : A / R + 2 * A * (Rc / R) ≤ 1 := by
    calc
      _ = (A + 2 * A * Rc) / R := by ring
      _ ≤ 1 := (div_le_one hR).2 (by nlinarith)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      have hw : 0 ≤ majorant R (d + 1) n := majorant_nonneg R hR.le _ _
      have hshift : majorant R d n ≤ majorant R (d + 1) n / R := by
        apply (le_div_iff₀ hR).2
        simpa only [mul_comm] using majorant_shift_le R hR.le d n
      have hs : (∑ k ∈ range n,
          (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
            Z (n - (k + 1)))
          ≤ (2 * (Rc / R)) * majorant R (d + 1) n := by
        calc
          _ ≤ ∑ k ∈ range n, (Rc / R) ^ (k + 1) * majorant R (d + 1) n := by
            apply sum_le_sum
            intro k hk
            have hklt : k < n := mem_range.mp hk
            have hlow : n - (k + 1) < n := by omega
            have hc : 0 ≤ (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) *
                ((k + 1).factorial : ℝ) ^ 2 := by positivity
            exact (mul_le_mul_of_nonneg_left (ih _ hlow) hc).trans
              (majorant_coefficient_term R Rc (Rc / R) hR.le hRc hq0 hscale
                n (k + 1) (d + 1) (by omega))
          _ = (∑ k ∈ range n, (Rc / R) ^ (k + 1)) * majorant R (d + 1) n :=
            (sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (geometric_tail_le_two_mul (Rc / R) hq0 hqhalf n) hw
      calc
        Z n ≤ A * (F n + ∑ k ∈ range n,
            (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
              Z (n - (k + 1))) := hZ n
        _ ≤ A * (majorant R (d + 1) n / R +
            (2 * (Rc / R)) * majorant R (d + 1) n) :=
          mul_le_mul_of_nonneg_left (add_le_add ((hF n).trans hshift) hs) hA0
        _ = (A / R + 2 * A * (Rc / R)) * majorant R (d + 1) n := by ring
        _ ≤ majorant R (d + 1) n := mul_le_of_le_one_left hw hbudget

/-- For coefficient and inverse size `P^c`, the radius `P^(2c+2)` suffices. -/
theorem triangular_inverse_polynomial_radius (P : ℝ) (hP : 2 ≤ P) (c d : ℕ)
    (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant (P ^ (2 * c + 2)) d n)
    (hZ : ∀ n, Z n ≤ P ^ c * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * (P ^ c) ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant (P ^ (2 * c + 2)) (d + 1) n := by
  have hPc : 1 ≤ P ^ c := one_le_pow₀ (by linarith)
  have hPc0 : 0 ≤ P ^ c := by linarith
  have hP2 : 4 ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 2)]
  have heq : P ^ (2 * c + 2) = (P ^ c) ^ 2 * P ^ 2 := by
    rw [show 2 * c + 2 = c * 2 + 2 by omega, pow_add, pow_mul]
  have hlarge : 2 * P ^ c * (P ^ c + 1) ≤ P ^ (2 * c + 2) := by
    calc
      _ ≤ (P ^ c) ^ 2 * 4 := by nlinarith
      _ ≤ (P ^ c) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
      _ = _ := heq.symm
  exact triangular_inverse_majorant (P ^ c) (P ^ c) (P ^ (2 * c + 2))
    hPc hPc0 hlarge d F Z hF hZ
""".strip("\n")


# --------------------------------------------------------------------------- #
# Certification                                                               #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class GevreyMajorantCert:
    """One Gevrey-majorant instance.

    ``mode`` ∈ {"calculus", "budget", "polynomial_radius"}.  For ``budget``,
    ``(A, Rc, R)`` are exact rationals with ``1 ≤ A``, ``0 ≤ Rc``,
    ``2A(Rc+1) ≤ R`` re-verified; for ``polynomial_radius``, ``P ≥ 2`` rational
    and ``c : ℕ``."""

    mode: str
    A: sp.Rational | None = None
    Rc: sp.Rational | None = None
    R: sp.Rational | None = None
    P: sp.Rational | None = None
    c: int | None = None


def gevrey_majorant_certificate(mode, A=None, Rc=None, R=None, P=None, c=None
                                ) -> GevreyMajorantCert:
    """Build and EXACTLY re-check a Gevrey-majorant instance.  Refuses violated
    budgets (the negative controls)."""
    if mode == "calculus":
        return GevreyMajorantCert(mode="calculus")
    if mode == "budget":
        A = sp.Rational(sp.nsimplify(A))
        Rc = sp.Rational(sp.nsimplify(Rc))
        R = sp.Rational(sp.nsimplify(R))
        if not A >= 1:
            raise ValueError(f"gevrey_majorant REFUSED: need 1 ≤ A; got A={A}")
        if not Rc >= 0:
            raise ValueError(f"gevrey_majorant REFUSED: need 0 ≤ Rc; got Rc={Rc}")
        if not 2 * A * (Rc + 1) <= R:
            raise ValueError(
                f"gevrey_majorant REFUSED: radius budget 2·A·(Rc+1) ≤ R violated "
                f"(2·{A}·({Rc}+1) = {2*A*(Rc+1)} > {R})")
        return GevreyMajorantCert(mode="budget", A=A, Rc=Rc, R=R)
    if mode == "polynomial_radius":
        P = sp.Rational(sp.nsimplify(P))
        c = int(c)
        if not P >= 2:
            raise ValueError(f"gevrey_majorant REFUSED: need 2 ≤ P; got P={P}")
        if c < 0:
            raise ValueError(f"gevrey_majorant REFUSED: need c ≥ 0; got c={c}")
        return GevreyMajorantCert(mode="polynomial_radius", P=P, c=c)
    raise ValueError(
        f"gevrey_majorant REFUSED: mode ∈ {{calculus, budget, polynomial_radius}}; got {mode}")


def certify_gevrey_majorant_point(family, pt, name):
    """Certify one Gevrey-majorant instance: ``(CertifiedInstance, n_checks)``.

    ``spec(pt)`` returns ``("calculus",)``, ``("budget", A, Rc, R)``, or
    ``("polynomial_radius", P, c)``."""
    spec = family.special[1](pt)
    mode, *args = spec
    if mode == "budget":
        cert = gevrey_majorant_certificate("budget", A=args[0], Rc=args[1], R=args[2])
        n_checks = 3
    elif mode == "polynomial_radius":
        cert = gevrey_majorant_certificate("polynomial_radius", P=args[0], c=args[1])
        n_checks = 2
    else:
        cert = gevrey_majorant_certificate("calculus")
        n_checks = 1
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


# --------------------------------------------------------------------------- #
# Emitter                                                                     #
# --------------------------------------------------------------------------- #


@dataclass
class GevreyMajorantEmitter(Emitter):
    """Emit the Gevrey-2 factorial-majorant calculus (once per file) plus
    per-instance budget / polynomial-radius specializations, all side conditions
    discharged by ``norm_num``.  Self-contained over ℕ/ℝ (only ``import
    Mathlib``); the recurrence hypotheses are the analytic trust seam."""

    def __post_init__(self):
        self.kind = "gevrey_majorant"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [GEVREY_PRELUDE, ""]
        # the fixed calculus contributes its capstone theorems to the count
        n_thm = 2  # triangular_inverse_majorant + triangular_inverse_polynomial_radius
        for inst in fam.instances:
            cert: GevreyMajorantCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            if cert.mode == "calculus":
                continue  # the prelude IS the emission
            if cert.mode == "budget":
                a, rc, r = rat_lean(cert.A), rat_lean(cert.Rc), rat_lean(cert.R)
                lines.append(
                    f"-- {nm}: triangular-recurrence closure at the concrete budget\n"
                    f"-- A={cert.A}, Rc={cert.Rc}, R={cert.R} (2·A·(Rc+1) = "
                    f"{2*cert.A*(cert.Rc+1)} ≤ {cert.R} certified exactly).\n"
                    f"-- Trust seam: hF and the recurrence shape hZ are HYPOTHESES.\n"
                    f"theorem {nm} (d : ℕ) (F Z : ℕ → ℝ)\n"
                    f"    (hF : ∀ n, F n ≤ majorant ({r}) d n)\n"
                    f"    (hZ : ∀ n, Z n ≤ ({a}) * (F n + ∑ k ∈ Finset.range n,\n"
                    f"      (n.choose (k + 1) : ℝ) * ({rc}) ^ (k + 1) * "
                    f"((k + 1).factorial : ℝ) ^ 2 * Z (n - (k + 1)))) :\n"
                    f"    ∀ n, Z n ≤ majorant ({r}) (d + 1) n :=\n"
                    f"  triangular_inverse_majorant ({a}) ({rc}) ({r})\n"
                    f"    (by norm_num) (by norm_num) (by norm_num) d F Z hF hZ\n"
                )
                n_thm += 1
            else:  # polynomial_radius
                p = rat_lean(cert.P)
                lines.append(
                    f"-- {nm}: polynomial-radius specialization at P={cert.P}, c={cert.c}\n"
                    f"-- (radius P^(2c+2) = {cert.P**(2*cert.c+2)}; P ≥ 2 certified exactly).\n"
                    f"-- Trust seam: hF and the recurrence shape hZ are HYPOTHESES.\n"
                    f"theorem {nm} (d : ℕ) (F Z : ℕ → ℝ)\n"
                    f"    (hF : ∀ n, F n ≤ majorant (({p}) ^ (2 * {cert.c} + 2)) d n)\n"
                    f"    (hZ : ∀ n, Z n ≤ ({p}) ^ {cert.c} * (F n + ∑ k ∈ Finset.range n,\n"
                    f"      (n.choose (k + 1) : ℝ) * (({p}) ^ {cert.c}) ^ (k + 1) * "
                    f"((k + 1).factorial : ℝ) ^ 2 * Z (n - (k + 1)))) :\n"
                    f"    ∀ n, Z n ≤ majorant (({p}) ^ (2 * {cert.c} + 2)) (d + 1) n :=\n"
                    f"  triangular_inverse_polynomial_radius ({p}) (by norm_num) "
                    f"{cert.c} d F Z hF hZ\n"
                )
                n_thm += 1
        return "\n".join(lines), n_thm


def gevrey_majorant_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Gevrey-majorant family (kind ``gevrey_majorant``).

    ``spec: pt -> ("calculus",) | ("budget", A, Rc, R) | ("polynomial_radius", P, c)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("gevrey_majorant", spec),
        constants=dict(constants or {}),
    )
