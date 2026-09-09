"""DiscreteMoment emitter — discrete-sum moment atoms distilled from the
OpenAI Navier--Stokes/Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``, Apache-2.0;
``Euler/GevreyInversePartitions.lean`` ``sum_partSize_sq_le``,
``NavierStokes/AxisWeightEstimates.lean`` ``squareDecay`` calculus).

Fixed generic atoms (closing catalog shapes ``simplex_second_moment``,
``reciprocal_square_convolution`` AND the round-0
``TelescopingReciprocalSquare``):

  * ``simplex_second_moment`` — for a composition ``p : Fin k → ℕ`` with
    ``1 ≤ pᵢ`` and ``Σp = n``:  ``Σ pᵢ² ≤ (n−k+1)·n``  (genericized from
    ``OrderedFinpartition``; the Faà di Bruno / Gevrey partition kernel);
  * the ``squareDecay n := 1/(n+1)²`` calculus — telescoping majorant
    ``1/x² ≤ 2/x − 2/(x+1)``, tail sums ``Σ ≤ 2 − 2/(n+2) ≤ 2``, shift
    comparability ``d(n) ≤ 4·d(n+1)``, product bound, and the antidiagonal
    convolution ``Σ_{i+j=n} d(i)·d(j) ≤ 8·d(n)`` (the Cauchy/Leibniz
    square-summable-jet workhorse).

HONESTY SEAM: none needed — self-contained finitary facts.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

DISCRETE_MOMENT_PRELUDE = r"""
-- Discrete-sum moment atoms, ported (genericized) from OpenAI's blowup
-- formalization (github.com/openai/NavierStokesAndEuler; Apache-2.0).
open Finset Finset.Nat

/-- Second moment of a composition under a shared mass constraint. -/
theorem simplex_second_moment {k n : ℕ} (p : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ p i) (hsum : ∑ i, p i = n) :
    ∑ i, (p i : ℝ) ^ 2 ≤ ((n : ℝ) - k + 1) * n := by
  have hlen : ∀ i, p i + k ≤ n + 1 := by
    intro i
    have hs : (∑ j, (p j - 1)) + k = n := by
      have h : ∑ j, (p j - 1 + 1) = n := by
        simpa only [Nat.sub_add_cancel (hpos _)] using hsum
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] using h
    have hi : p i - 1 ≤ ∑ j, (p j - 1) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (p j - 1)) (Finset.mem_univ i)
    have hp := hpos i
    omega
  have hsum_real : ∑ i, (p i : ℝ) = n := by exact_mod_cast hsum
  calc
    _ ≤ ∑ i, ((n : ℝ) - k + 1) * (p i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h : (p i : ℝ) + k ≤ (n : ℝ) + 1 := by exact_mod_cast hlen i
      have hmul := mul_le_mul_of_nonneg_right
        (show (p i : ℝ) ≤ (n : ℝ) - k + 1 by linarith)
        (show 0 ≤ (p i : ℝ) by positivity)
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, hsum_real]

/-- The square-decay weight `1/(n+1)²`. -/
noncomputable def squareDecay (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2

theorem squareDecay_pos (n : ℕ) : 0 < squareDecay n := by
  unfold squareDecay
  positivity

theorem squareDecay_succ_le (n : ℕ) : squareDecay (n + 1) ≤ squareDecay n := by
  unfold squareDecay
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [show (0 : ℝ) ≤ n by positivity]

theorem squareDecay_le_four_succ (n : ℕ) : squareDecay n ≤ 4 * squareDecay (n + 1) := by
  unfold squareDecay
  have hn : (0 : ℝ) ≤ n := by positivity
  have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [show 4 * (1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) =
    4 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos h₁) (sq_pos_of_pos h₂)]
  push_cast
  nlinarith

/-- Elementary telescoping majorant for the square summability estimate. -/
theorem reciprocal_square_telescope (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hid : 2 / x - 2 / (x + 1) = 2 / (x * (x + 1)) := by
    field_simp; ring
  rw [hid, div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)]
  nlinarith

theorem sum_squareDecay_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 - 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [squareDecay]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have htel := reciprocal_square_telescope ((n : ℝ) + 2) (by linarith)
      have hid : squareDecay (n + 1) = 1 / ((n : ℝ) + 2) ^ 2 := by
        simp [squareDecay, Nat.cast_add, Nat.cast_one]
        ring
      rw [hid]
      push_cast
      ring_nf at ih htel ⊢
      linarith

theorem sum_squareDecay_le_two (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 := by
  have h := sum_squareDecay_le n
  have hp : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
  linarith

theorem squareDecay_product_le (i j : ℕ) :
    squareDecay i * squareDecay j ≤
      2 * squareDecay (i + j) * (squareDecay i + squareDecay j) := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hij : 0 < ((i + j : ℕ) : ℝ) + 1 := by positivity
  have hpoly : (((i + j : ℕ) : ℝ) + 1) ^ 2 ≤
      2 * (((i : ℝ) + 1) ^ 2 + ((j : ℝ) + 1) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg ((i : ℝ) - (j : ℝ))]
  have hh := div_le_div_of_nonneg_right hpoly (le_of_lt
    (mul_pos (mul_pos (sq_pos_of_pos hi) (sq_pos_of_pos hj)) (sq_pos_of_pos hij)))
  convert! hh using 1 <;> unfold squareDecay <;>
    field_simp [ne_of_gt hi, ne_of_gt hj, ne_of_gt hij]
  ring

/-- The one-dimensional convolution constant is at most eight. -/
theorem squareDecay_convolution_le (n : ℕ) :
    (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤ 8 * squareDecay n := by
  have hsum : (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤
      ∑ ij ∈ antidiagonal n, 2 * squareDecay n * (squareDecay ij.1 + squareDecay ij.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    have h := squareDecay_product_le ij.1 ij.2
    rw [mem_antidiagonal.mp hij] at h
    exact h
  have hfirst : (∑ ij ∈ antidiagonal n, squareDecay ij.1) ≤ 2 := by
    rw [sum_antidiagonal_eq_sum_range_succ_mk]
    exact sum_squareDecay_le_two n
  have hsecond : (∑ ij ∈ antidiagonal n, squareDecay ij.2) ≤ 2 := by
    have heq : (∑ ij ∈ antidiagonal n, squareDecay ij.2) =
        ∑ ij ∈ antidiagonal n, squareDecay ij.1 := by
      simpa only [Prod.fst_swap] using
        (sum_antidiagonal_swap (n := n) (f := fun ij => squareDecay ij.1))
    rw [heq]
    exact hfirst
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hd := (squareDecay_pos n).le
  nlinarith
""".strip("\n")


@dataclass(frozen=True)
class DiscreteMomentCert:
    mode: str = "calculus"


def discrete_moment_certificate() -> DiscreteMomentCert:
    return DiscreteMomentCert()


def certify_discrete_moment_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=discrete_moment_certificate())
    return inst, 1


@dataclass
class DiscreteMomentEmitter(Emitter):
    """Emit the fixed discrete-moment atoms (once per file)."""

    def __post_init__(self):
        self.kind = "discrete_moment"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return DISCRETE_MOMENT_PRELUDE + "\n", 8


def discrete_moment_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``discrete_moment`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("discrete_moment", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
