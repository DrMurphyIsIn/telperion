"""LowOrderGeometricTail emitter — hybrid finite-low-grades + doubled geometric
tail certificate, distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``,
``Euler/PacketFiniteSumBounds.lean`` ``weighted_low_high_sum_le`` /
``Euler/PacketTailBound.lean`` ``sum_geometric_Ico_le``, Apache-2.0; reused
3+ times).

The hybrid shape neither ``telescope`` nor ``monotone_tail`` covers: finitely
many explicit low grades with individual constants PLUS a doubled geometric
tail under ratio ``≤ 1/2``:

    A 0 = 0,  A 1 ≤ C₁,  A 2 ≤ C₂,  A n ≤ B^{n+1} (3 ≤ n ≤ N+1),  κB ≤ 1/2
    ⟹  Σ_{n<N+2} κⁿ·A n  ≤  κC₁ + κ²C₂ + 2B(κB)³        uniformly in N,

with the supporting geometric atoms ``Σ_{range n} qᵏ ≤ 2`` and
``Σ_{Ico a b} qᵏ ≤ 2q^a`` (``q ≤ 1/2``).  Fixed generic atoms, verbatim port.

HONESTY SEAM: the per-grade bounds are HYPOTHESES on the abstract sequence.
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

LOW_ORDER_TAIL_PRELUDE = r"""
-- Low-order + geometric-tail hybrid certificate, ported from OpenAI's Euler
-- blowup formalization (github.com/openai/NavierStokesAndEuler,
-- PacketFiniteSumBounds/PacketTailBound; Apache-2.0).
open Finset

theorem sum_geometric_le_two (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (n : ℕ) :
    (∑ k ∈ range n, q ^ k) ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ']
      simp_rw [pow_succ]
      rw [← sum_mul]
      simp only [pow_zero]
      have hm := mul_le_mul_of_nonneg_right ih hq
      linarith

theorem sum_geometric_Ico_le (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (a b : ℕ) :
    (∑ i ∈ Ico a b, q ^ i) ≤ 2 * q ^ a := by
  rw [sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (sum_geometric_le_two q hq hqhalf (b - a))
    (pow_nonneg hq a)).trans_eq (mul_comm _ _)

/-- Finitely many explicit low grades plus a doubled geometric tail. -/
theorem weighted_low_high_sum_le (N : ℕ) (hN : 1 ≤ N) (κ B C₁ C₂ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hsmall : κ * B ≤ 1/2) (A : ℕ → ℝ)
    (hzero : A 0 = 0) (hone : A 1 ≤ C₁) (htwo : A 2 ≤ C₂)
    (htail : ∀ n, 3 ≤ n → n ≤ N + 1 → A n ≤ B ^ (n + 1)) :
    (∑ n ∈ range (N + 2), κ ^ n * A n) ≤ κ * C₁ + κ ^ 2 * C₂ + 2 * B * (κ * B) ^ 3 := by
  have hlow : (∑ n ∈ range 3, κ ^ n * A n) ≤ κ * C₁ + κ ^ 2 * C₂ := by
    simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, hzero,
      mul_zero, zero_add]
    exact add_le_add (mul_le_mul_of_nonneg_left hone hκ)
      (mul_le_mul_of_nonneg_left htwo (sq_nonneg κ))
  have hhigh : (∑ n ∈ Ico 3 (N + 2), κ ^ n * A n) ≤ 2 * B * (κ * B) ^ 3 := by
    calc
      _ ≤ ∑ n ∈ Ico 3 (N + 2), κ ^ n * B ^ (n + 1) := sum_le_sum (fun n hn =>
        mul_le_mul_of_nonneg_left
          (htail n (mem_Ico.mp hn).1 (by have := (mem_Ico.mp hn).2; omega))
          (pow_nonneg hκ _))
      _ = B * (∑ n ∈ Ico 3 (N + 2), (κ * B) ^ n) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        simp only [pow_succ, mul_pow]
        ring
      _ ≤ B * (2 * (κ * B) ^ 3) := mul_le_mul_of_nonneg_left
        (sum_geometric_Ico_le (κ * B) (mul_nonneg hκ hB) hsmall _ _) hB
      _ = _ := by ring
  rw [← sum_range_add_sum_Ico _ (show 3 ≤ N + 2 by omega)]
  exact add_le_add hlow hhigh
""".strip("\n")


@dataclass(frozen=True)
class LowOrderTailCert:
    mode: str = "calculus"


def low_order_tail_certificate() -> LowOrderTailCert:
    return LowOrderTailCert()


def certify_low_order_tail_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=low_order_tail_certificate())
    return inst, 1


@dataclass
class LowOrderTailEmitter(Emitter):
    """Emit the fixed low-order + geometric-tail atoms (once per file)."""

    def __post_init__(self):
        self.kind = "low_order_tail"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return LOW_ORDER_TAIL_PRELUDE + "\n", 3


def low_order_tail_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``low_order_tail`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("low_order_tail", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
