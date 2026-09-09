"""RatioRecurrenceTelescope emitter — multiplicative telescoping of per-step
ratio bounds into closed normal forms, distilled from the OpenAI Euler blowup
formalization (``github.com/openai/NavierStokesAndEuler``, Apache-2.0;
``Euler/GevreyInversePartitions.lean`` ``predecessorPartitionSum_le``,
``Euler/ParentRenewalScaleCosts.lean`` ``reciprocal_geometric``,
``Euler/PacketStageGrowth.lean`` ``previousShear_ge_index``).

The existing ``telescope``/``TelescopingReciprocalSquare`` kinds are ADDITIVE;
this is the PRODUCT closure of ratio recursions, in three generic modes:

  * ``factorial``  — ``f(n+1) ≤ ((n:ℝ)+1)²·f(n)`` (n ≥ 1), ``f 1 ≤ x``
                     ⟹ ``f n ≤ x·(n!)²``  (the Gevrey partition normalizer);
  * ``geometric``  — ``0 < a n``, doubling floor ``2·a n ≤ a(n+1)``
                     ⟹ ``1/a n ≤ (1/a 0)·(1/2)ⁿ``  (summable-reciprocal envelope);
  * ``index``      — ``1 ≤ x n``, quadratic separation ``4·(x n)² ≤ x(n+1)``
                     ⟹ ``(n:ℝ)+1 ≤ x n``  (index domination, feeds Tendsto atTop).

All three are fixed fully-generic atoms over abstract sequences (induction +
per-step ``mul_le_mul`` / ``nlinarith [sq_nonneg …]``; kernel-cheap).

HONESTY SEAM: the per-step ratio bounds are HYPOTHESES on the abstract
sequence; the kernel certifies only the telescoping closure.
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

RATIO_TELESCOPE_PRELUDE = r"""
-- Ratio-recurrence telescoping atoms, ported (genericized from their concrete
-- sequences) from OpenAI's Euler blowup formalization
-- (github.com/openai/NavierStokesAndEuler; Apache-2.0).

/-- Factorial normalizer: per-step quadratic ratio closes to `x·(n!)²`. -/
theorem ratio_factorial_telescope (f : ℕ → ℝ) (x : ℝ) (hbase : f 1 ≤ x)
    (hstep : ∀ n, 1 ≤ n → f (n + 1) ≤ ((n : ℝ) + 1) ^ 2 * f n) :
    ∀ n : ℕ, 1 ≤ n → f n ≤ x * (n.factorial : ℝ) ^ 2 := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
    calc
      f (m + 2) ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ 2 * f (m + 1) := by
        simpa using hstep (m + 1) (by omega)
      _ ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ 2 * (x * ((m + 1).factorial : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (sq_nonneg _)
      _ = x * (((m + 2 : ℕ)).factorial : ℝ) ^ 2 := by
        rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ (m + 1), Nat.cast_mul]
        push_cast
        ring

/-- Doubling floor closes to a geometric reciprocal envelope. -/
theorem ratio_geometric_reciprocal (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n)
    (hdouble : ∀ n, 2 * a n ≤ a (n + 1)) :
    ∀ n : ℕ, 1 / a n ≤ (1 / a 0) * (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (0 : ℝ) < 2 * a n := by linarith [hpos n]
    have hrec := one_div_le_one_div_of_le h2 (hdouble n)
    calc
      1 / a (n + 1) ≤ 1 / (2 * a n) := hrec
      _ = (1 / 2) * (1 / a n) := by ring
      _ ≤ (1 / 2) * ((1 / a 0) * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / a 0) * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- Quadratic separation above 1 dominates the index. -/
theorem ratio_index_domination (x : ℕ → ℝ) (hone : ∀ n, 1 ≤ x n)
    (hsep : ∀ n, 4 * (x n) ^ 2 ≤ x (n + 1)) :
    ∀ n : ℕ, (n : ℝ) + 1 ≤ x n := by
  intro n
  induction n with
  | zero => simpa using hone 0
  | succ n ih =>
    have h := hsep n
    have hp := hone n
    push_cast
    nlinarith only [ih, h, hp, sq_nonneg (x n - 1)]
""".strip("\n")


@dataclass(frozen=True)
class RatioTelescopeCert:
    """The fixed three-atom calculus (no per-instance numeric data)."""

    mode: str = "calculus"


def ratio_telescope_certificate() -> RatioTelescopeCert:
    return RatioTelescopeCert()


def certify_ratio_telescope_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=ratio_telescope_certificate())
    return inst, 1


@dataclass
class RatioTelescopeEmitter(Emitter):
    """Emit the fixed factorial/geometric/index ratio-telescoping atoms."""

    def __post_init__(self):
        self.kind = "ratio_telescope"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return RATIO_TELESCOPE_PRELUDE + "\n", 3


def ratio_telescope_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``ratio_telescope`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("ratio_telescope", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
