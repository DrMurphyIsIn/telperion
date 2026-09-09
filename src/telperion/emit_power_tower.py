"""PowerTowerRecurrenceClosure emitter — polynomial self-composition recursions
closed to a doubly-exponential tower normal form, distilled from the OpenAI
Euler blowup formalization (``github.com/openai/NavierStokesAndEuler``,
``Euler/H6PressureConstants.lean``, Apache-2.0).

For a sequence obeying the cubic self-composition step

    C(q+1) ≤ L + 4·C(q)·(1 + 9^q·L·C(q)),

the closure is the power TOWER ``C(q) ≤ (9L)^(3^q)`` — a normal form neither
``gevrey_majorant`` (factorial) nor ``ratio_telescope`` (geometric/index)
produces.  Fixed generic atoms (the capstone GENERICIZED from the source's
``CoefficientJet`` structure to an abstract sequence):

  * ``succ_le_three_pow``          — ``q+1 ≤ 3^q`` (exponent budget);
  * ``inverse_majorant_dominates`` — ``9·(9^q·L) ≤ (9L)^(3^q)``;
  * ``inverse_majorant_step``      — ``L + 4·M(1+BM) ≤ M³`` off ``9B ≤ M``
    (the per-stage cubic domination);
  * ``power_tower_closure``        — the induction assembling the three into
    ``∀ q, C q ≤ (9L)^(3^q)``.

HONESTY SEAM: the recurrence step is a HYPOTHESIS on the abstract sequence.
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

POWER_TOWER_PRELUDE = r"""
-- Power-tower recurrence closure, ported (capstone genericized to an abstract
-- sequence) from OpenAI's Euler blowup formalization
-- (github.com/openai/NavierStokesAndEuler, H6PressureConstants.lean; Apache-2.0).

theorem succ_le_three_pow (q : ℕ) : q + 1 ≤ 3 ^ q := by
  induction q with
  | zero => norm_num
  | succ q ih => rw [pow_succ]; omega

/-- The inverse majorant dominates nine times the fixed-order multiplier majorant. -/
theorem inverse_majorant_dominates (q : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    9 * ((9 : ℝ) ^ q * L) ≤ (9 * L) ^ (3 ^ q) := by
  have hp : 1 ≤ L ^ q := one_le_pow₀ hL
  have hstep : L ≤ L ^ (q + 1) := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ L)
  calc
    _ = (9 : ℝ) ^ (q + 1) * L := by rw [pow_succ]; ring
    _ ≤ (9 : ℝ) ^ (q + 1) * L ^ (q + 1) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (9 * L) ^ (q + 1) := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (succ_le_three_pow q)

/-- One stage of the explicit polynomial inverse bound. -/
theorem inverse_majorant_step {L B M : ℝ} (hL : 1 ≤ L) (hB : L ≤ B) (hM : 9 * B ≤ M) :
    L + 4 * (M * (1 + B * M)) ≤ M ^ 3 := by
  have hM9 : 9 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hLleM : L ≤ M := by linarith
  have hM2 : 81 ≤ M ^ 2 := by nlinarith only [hM9]
  have hcube := mul_le_mul_of_nonneg_right hM2 hM0
  have hprod := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
  have hcubepos : 0 ≤ M ^ 3 := by positivity
  nlinarith only [hLleM, hcube, hprod, hcubepos]

/-- The cubic self-composition recursion closes to the power tower `(9L)^(3^q)`. -/
theorem power_tower_closure (C : ℕ → ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hpos : ∀ q, 0 ≤ C q) (hbase : C 0 ≤ 9 * L)
    (hstep : ∀ q, C (q + 1) ≤ L + 4 * (C q * (1 + ((9 : ℝ) ^ q * L) * C q))) :
    ∀ q, C q ≤ (9 * L) ^ (3 ^ q) := by
  intro q
  induction q with
  | zero => simpa using hbase
  | succ q ih =>
    have hB : L ≤ (9 : ℝ) ^ q * L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)) (by linarith : 0 ≤ L)
    have hB0 : 0 ≤ (9 : ℝ) ^ q * L := by positivity
    have hM : 9 * ((9 : ℝ) ^ q * L) ≤ (9 * L) ^ (3 ^ q) :=
      inverse_majorant_dominates q hL
    have hM0 : (0 : ℝ) ≤ (9 * L) ^ (3 ^ q) := by positivity
    have hsq : ((9 : ℝ) ^ q * L) * (C q * C q) ≤
        ((9 : ℝ) ^ q * L) * ((9 * L) ^ (3 ^ q) * (9 * L) ^ (3 ^ q)) :=
      mul_le_mul_of_nonneg_left (mul_self_le_mul_self (hpos q) ih) hB0
    have hmono : C q * (1 + ((9 : ℝ) ^ q * L) * C q) ≤
        (9 * L) ^ (3 ^ q) * (1 + ((9 : ℝ) ^ q * L) * (9 * L) ^ (3 ^ q)) := by
      nlinarith [hpos q, ih, hsq]
    have hfin := inverse_majorant_step hL hB hM
    have hpow : ((9 * L) ^ (3 ^ q)) ^ 3 = (9 * L) ^ (3 ^ (q + 1)) := by
      rw [show (3 : ℕ) ^ (q + 1) = 3 ^ q * 3 by rw [pow_succ], pow_mul]
    calc
      C (q + 1) ≤ L + 4 * (C q * (1 + ((9 : ℝ) ^ q * L) * C q)) := hstep q
      _ ≤ L + 4 * ((9 * L) ^ (3 ^ q) * (1 + ((9 : ℝ) ^ q * L) * (9 * L) ^ (3 ^ q))) := by
        linarith [hmono]
      _ ≤ ((9 * L) ^ (3 ^ q)) ^ 3 := hfin
      _ = _ := hpow
""".strip("\n")


@dataclass(frozen=True)
class PowerTowerCert:
    mode: str = "calculus"


def power_tower_certificate() -> PowerTowerCert:
    return PowerTowerCert()


def certify_power_tower_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=power_tower_certificate())
    return inst, 1


@dataclass
class PowerTowerEmitter(Emitter):
    """Emit the fixed power-tower closure atoms (once per file)."""

    def __post_init__(self):
        self.kind = "power_tower"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return POWER_TOWER_PRELUDE + "\n", 4


def power_tower_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``power_tower`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("power_tower", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
