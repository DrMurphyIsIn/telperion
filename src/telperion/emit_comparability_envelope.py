"""ComparabilityEnvelope emitter — three comparability/Lipschitz atoms
distilled from the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``, Apache-2.0;
``NavierStokes/PhysicalGraphBounds.lean`` ``comparable_rpow``,
``NavierStokes/PulseCovariance.lean`` ``radiusProfile_lipschitz``,
``NavierStokes/MovingFrameODE.lean`` ``reciprocal_quadratic_difference``).

Fixed generic atoms (closing catalog shapes ``rpow_comparability_enclosure``,
``sqrt_comparability_envelope``, ``positive_quadratic_denominator_bound``):

  * ``comparable_rpow``      — ``q/2 ≤ Q ≤ 2q ⟹ Q^e ≤ 2^|e|·q^e`` for ANY real
    exponent (the |e|-driven case split unifying both signs);
  * ``sqrt_shift_lipschitz`` — ``|√(c+s²) − √(c+t²)| ≤ |s−t|`` for ``c > 0``
    (conjugate-multiply trick; genericized from ``radiusProfile = √(1+s²)``);
  * ``reciprocal_quadratic_difference`` — ``|1/(1+r²) − 1/(1+s²)| ≤
    |r−s|·(|r|+|s|)`` (the ``1+x² ≥ 1`` denominator-domination move), with its
    helper ``abs_div_le_of_one_le``.

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

COMPARABILITY_PRELUDE = r"""
-- Comparability/Lipschitz envelope atoms, ported (genericized) from OpenAI's
-- Navier-Stokes blowup formalization
-- (github.com/openai/NavierStokesAndEuler; Apache-2.0).

/-- Comparable bases give a uniform rpow comparability constant, both signs. -/
theorem comparable_rpow {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hlo : q / 2 ≤ Q) (hhi : Q ≤ 2 * q) (e : ℝ) :
    Q ^ e ≤ 2 ^ |e| * q ^ e := by
  by_cases he : 0 ≤ e
  · calc
      Q ^ e ≤ (2 * q) ^ e := Real.rpow_le_rpow hQ.le hhi he
      _ = 2 ^ |e| * q ^ e := by rw [Real.mul_rpow (by norm_num) hq.le, abs_of_nonneg he]
  · have he' : e ≤ 0 := le_of_not_ge he
    calc
      Q ^ e ≤ (q / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) hlo he'
      _ = q ^ e / (2 : ℝ) ^ e := Real.div_rpow hq.le (by norm_num) e
      _ = 2 ^ |e| * q ^ e := by
        rw [abs_of_nonpos he', Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- `√(c+s²)` is 1-Lipschitz in `s` (conjugate-multiply trick). -/
theorem sqrt_shift_lipschitz (c : ℝ) (hc : 0 < c) (s t : ℝ) :
    |Real.sqrt (c + s ^ 2) - Real.sqrt (c + t ^ 2)| ≤ |s - t| := by
  set fs := Real.sqrt (c + s ^ 2) with hfs
  set ft := Real.sqrt (c + t ^ 2) with hft
  have hfs0 : 0 < fs := Real.sqrt_pos.mpr (by positivity)
  have hft0 : 0 < ft := Real.sqrt_pos.mpr (by positivity)
  have hp : 0 < fs + ft := by linarith
  have hsq_s : fs ^ 2 = c + s ^ 2 := Real.sq_sqrt (by positivity)
  have hsq_t : ft ^ 2 = c + t ^ 2 := Real.sq_sqrt (by positivity)
  have he : (fs - ft) * (fs + ft) = (s - t) * (s + t) := by nlinarith [hsq_s, hsq_t]
  have ha := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_pos hp] at ha
  have habs_s : |s| ≤ fs := by
    have h := Real.sqrt_le_sqrt (show s ^ 2 ≤ c + s ^ 2 by linarith)
    rwa [Real.sqrt_sq_eq_abs] at h
  have habs_t : |t| ≤ ft := by
    have h := Real.sqrt_le_sqrt (show t ^ 2 ≤ c + t ^ 2 by linarith)
    rwa [Real.sqrt_sq_eq_abs] at h
  have hst : |s + t| ≤ fs + ft := (abs_add_le s t).trans (add_le_add habs_s habs_t)
  exact (mul_le_mul_iff_left₀ hp).mp (by
    nlinarith [mul_le_mul_of_nonneg_left hst (abs_nonneg (s - t))])

theorem abs_div_le_of_one_le (a d : ℝ) (hd : 1 ≤ d) : |a / d| ≤ |a| := by
  rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).2
    (by nlinarith [abs_nonneg a])

/-- Cauchy/Poisson-kernel reciprocal difference: `1+x² ≥ 1` kills the division. -/
theorem reciprocal_quadratic_difference (r s : ℝ) :
    |1 / (1 + r ^ 2) - 1 / (1 + s ^ 2)| ≤ |r - s| * (|r| + |s|) := by
  have hr : 1 + r ^ 2 ≠ 0 := by positivity
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have heq : 1 / (1 + r ^ 2) - 1 / (1 + s ^ 2) =
      (s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2)) := by
    field_simp ; ring
  rw [heq]
  calc
    |(s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2))| ≤ |(s - r) * (s + r)| :=
      abs_div_le_of_one_le _ _ (by
        nlinarith only [sq_nonneg r, sq_nonneg s, mul_nonneg (sq_nonneg r) (sq_nonneg s)])
    _ ≤ |r - s| * (|r| + |s|) := by
      rw [abs_mul, abs_sub_comm s r]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_add_le s r]) (abs_nonneg _)
""".strip("\n")


@dataclass(frozen=True)
class ComparabilityEnvelopeCert:
    mode: str = "calculus"


def comparability_envelope_certificate() -> ComparabilityEnvelopeCert:
    return ComparabilityEnvelopeCert()


def certify_comparability_envelope_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=comparability_envelope_certificate())
    return inst, 1


@dataclass
class ComparabilityEnvelopeEmitter(Emitter):
    """Emit the fixed comparability/Lipschitz atoms (once per file)."""

    def __post_init__(self):
        self.kind = "comparability_envelope"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return COMPARABILITY_PRELUDE + "\n", 4


def comparability_envelope_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``comparability_envelope`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("comparability_envelope", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
