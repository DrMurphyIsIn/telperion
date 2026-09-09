"""TwoRowSolveBound emitter — solution-entry bounds for a 2×2 scalar system,
distilled from the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``NavierStokes/OutgoingPulseBounds.lean``
``two_row_solution_bound``, Apache-2.0; consumed 3× in-file + the 3×3 analog).

From row-scale and column-ratio-gap data alone — ``k ≤ A₀, A₁`` (row scales),
``λ ≤ r₀ − r₁`` (ratio gap), ``0 ≤ r₀ ≤ Rmax`` — the solution of

    A₀·(x₀ + r₀·x₁) = d₀,      A₁·(x₀ + r₁·x₁) = d₁

obeys the explicit inverse bound

    λ·|xᵢ|  ≤  ((1 + Rmax)/k)·(|d₀| + |d₁|)      (i = 0, 1),

pure scalar arithmetic (no ``Matrix``).  GENERALIZED from the source, which
fixes ``Rmax = e``: here the ceiling is an abstract hypothesis.  No existing
kind bounds inverse/solution entries (``cone`` is feasibility, ``affine_ledger``
is direct margins); this is the standard moment/collocation obligation.

Single fixed generic atom (all data quantified).  HONESTY SEAM: the row
equations and scale/gap bounds are HYPOTHESES.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

TWO_ROW_ATOM = r"""
-- 2x2 solution-entry bound, ported (Rmax-generalized from the fixed e) from
-- OpenAI's Navier-Stokes blowup formalization
-- (github.com/openai/NavierStokesAndEuler, OutgoingPulseBounds.lean
-- two_row_solution_bound; Apache-2.0).  Pure scalar, no Matrix.

theorem two_row_solve_bound {k lam Rmax A0 A1 r0 r1 x0 x1 d0 d1 : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hlam' : lam ≤ 1)
    (hA0 : k ≤ A0) (hA1 : k ≤ A1)
    (hr0 : 0 ≤ r0) (hr0' : r0 ≤ Rmax)
    (hgap : lam ≤ r0 - r1)
    (h0 : A0 * (x0 + r0 * x1) = d0) (h1 : A1 * (x0 + r1 * x1) = d1) :
    lam * |x0| ≤ ((1 + Rmax) / k) * (|d0| + |d1|) ∧
      lam * |x1| ≤ ((1 + Rmax) / k) * (|d0| + |d1|) := by
  have hA0p := hk.trans_le hA0
  have hA1p := hk.trans_le hA1
  have h0' : x0 + r0 * x1 = d0 / A0 := (eq_div_iff hA0p.ne').mpr (by nlinarith [h0])
  have h1' : x0 + r1 * x1 = d1 / A1 := (eq_div_iff hA1p.ne').mpr (by nlinarith [h1])
  have ha0 : |d0 / A0| ≤ |d0| / k := by
    rw [abs_div, abs_of_pos hA0p]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk hA0
  have ha1 : |d1 / A1| ≤ |d1| / k := by
    rw [abs_div, abs_of_pos hA1p]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk hA1
  have hdx : (r0 - r1) * x1 = d0 / A0 - d1 / A1 := by nlinarith [h0', h1']
  have hdiff := abs_sub (d0 / A0) (d1 / A1)
  rw [← hdx, abs_mul, abs_of_pos (hlam.trans_le hgap)] at hdiff
  have hx1 : lam * |x1| ≤ (|d0| + |d1|) / k := by
    have hx := mul_le_mul_of_nonneg_right hgap (abs_nonneg x1)
    rw [add_div]
    linarith
  have hx0eq : x0 = d0 / A0 - r0 * x1 := by linarith [h0']
  have hx0 : |x0| ≤ |d0 / A0| + r0 * |x1| := by
    rw [hx0eq]
    simpa only [abs_mul, abs_of_nonneg hr0] using abs_sub (d0 / A0) (r0 * x1)
  have hd : 0 ≤ (|d0| + |d1|) / k := div_nonneg (by positivity) hk.le
  have he : 0 ≤ Rmax := hr0.trans hr0'
  have h0d : |d0| / k ≤ (|d0| + |d1|) / k :=
    div_le_div_of_nonneg_right (by linarith [abs_nonneg d1]) hk.le
  have hsmall : lam * |d0 / A0| ≤ (|d0| + |d1|) / k := by
    have hmul := mul_le_mul_of_nonneg_right hlam' (abs_nonneg (d0 / A0))
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hx0 hlam.le
  have hrscaled : r0 * (lam * |x1|) ≤ Rmax * ((|d0| + |d1|) / k) :=
    mul_le_mul hr0' hx1 (mul_nonneg hlam.le (abs_nonneg x1)) he
  have hid : ((1 + Rmax) / k) * (|d0| + |d1|) =
      (|d0| + |d1|) / k + Rmax * ((|d0| + |d1|) / k) := by ring
  constructor <;> rw [hid]
  · nlinarith
  · nlinarith
""".strip("\n")


@dataclass(frozen=True)
class TwoRowSolveCert:
    """The fixed generic atom (no per-instance numeric data)."""

    mode: str = "generic"


def two_row_solve_certificate() -> TwoRowSolveCert:
    return TwoRowSolveCert()


def certify_two_row_solve_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atom); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=two_row_solve_certificate())
    return inst, 1


@dataclass
class TwoRowSolveEmitter(Emitter):
    """Emit the fixed 2×2 solution-entry bound atom (once per file)."""

    def __post_init__(self):
        self.kind = "two_row_solve"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return TWO_ROW_ATOM + "\n", 1


def two_row_solve_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``two_row_solve`` (fully generic atom; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("two_row_solve", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
