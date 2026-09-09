"""GradedConvolutionEndpoint emitter — exact identity calculus on truncated
antidiagonal convolutions, distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``Euler/FiniteGradeTriangular.lean``
/ ``FiniteGradeDiagonal.lean``, Apache-2.0; same engine in
``NavierStokes/PositiveAxisSystem.lean``).

The frozen-lower-triangle reformulation of order-n power-series/jet equations:
for a bilinear ``B`` and graded coefficients ``u``, the grade-n convolution
``gconv B u v n := Σ_{i≤n} B (u i) (v (n−i))`` obeys EXACT additive identities:

  * ``gconv_congr_below``  — grade n depends only on grades ≤ n;
  * ``gconv_strict_congr`` — with zero constant term, the SLOW grade p depends
    only on grades < p (the unknown does not feed its own equation);
  * ``gconv_next_delta``   — perturbing grade p by δ moves grade p+1 by exactly
    ``B δ (u 1) + B (u 1) δ`` (the two endpoint dependencies).

Genericized from the source: the truncation parameter ``M`` (pure bookkeeping)
is dropped — ``gconv`` is defined directly in range form.  Fixed generic atoms
over abstract ℝ-modules; discharge = ``Finset.sum_congr`` + per-index
``by_cases``/``omega`` + ``sum_ite_eq'``.

HONESTY SEAM: none — exact finitary identities.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

GRADED_CONVOLUTION_PRELUDE = r"""
-- Graded-convolution endpoint calculus, ported (truncation-genericized) from
-- OpenAI's Euler blowup formalization (github.com/openai/NavierStokesAndEuler,
-- FiniteGradeDiagonal/FiniteGradeTriangular; Apache-2.0).
open Finset

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The grade-`n` bilinear convolution `Σ_{i≤n} B (u i) (v (n−i))`. -/
def gconv (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u v : ℕ → V) (n : ℕ) : W :=
  ∑ i ∈ range (n + 1), B (u i) (v (n - i))

/-- Grade `n` depends only on grades `≤ n`. -/
theorem gconv_congr_below (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' v v' : ℕ → V) (n : ℕ)
    (hu : ∀ i ≤ n, u i = u' i) (hv : ∀ i ≤ n, v i = v' i) :
    gconv B u v n = gconv B u' v' n := by
  unfold gconv
  apply sum_congr rfl
  intro i hi
  rw [hu i (by have h := mem_range.mp hi; omega), hv (n - i) (Nat.sub_le n i)]

/-- With zero constant term, the slow grade `p` depends only on grades `< p`. -/
theorem gconv_strict_congr (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (p : ℕ)
    (hp : 0 < p) (hu0 : u 0 = 0) (hu : ∀ i < p, u' i = u i) :
    gconv B u' u' p = gconv B u u p := by
  unfold gconv
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ p := by have h := mem_range.mp hi; omega
  by_cases hi0 : i = 0
  · simp only [hi0, hu 0 hp, hu0, map_zero, LinearMap.zero_apply]
  by_cases hip : i = p
  · simp only [hip, Nat.sub_self, hu 0 hp, hu0, map_zero]
  rw [hu i (by omega), hu (p - i) (by omega)]

/-- Perturbing grade `p` by `δ` moves grade `p+1` by exactly the two endpoint
dependencies `B δ (u 1) + B (u 1) δ`. -/
theorem gconv_next_delta (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (δ : V) (p : ℕ)
    (hp : 2 ≤ p) (hu0 : u 0 = 0) (hu : ∀ i < p, u' i = u i) (hδ : u' p = u p + δ) :
    gconv B u' u' (p + 1) = gconv B u u (p + 1) + B δ (u 1) + B (u 1) δ := by
  unfold gconv
  have hterm : ∀ i ∈ range (p + 2),
      B (u' i) (u' (p + 1 - i)) = B (u i) (u (p + 1 - i)) +
        (if i = p then B δ (u 1) else 0) + (if i = 1 then B (u 1) δ else 0) := by
    intro i hi
    have hi' : i ≤ p + 1 := by have h := mem_range.mp hi; omega
    by_cases hi0 : i = 0
    · simp [hi0, hu 0 (by omega), hu0, show (0 : ℕ) ≠ p by omega]
    by_cases hiend : i = p + 1
    · simp [hiend, hu 0 (by omega), hu0, show p ≠ 0 by omega]
    by_cases hip : i = p
    · simp [hip, hδ, hu 1 (by omega), show p ≠ 1 by omega, map_add,
        LinearMap.add_apply]
    by_cases hi1 : i = 1
    · simp [hi1, hδ, hu 1 (by omega), show 1 ≠ p by omega, map_add]
    rw [hu i (by omega), hu (p + 1 - i) (by omega)]
    simp [hip, hi1]
  calc
    _ = ∑ i ∈ range (p + 2),
        (B (u i) (u (p + 1 - i)) + (if i = p then B δ (u 1) else 0) +
          (if i = 1 then B (u 1) δ else 0)) := sum_congr rfl hterm
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib]
      simp only [sum_ite_eq', mem_range, show p < p + 2 by omega,
        show 1 < p + 2 by omega, ite_true]
""".strip("\n")


@dataclass(frozen=True)
class GradedConvolutionCert:
    mode: str = "calculus"


def graded_convolution_certificate() -> GradedConvolutionCert:
    return GradedConvolutionCert()


def certify_graded_convolution_point(family, pt, name):
    """``spec(pt)`` ignored (fully generic atoms); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(),
                            payload=graded_convolution_certificate())
    return inst, 1


@dataclass
class GradedConvolutionEmitter(Emitter):
    """Emit the fixed graded-convolution identity atoms (once per file)."""

    def __post_init__(self):
        self.kind = "graded_convolution"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return GRADED_CONVOLUTION_PRELUDE + "\n", 3


def graded_convolution_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``graded_convolution`` (fully generic atoms; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("graded_convolution", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
