"""FinitePrefixAbsorption emitter — "eventually bounded ⟹ globally bounded,
with an explicit constant" distilled from the OpenAI Navier--Stokes blowup
formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/GaugeAliasDecay.lean`` ``scalar_bound_of_tail``, Apache-2.0;
4 instances across 2 files).

The ubiquitous asymptotic-to-uniform upgrade: a tail bound ``|f n| ≤ A·w n``
for ``n ≥ N`` extends to ALL ``n`` after enlarging the constant by the finite
prefix, with the EXPLICIT witness

    C := A + Σ_{n<N} |f n| / w n.

Nothing in Telperion CONSTRUCTS this enlarged constant (``monotone_tail``
proves pointwise inequalities under uniform hypotheses); the witness is a
computable ``Finset`` sum, so the whole argument is kernel-cheap (no analysis).

Single mode: the fixed generic atom (the sequence, weight, tail constant, and
cutoff are all quantified).  HONESTY SEAM: the tail bound itself is an
analytic-side HYPOTHESIS; the kernel certifies only the absorption logic.
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

PREFIX_ABSORPTION_ATOM = r"""
-- Finite-prefix absorption, ported from OpenAI's Navier-Stokes blowup
-- formalization (github.com/openai/NavierStokesAndEuler,
-- NavierStokes/GaugeAliasDecay.lean scalar_bound_of_tail; Apache-2.0).
-- Trust seam: the tail bound htail is an analytic-side HYPOTHESIS; the
-- explicit witness C = A + sum_{n<N} |f n| / w n does the absorption.

theorem finite_prefix_absorption (f w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (htail : ∀ n, N ≤ n → |f n| ≤ A * w n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |f n| ≤ C * w n := by
  let B := ∑ n ∈ Finset.range N, |f n| / w n
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => div_nonneg (abs_nonneg _) (hw n).le)
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (htail n hn).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (hw n).le)
  · have hterm : |f n| / w n ≤ B :=
      Finset.single_le_sum (fun k _ => div_nonneg (abs_nonneg _) (hw k).le)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    calc
      |f n| = (|f n| / w n) * w n := (div_mul_cancel₀ _ (hw n).ne').symm
      _ ≤ B * w n := mul_le_mul_of_nonneg_right hterm (hw n).le
      _ ≤ (A + B) * w n := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (hw n).le
""".strip("\n")


@dataclass(frozen=True)
class FinitePrefixAbsorptionCert:
    """The fixed atom (no per-instance numeric data)."""

    mode: str = "generic"


def finite_prefix_absorption_certificate() -> FinitePrefixAbsorptionCert:
    return FinitePrefixAbsorptionCert()


def certify_finite_prefix_absorption_point(family, pt, name):
    """``spec(pt)`` is ignored (the atom is fully generic); one structural check."""
    _ = family.special[1](pt)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=finite_prefix_absorption_certificate())
    return inst, 1


@dataclass
class FinitePrefixAbsorptionEmitter(Emitter):
    """Emit the fixed absorption atom (once per file).  The tail bound is a
    hypothesis; the enlarged constant is an explicit Finset-sum witness."""

    def __post_init__(self):
        self.kind = "finite_prefix_absorption"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        return PREFIX_ABSORPTION_ATOM + "\n", 1


def finite_prefix_absorption_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``finite_prefix_absorption`` (fully generic atom; spec unused)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("finite_prefix_absorption", spec or (lambda pt: None)),
        constants=dict(constants or {}),
    )
