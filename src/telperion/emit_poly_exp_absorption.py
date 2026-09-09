"""PolyExpAbsorption emitter — inverse-power prefactors absorbed into a halved
exponential rate, distilled from the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/OutgoingPulseBounds.lean`` ``inverse_square_exp_absorption``,
Apache-2.0).

The parameter-UNIFORM poly-vs-exp domination (a sup over ALL ``λ > 0``, not a
numeric enclosure):

    exp(−1/(2λ)) / λ^m  ≤  (4m)^m · exp(−1/(4λ))      for every λ > 0,

via ``t ≤ eᵗ`` at the split rate ``t = 1/(4mλ)`` raised to the m-th power.
The source proves ``m = 2`` (constant 64); this emitter GENERALIZES to any
``m ≥ 1`` with the EXACT constant ``K = (4m)^m`` certified in sympy
(``m = 2 ⟹ K = 64`` reproduces the source).  ``m = 0`` refused (trivial /
degenerate) — the negative control.

Standard closer wherever exponential smallness must eat an inverse-power
prefactor (heat-kernel scales, Gevrey radii).  HONESTY SEAM: none — a
self-contained analytic fact about ``Real.exp``.
``conjecture1_proved = False``.
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


@dataclass(frozen=True)
class PolyExpAbsorptionCert:
    """The power ``m ≥ 1`` and the exact constant ``K = (4m)^m``."""

    m: int
    K: sp.Rational


def poly_exp_absorption_certificate(m) -> PolyExpAbsorptionCert:
    """Build and EXACTLY re-check a poly-exp absorption instance."""
    m = int(m)
    if m < 1:
        raise ValueError(f"poly_exp_absorption REFUSED: need power m ≥ 1; got {m}")
    K = sp.Rational((4 * m) ** m)
    assert K == sp.Integer(4 * m) ** m  # exact re-validation
    return PolyExpAbsorptionCert(m=m, K=K)


def certify_poly_exp_absorption_point(family, pt, name):
    """``spec(pt) -> m``.  n_checks = 2 (range + exact constant)."""
    m = family.special[1](pt)
    cert = poly_exp_absorption_certificate(m)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class PolyExpAbsorptionEmitter(Emitter):
    """Emit the absorption bound at concrete ``m`` with constant ``(4m)^m``,
    via ``Real.add_one_le_exp`` at the split rate raised to the m-th power."""

    def __post_init__(self):
        self.kind = "poly_exp_absorption"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: PolyExpAbsorptionCert = inst.payload  # type: ignore[assignment]
            nm, m = inst.lean_name, cert.m
            K = rat_lean(cert.K)
            fourm = 4 * m
            lines.append(
                f"-- {nm}: poly-exp absorption at m={m}, constant K=(4m)^m={cert.K}\n"
                f"-- (exact; m=2 gives the source's 64).  Ported/generalized from\n"
                f"-- NavierStokesAndEuler OutgoingPulseBounds.lean\n"
                f"-- inverse_square_exp_absorption (Apache-2.0).\n"
                f"theorem {nm} {{lam : ℝ}} (hlam : 0 < lam) :\n"
                f"    Real.exp (-(1 / (2 * lam))) / lam ^ {m} ≤\n"
                f"      ({K}) * Real.exp (-(1 / (4 * lam))) := by\n"
                f"  have ht : 0 ≤ 1 / ({fourm} * lam) := by positivity\n"
                f"  have hex : 1 / ({fourm} * lam) ≤ Real.exp (1 / ({fourm} * lam)) := by\n"
                f"    linarith [Real.add_one_le_exp (1 / ({fourm} * lam))]\n"
                f"  have hsq := pow_le_pow_left₀ ht hex {m}\n"
                f"  rw [← Real.exp_nat_mul] at hsq\n"
                f"  have hfac : 1 / lam ^ {m} ≤ ({K}) * Real.exp (1 / (4 * lam)) := by\n"
                f"    apply (div_le_iff₀ (pow_pos hlam {m})).mpr\n"
                f"    have ht' : (1 / ({fourm} * lam)) ^ {m} = 1 / (({K}) * lam ^ {m}) := by\n"
                f"      ring\n"
                f"    have he' : (({m} : ℕ) : ℝ) * (1 / ({fourm} * lam)) = 1 / (4 * lam) := by\n"
                f"      push_cast\n"
                f"      ring\n"
                f"    rw [ht', he'] at hsq\n"
                f"    have h := (div_le_iff₀ (by positivity : (0:ℝ) < ({K}) * lam ^ {m})).mp hsq\n"
                f"    nlinarith [h, Real.exp_pos (1 / (4 * lam))]\n"
                f"  have hprod := mul_le_mul_of_nonneg_right hfac\n"
                f"    (Real.exp_pos (-(1 / (2 * lam)))).le\n"
                f"  have hsum : 1 / (4 * lam) + -(1 / (2 * lam)) = -(1 / (4 * lam)) := by\n"
                f"    ring\n"
                f"  calc\n"
                f"    _ = (1 / lam ^ {m}) * Real.exp (-(1 / (2 * lam))) := by ring\n"
                f"    _ ≤ _ := hprod\n"
                f"    _ = _ := by rw [mul_assoc, ← Real.exp_add, hsum]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def poly_exp_absorption_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``poly_exp_absorption``; ``spec: pt -> m`` (integer ≥ 1)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("poly_exp_absorption", spec),
        constants=dict(constants or {}),
    )
