"""QuadraticIrrationalSeparation emitter — distilled from the OpenAI
Navier--Stokes formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/DiophantineGraph.lean``).

The construction places its wave carriers on integer frequencies ``(m, n)`` and
needs its two graph directions ``v_r = (1, 1 - √2)``, ``v_t = (√2 - 1, 1)`` to be
UNIFORMLY badly approximated by the integer lattice -- otherwise the correction
scheme's small divisors are uncontrolled.  ``DiophantineGraph.lean`` proves this
by the classical quadratic-irrational trick: for integers ``(p, q)`` not both
zero the CONJUGATE PRODUCT

    (p + √d·q)·(p − √d·q) = p² − d·q²

is a NONZERO integer (nonzero because √d is irrational), hence has absolute value
at least one:

    1 ≤ |p + √d·q| · |p − √d·q|.

This emitter ships that atom for any positive non-square integer ``d``:

  * ``conjugate_product`` : the real identity ``(p+√d q)(p−√d q) = p² − d q²``,
    closed by ``nlinarith`` off ``Real.sq_sqrt``;
  * ``norm_lower``        : ``p² − d q² ≠ 0 → 1 ≤ |p+√d q|·|p−√d q|``, closed via
    ``Int.one_le_abs`` on the integer norm + the identity.

HONESTY SEAM (zeta-23 discipline): the ``norm_lower`` theorem takes the norm's
NON-VANISHING ``p² − d q² ≠ 0`` as a HYPOTHESIS.  That non-vanishing is exactly
where the irrationality / square-freeness of ``d`` enters analytically; the
kernel here proves only the algebraic implication "nonzero integer norm ⟹ product
≥ 1".  ``conjecture1_proved = False``.  A perfect-square ``d`` is REFUSED (then
√d is rational, the norm can vanish for nonzero ``(p,q)``, and the separation is
vacuous) -- the negative control.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class QuadraticIrrationalCert:
    """The radicand ``d`` (positive, non-square) of a ℤ[√d] separation atom."""

    d: int


def quadratic_irrational_certificate(d) -> QuadraticIrrationalCert:
    """Build and re-check a ℤ[√d] separation certificate.  Refuses ``d ≤ 0`` and
    perfect squares (√d rational ⟹ the conjugate norm can vanish for nonzero
    ``(p, q)`` and the badly-approximable framing is vacuous)."""
    d = int(d)
    if d <= 0:
        raise ValueError(f"quadratic_irrational REFUSED: need d > 0; got {d}")
    r = sp.Integer(d)
    if sp.sqrt(r).is_Integer:
        raise ValueError(
            f"quadratic_irrational REFUSED: d = {d} is a perfect square "
            f"(√d rational; norm vanishes for nonzero (p,q) — separation vacuous)")
    return QuadraticIrrationalCert(d=d)


def certify_quadratic_irrational_point(family, pt, name):
    """Certify one ℤ[√d] instance: ``(CertifiedInstance, 2)`` (the identity and
    the nonzero-integer lower bound)."""
    d = family.special[1](pt)
    cert = quadratic_irrational_certificate(d)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class QuadraticIrrationalEmitter(Emitter):
    """Emit the ℤ[√d] conjugate-product identity and the ``|p+√d q||p−√d q| ≥ 1``
    lower bound (with the norm's non-vanishing as an analytic-side hypothesis).
    Self-contained over ℝ/ℤ; ``nlinarith`` off ``Real.sq_sqrt`` and
    ``Int.one_le_abs``."""

    def __post_init__(self):
        self.kind = "quadratic_irrational"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: QuadraticIrrationalCert = inst.payload  # type: ignore[assignment]
            d = cert.d
            nm = inst.lean_name
            lines.append(
                f"-- {nm}_id: ℤ[√{d}] conjugate-product identity "
                f"(NS/Euler DiophantineGraph shape).\n"
                f"theorem {nm}_id (p q : ℝ) :\n"
                f"    (p + Real.sqrt {d} * q) * (p - Real.sqrt {d} * q) = p^2 - {d} * q^2 := by\n"
                f"  have hsq : Real.sqrt {d} ^ 2 = ({d} : ℝ) := Real.sq_sqrt (by norm_num)\n"
                f"  nlinarith [hsq]\n"
                f"\n"
                f"-- {nm}_norm_lower: nonzero integer norm ⟹ conjugate product ≥ 1.\n"
                f"-- Honesty seam: the non-vanishing p²−{d}q² ≠ 0 is a HYPOTHESIS — that is\n"
                f"-- where irrationality/square-freeness of {d} enters; not proved here.\n"
                f"theorem {nm}_norm_lower (p q : ℤ) (hnz : p^2 - {d} * q^2 ≠ 0) :\n"
                f"    1 ≤ |(p : ℝ) + Real.sqrt {d} * q| * |(p : ℝ) - Real.sqrt {d} * q| := by\n"
                f"  have hsq : Real.sqrt {d} ^ 2 = ({d} : ℝ) := Real.sq_sqrt (by norm_num)\n"
                f"  have hprod : ((p : ℝ) + Real.sqrt {d} * q) * ((p : ℝ) - Real.sqrt {d} * q)\n"
                f"      = ((p^2 - {d} * q^2 : ℤ) : ℝ) := by push_cast; nlinarith [hsq]\n"
                f"  have hi : (1 : ℤ) ≤ |p^2 - {d} * q^2| := Int.one_le_abs hnz\n"
                f"  have hr : (1 : ℝ) ≤ |((p^2 - {d} * q^2 : ℤ) : ℝ)| := by exact_mod_cast hi\n"
                f"  rwa [← hprod, abs_mul] at hr\n"
            )
            n_thm += 2
        return "\n".join(lines), n_thm


def quadratic_irrational_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a ℤ[√d] separation family (kind ``quadratic_irrational``).
    ``spec: pt -> d`` (a positive non-square integer)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("quadratic_irrational", spec),
        constants=dict(constants or {}),
    )
