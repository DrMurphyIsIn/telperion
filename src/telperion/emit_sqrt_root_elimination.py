"""SqrtRootElimination emitter — symbolic radical elimination distilled from the
OpenAI Navier--Stokes formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/ConeAlgebra.lean`` ``true_cone_iff`` / ``ProfileSpectralCone.lean``,
Apache-2.0).

The blowup cone algebra repeatedly needs "the state is below the lower root of a
quadratic" rewritten WITHOUT the radical.  The generic two-way atom is

    v < E − u·√rad   ⟺   (v < E  ∧  u²·rad < (E − v)²)      (u, rad ≥ 0)

— "below a shifted-sqrt threshold iff a discriminant-style inequality" — plus the
one-way amplitude transfer ``k² = g/2 ∧ g·t² < 2s² ∧ 0 < s ⟹ |k·t| < s``.

Per instance the user supplies symbolic ``(E, u, rad)`` and the ELIMINATED
quadratic form ``Q``; the load-bearing certificate is the exact polynomial
identity

    (E − v)² − u²·rad  ≡  Q

checked EXACTLY in sympy at certify time (a corrupted ``Q`` is refused — and
would independently break the emitted ``ring``).  The emitted theorem is

    v < E − u·√rad ⟺ (v < E ∧ 0 < Q)

with the side conditions ``0 ≤ u``, ``0 ≤ rad`` as HYPOTHESES (the honesty
seam: their positivity is the caller's analytic obligation; for the NS cone
they follow from ``2 < P``).

Directly reusable on the BG price-interval and RH boundary-curve fronts
(quadratic-formula thresholds with symbolic parameters), per the BG↔RH
cross-pollination standing order.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# --------------------------------------------------------------------------- #
# Fixed generic atoms (emitted once per file, self-contained)                  #
# --------------------------------------------------------------------------- #

SQRT_ELIM_PRELUDE = r"""
-- Radical-elimination atoms, distilled from OpenAI's Navier-Stokes blowup
-- formalization (github.com/openai/NavierStokesAndEuler, ConeAlgebra.lean
-- true_cone_iff; Apache-2.0).  Self-contained over ℝ.

/-- Below a shifted-sqrt threshold iff the discriminant-style inequality. -/
theorem sqrt_shift_lt_iff (E u rad v : ℝ) (hu : 0 ≤ u) (hrad : 0 ≤ rad) :
    v < E - u * Real.sqrt rad ↔ (v < E ∧ u ^ 2 * rad < (E - v) ^ 2) := by
  have hs : Real.sqrt rad ^ 2 = rad := Real.sq_sqrt hrad
  have hs0 : 0 ≤ Real.sqrt rad := Real.sqrt_nonneg rad
  have hur : 0 ≤ u * Real.sqrt rad := mul_nonneg hu hs0
  constructor
  · intro h
    have hvE : v < E := by linarith
    refine ⟨hvE, ?_⟩
    have h3 : u * Real.sqrt rad < E - v := by linarith
    have h4 := mul_self_lt_mul_self hur h3
    nlinarith [hs, h4]
  · rintro ⟨hvE, hq⟩
    have h1 : u * Real.sqrt rad = Real.sqrt (u ^ 2 * rad) := by
      rw [Real.sqrt_mul (by positivity) rad, Real.sqrt_sq hu]
    have h2 : Real.sqrt (u ^ 2 * rad) < Real.sqrt ((E - v) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) hq
    rw [Real.sqrt_sq (by linarith)] at h2
    have h3 : u * Real.sqrt rad < E - v := by rw [h1]; exact h2
    linarith

/-- One-way amplitude transfer: a squared-amplitude budget caps the product. -/
theorem sqrt_amplitude_transfer (k g t s : ℝ)
    (hk : k ^ 2 = g / 2) (hq : g * t ^ 2 < 2 * s ^ 2) (hs : 0 < s) :
    |k * t| < s := by
  by_contra hcon
  rw [not_lt] at hcon
  have habs : 0 ≤ |k * t| := abs_nonneg (k * t)
  have hsq : s * s ≤ |k * t| * |k * t| :=
    mul_le_mul hcon hcon hs.le habs
  have hkt : |k * t| * |k * t| = (k * t) ^ 2 := by
    rw [← sq_abs]
    ring
  nlinarith [hsq, hkt]
""".strip("\n")


# --------------------------------------------------------------------------- #
# Certification                                                               #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class SqrtRootElimCert:
    """One radical-elimination instance: symbols, the designated state symbol
    ``v``, the threshold pieces ``(E, u, rad)``, and the eliminated form ``Q``
    with the identity ``(E − v)² − u²·rad ≡ Q`` re-verified exactly."""

    variables: tuple[sp.Symbol, ...]
    v: sp.Symbol
    E: sp.Expr
    u: sp.Expr
    rad: sp.Expr
    Q: sp.Expr


def sqrt_root_elim_certificate(variables, v, E, u, rad, Q) -> SqrtRootElimCert:
    """Build and EXACTLY re-check a radical-elimination instance.  Refuses a
    ``Q`` that is not identically ``(E − v)² − u²·rad`` (the corrupted-certificate
    negative control) and a ``v`` missing from ``variables``."""
    variables = tuple(variables)
    if v not in variables:
        raise ValueError("sqrt_root_elimination REFUSED: v must be one of the variables")
    E, u, rad, Q = (sp.nsimplify(e) if not isinstance(e, sp.Expr) else e
                    for e in (E, u, rad, Q))
    residual = sp.expand((E - v) ** 2 - u ** 2 * rad - Q)
    if sp.simplify(residual) != 0:
        raise ValueError(
            "sqrt_root_elimination REFUSED: certificate identity fails — "
            f"(E − v)² − u²·rad − Q ≡ {residual} ≠ 0 (corrupted Q)")
    return SqrtRootElimCert(variables=variables, v=v, E=E, u=u, rad=rad, Q=Q)


def certify_sqrt_root_elim_point(family, pt, name):
    """Certify one instance: ``(CertifiedInstance, 1)`` (the ring identity).

    ``spec(pt) -> (variables, v, E, u, rad, Q)``."""
    variables, v, E, u, rad, Q = family.special[1](pt)
    cert = sqrt_root_elim_certificate(variables, v, E, u, rad, Q)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# --------------------------------------------------------------------------- #
# Emitter                                                                     #
# --------------------------------------------------------------------------- #


@dataclass
class SqrtRootEliminationEmitter(Emitter):
    """Emit the generic radical-elimination atoms (once per file) plus
    per-instance specializations whose load-bearing ``Q`` identity is re-proved
    by ``ring`` in-kernel.  Side conditions ``0 ≤ u``, ``0 ≤ rad`` are
    hypotheses (the analytic trust seam)."""

    def __post_init__(self):
        self.kind = "sqrt_root_elimination"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [SQRT_ELIM_PRELUDE, ""]
        n_thm = 2  # the two generic atoms
        for inst in fam.instances:
            cert: SqrtRootElimCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            syms = cert.variables
            names = " ".join(s.name for s in syms)
            e, u, rad, q = (expr_lean(x, syms) for x in (cert.E, cert.u, cert.rad, cert.Q))
            vn = cert.v.name
            lines.append(
                f"-- {nm}: radical elimination for E={cert.E}, u={cert.u}, rad={cert.rad}.\n"
                f"-- Certificate: (E − {vn})² − u²·rad ≡ Q, re-proved by ring in-kernel.\n"
                f"-- Trust seam: 0 ≤ u and 0 ≤ rad are HYPOTHESES (caller's obligation).\n"
                f"theorem {nm} ({names} : ℝ) (hu : 0 ≤ {u}) (hrad : 0 ≤ {rad}) :\n"
                f"    {vn} < ({e}) - ({u}) * Real.sqrt ({rad}) ↔\n"
                f"      ({vn} < ({e}) ∧ 0 < ({q})) := by\n"
                f"  have hid : (({e}) - {vn}) ^ 2 - ({u}) ^ 2 * ({rad}) = ({q}) := by ring\n"
                f"  have h := sqrt_shift_lt_iff ({e}) ({u}) ({rad}) {vn} hu hrad\n"
                f"  constructor\n"
                f"  · intro hlt\n"
                f"    obtain ⟨h1, h2⟩ := h.mp hlt\n"
                f"    exact ⟨h1, by linarith [hid]⟩\n"
                f"  · rintro ⟨h1, h2⟩\n"
                f"    exact h.mpr ⟨h1, by linarith [hid]⟩\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def sqrt_root_elimination_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a radical-elimination family (kind ``sqrt_root_elimination``).

    ``spec: pt -> (variables, v, E, u, rad, Q)`` with sympy Symbols/exprs;
    ``Q`` must satisfy ``(E − v)² − u²·rad ≡ Q`` exactly."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("sqrt_root_elimination", spec),
        constants=dict(constants or {}),
    )
