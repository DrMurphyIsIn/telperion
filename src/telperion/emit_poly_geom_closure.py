"""PolynomialWeightedGeometricClosure emitter — exact-invariant uniform bounds
for polynomially-weighted geometric series, distilled from the OpenAI Euler
blowup formalization (``github.com/openai/NavierStokesAndEuler``,
``Euler/PacketFieldSobolevBudget.lean`` ``half_square_sum_identity`` /
``square_geometric_le_twelve``, Apache-2.0).

For a polynomial weight ``p(n)`` (nonneg rational coefficients) and an anchor
rate ``ρ ∈ (0,1)``, this emitter SYNTHESIZES the exact remainder polynomial
``q`` (same degree) solving the backward recurrence

    q(N) = p(N) + ρ·q(N+1)        (polynomial identity),

so that the partial sums carry the EXACT invariant

    Σ_{n<N} ρⁿ·p(n) + q(N)·ρᴺ = q(0)          for every N,

closed in Lean by induction + ``push_cast; ring``.  With ``q``'s coefficients
nonnegative (checked; refused otherwise), ``positivity`` kills the remainder and
any ``0 ≤ r ≤ ρ`` transfers termwise:

    Σ_{n<N} rⁿ·p(n) ≤ q(0)        uniformly in N.

The source instance is ``p(n) = (n+1)²``, ``ρ = 1/2``, ``q(N) = 2N²+8N+12``,
bound ``12``.  The synthesis is a triangular rational linear solve — fully
mechanical for arbitrary polynomial weight and rational rate.

Negative controls: ``ρ ∉ (0,1)``, a negative weight coefficient, a synthesized
remainder with a negative coefficient (all refused).

HONESTY SEAM: none needed — this is a self-contained finitary bound; the
certificate content is the exact remainder synthesis.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class PolyGeomClosureCert:
    """Weight coefficients ``p`` (lowest-first), anchor rate ``ρ``, synthesized
    remainder coefficients ``q`` (lowest-first), and the uniform bound
    ``B = q(0)``.  Invariant ``q(N) − ρ·q(N+1) − p(N) ≡ 0`` re-verified."""

    p: tuple[sp.Rational, ...]
    rho: sp.Rational
    q: tuple[sp.Rational, ...]
    B: sp.Rational


def poly_geom_closure_certificate(p_coeffs, rho) -> PolyGeomClosureCert:
    """Synthesize the remainder and EXACTLY re-check the invariant."""
    p = tuple(sp.Rational(sp.nsimplify(c)) for c in p_coeffs)
    rho = sp.Rational(sp.nsimplify(rho))
    if not (0 < rho < 1):
        raise ValueError(f"poly_geom_closure REFUSED: need anchor 0 < ρ < 1; got {rho}")
    if len(p) < 1 or all(c == 0 for c in p):
        raise ValueError("poly_geom_closure REFUSED: zero weight")
    for c in p:
        if not c >= 0:
            raise ValueError(
                f"poly_geom_closure REFUSED: weight coefficient {c} < 0 "
                f"(termwise transfer needs p(n) ≥ 0 by positivity)")
    N = sp.Symbol("N")
    d = len(p) - 1
    pN = sum(c * N ** i for i, c in enumerate(p))
    cs = sp.symbols(f"c0:{d + 1}")
    qN = sum(cs[i] * N ** i for i in range(d + 1))
    qN1 = sum(cs[i] * (N + 1) ** i for i in range(d + 1))
    sol = sp.solve(sp.Poly(sp.expand(qN - rho * qN1 - pN), N).coeffs(), cs, dict=True)
    if not sol:
        raise ValueError("poly_geom_closure REFUSED: remainder synthesis has no solution")
    q = tuple(sp.Rational(sol[0][cs[i]]) for i in range(d + 1))
    for c in q:
        if not c >= 0:
            raise ValueError(
                f"poly_geom_closure REFUSED: synthesized remainder coefficient {c} < 0 "
                f"(positivity cannot kill the remainder)")
    # exact re-validation of the invariant recurrence
    qNs = sum(q[i] * N ** i for i in range(d + 1))
    qN1s = sum(q[i] * (N + 1) ** i for i in range(d + 1))
    assert sp.expand(qNs - rho * qN1s - pN) == 0
    B = q[0]
    return PolyGeomClosureCert(p=p, rho=rho, q=q, B=sp.Rational(B))


def certify_poly_geom_closure_point(family, pt, name):
    """``spec(pt) -> (p_coeffs, ρ)``.  n_checks = 3 (rate range, coefficient
    signs, invariant identity)."""
    p_coeffs, rho = family.special[1](pt)
    cert = poly_geom_closure_certificate(p_coeffs, rho)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 3


def _cast_poly(coeffs: Sequence[sp.Rational], var: str) -> str:
    """Render ``c₀ + c₁·(var:ℝ) + …`` (all terms kept, lowest-first)."""
    parts = [f"({rat_lean(coeffs[0])})"]
    for i, c in enumerate(coeffs[1:], start=1):
        pw = f"({var} : ℝ)" if i == 1 else f"({var} : ℝ) ^ {i}"
        parts.append(f"({rat_lean(c)}) * {pw}")
    return " + ".join(parts)


@dataclass
class PolyGeomClosureEmitter(Emitter):
    """Emit the exact partial-sum invariant (induction + ``push_cast; ring``)
    plus the uniform transfer bound for any ``0 ≤ r ≤ ρ``."""

    def __post_init__(self):
        self.kind = "poly_geom_closure"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: PolyGeomClosureCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            rho, B = rat_lean(cert.rho), rat_lean(cert.B)
            pn = _cast_poly(cert.p, "n")
            qN = _cast_poly(cert.q, "N")
            lines.append(
                f"-- {nm}: polynomially-weighted geometric closure, weight p={list(cert.p)},\n"
                f"-- anchor ρ={cert.rho}, synthesized remainder q={list(cert.q)}, bound B=q(0)={cert.B}.\n"
                f"-- Ported/mechanized from NavierStokesAndEuler PacketFieldSobolevBudget.lean\n"
                f"-- (p=(n+1)², ρ=1/2, B=12 instance; Apache-2.0).\n"
                f"theorem {nm}_identity (N : ℕ) :\n"
                f"    (∑ n ∈ Finset.range N, ({rho} : ℝ) ^ n * ({pn})) +\n"
                f"      ({qN}) * ({rho} : ℝ) ^ N = ({B}) := by\n"
                f"  induction N with\n"
                f"  | zero => norm_num\n"
                f"  | succ N ih =>\n"
                f"    rw [Finset.sum_range_succ, pow_succ ({rho} : ℝ) N]\n"
                f"    convert ih using 1\n"
                f"    push_cast\n"
                f"    ring\n"
                f"\n"
                f"theorem {nm} (r : ℝ) (hr : 0 ≤ r) (hrho : r ≤ ({rho})) (N : ℕ) :\n"
                f"    (∑ n ∈ Finset.range N, r ^ n * ({pn})) ≤ ({B}) := by\n"
                f"  have hs : (∑ n ∈ Finset.range N, ({rho} : ℝ) ^ n * ({pn})) ≤ ({B}) := by\n"
                f"    have h := {nm}_identity N\n"
                f"    have hp : 0 ≤ ({qN}) * ({rho} : ℝ) ^ N := by positivity\n"
                f"    linarith only [h, hp]\n"
                f"  refine (Finset.sum_le_sum fun n _ => ?_).trans hs\n"
                f"  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrho n) (by positivity)\n"
            )
            n_thm += 2
        return "\n".join(lines), n_thm


def poly_geom_closure_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``poly_geom_closure``; ``spec: pt -> (p_coeffs lowest-first, ρ)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("poly_geom_closure", spec),
        constants=dict(constants or {}),
    )
