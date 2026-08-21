"""Tangent-line-trick emitter — a symmetric-sum (combinatorial) inequality.

Compete where the frontier is weakest: symmetric / combinatorial inequalities.
For a CONVEX quadratic ``f(x) = c₂x² + c₁x + c₀`` (``c₂ > 0``) and reals
``x₁..xₙ`` with ``Σxᵢ = S``, the tangent line at ``a = S/n`` gives the classic
tangent-line (Jensen) bound

    Σf(xᵢ) ≥ n·f(a) = B.

The certificate is the EXACT ring identity

    Σf(xᵢ) − B = c₂·Σ(xᵢ − a)² + f'(a)·(Σxᵢ − S),

so under the sum constraint the surplus is a nonnegative sum of squares.  The
emitted Lean is hypothesis-light and robust:

    theorem <name> (x₁ … xₙ : ℝ) (hsum : x₁ + … + xₙ = S) :
        (B : ℝ) ≤ f(x₁) + … + f(xₙ) := by
      nlinarith [sq_nonneg (x₁ − a), …, sq_nonneg (xₙ − a), hsum]

`nlinarith` discharges it: the goal is `c₂·Σ(xᵢ−a)² ≥ 0` after eliminating the
constraint, exactly the shape `nlinarith` closes from `sq_nonneg` hints plus the
linear `hsum`.

NEGATIVE CONTROL: a non-convex (``c₂ ≤ 0``) quadratic — where the tangent lies
ABOVE, not below — is refused at certification; no Lean is emitted.  (First
version: convex quadratics.  Higher-degree convex ``f`` extend the same identity
with a per-term SOS factor of ``(x−a)²`` — a documented follow-up.)
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TangentCertificate:
    """A verified tangent-line-trick certificate for a convex quadratic."""

    n: int
    c2: sp.Rational
    c1: sp.Rational
    c0: sp.Rational
    S: sp.Rational
    a: sp.Rational       # tangent point S/n
    B: sp.Rational       # bound n·f(a)
    slope: sp.Rational   # f'(a) = 2·c2·a + c1


def tangent_certificate(*, c2, c1, c0, n, S) -> TangentCertificate:
    """Build and EXACTLY self-check a tangent-line certificate.  Refuses a
    non-convex quadratic (c2 ≤ 0) or n < 2."""
    c2, c1, c0, S = (sp.nsimplify(v) for v in (c2, c1, c0, S))
    n = int(n)
    if not c2 > 0:
        raise ValueError(
            f"tangent-line trick needs a CONVEX quadratic (c₂ > 0); got c₂ = {c2} "
            "— a concave/linear f puts the tangent ABOVE the curve (refused)"
        )
    if n < 2:
        raise ValueError("tangent-line trick needs n ≥ 2 terms")
    a = sp.Rational(S, n)
    B = n * (c2 * a**2 + c1 * a + c0)
    slope = 2 * c2 * a + c1
    # exact ring-identity self-check (the whole certificate, verified)
    xs = sp.symbols(f"x1:{n + 1}")
    lhs = sum(c2 * x**2 + c1 * x + c0 for x in xs) - B
    rhs = c2 * sum((x - a) ** 2 for x in xs) + slope * (sum(xs) - S)
    if sp.expand(lhs - rhs) != 0:
        raise ValueError("tangent identity self-check failed — certificate rejected")
    return TangentCertificate(n=n, c2=c2, c1=c1, c0=c0, S=S, a=a, B=B, slope=slope)


def certify_tangent_point(family, pt, name):
    """Certify one tangent instance from ``family.special[1](pt) -> ((f, x), n, S)``.
    Refuses (ValueError) a non-quadratic or non-convex f."""
    (f, x), n, S = family.special[1](pt)
    f = sp.expand(sp.sympify(f))
    poly = sp.Poly(f, x)
    if poly.degree() != 2:
        raise ValueError(
            f"tangent instance '{name}': f must be a degree-2 polynomial in {x}; "
            f"got degree {poly.degree()}"
        )
    c2 = poly.coeff_monomial(x**2)
    c1 = poly.coeff_monomial(x)
    c0 = poly.coeff_monomial(1)
    cert = tangent_certificate(c2=c2, c1=c1, c0=c0, n=n, S=S)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, cert.n


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class TangentSumEmitter(Emitter):
    """Emit `B ≤ Σf(xᵢ)` (convex-quadratic tangent-line bound) as one theorem per
    certified instance, closed by `nlinarith` over `sq_nonneg` hints + `hsum`."""

    def __post_init__(self):
        self.kind = "tangent"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        ntheorems = 0
        for inst in fam.instances:
            cert: TangentCertificate = inst.payload  # type: ignore[assignment]
            n = cert.n
            xs = [sp.Symbol(f"x{i}") for i in range(1, n + 1)]
            binders = " ".join(f"x{i}" for i in range(1, n + 1))
            hsum_lhs = " + ".join(f"x{i}" for i in range(1, n + 1))
            fterms = " + ".join(
                f"({expr_lean(cert.c2 * x**2 + cert.c1 * x + cert.c0, (x,))})"
                for x in xs
            )
            a_lit = rat_lean(cert.a)
            sq_hints = ", ".join(f"sq_nonneg (x{i} - {a_lit})" for i in range(1, n + 1))
            lines.append(
                f"theorem {inst.lean_name} ({binders} : ℝ) "
                f"(hsum : {hsum_lhs} = {rat_lean(cert.S)}) :\n"
                f"    ({rat_lean(cert.B)} : ℝ) ≤ {fterms} := by\n"
                f"  nlinarith [{sq_hints}, hsum]\n"
            )
            ntheorems += 1
        return "".join(lines), ntheorems


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def tangent_sum_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a tangent-line-trick family (kind='tangent').

    ``spec``: a callable ``pt -> ((f, x), n, S)`` where ``f`` is a convex
    quadratic sympy expression in the symbol ``x``, ``n`` the number of terms
    (≥ 2), and ``S`` the value of the sum constraint ``Σxᵢ = S``.
    ``certify_tangent_point`` verifies convexity and the exact identity, refusing
    otherwise (no Lean for a non-member)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("tangent", spec),
        constants=dict(constants or {}),
    )
