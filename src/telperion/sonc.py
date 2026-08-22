"""SONC — nonnegative circuit polynomial certificates, exact rationalized AM-GM.

A *circuit polynomial* is

    p(x) = Σⱼ cⱼ x^{α(j)}  +  c_β x^β

where the exponent vectors α(0),…,α(k) are the vertices of a simplex with EVEN
coordinates and positive coefficients cⱼ > 0 (so each cⱼ x^{α(j)} ≥ 0), and β
lies in the relative interior of that simplex: β = Σⱼ λⱼ α(j) with λⱼ > 0,
Σλⱼ = 1 (barycentric, rational).

Iliman–de Wolff (2016): p is nonnegative iff |c_β| ≤ Θ, the *circuit number*
Θ = Πⱼ (cⱼ/λⱼ)^{λⱼ} (β having an odd coordinate; the even-β one-sided case is
c_β ≥ −Θ).  Θ is generally irrational, but λⱼ = pⱼ/q is rational, so raising to
the q-th power clears the fractional exponents and yields the EXACT rational
condition

    |c_β|^q ≤ Πⱼ (cⱼ/λⱼ)^{pⱼ}        (pⱼ = q·λⱼ ∈ ℤ).

That inequality is the kernel-checkable certificate (a `norm_num`/`decide`
rational comparison).  This module is the untrusted generator:
`find_circuit_certificate` detects the circuit, solves the exact barycentric λ,
and rationalizes; `verify_circuit_certificate` re-checks everything in exact
rationals.  SONC reaches sparse nonneg-not-SOS polynomials (e.g. Motzkin, a
tight single circuit) that the SOS/Pólya rungs miss or blow up on.

Scope: this v1 handles a SINGLE circuit polynomial (one interior term over an
even-vertex simplex).  A general SONC *decomposition* finder (sum of circuits via
an LP over the Newton polytope) is future work.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import gcd

import sympy as sp


@dataclass(frozen=True)
class SONCCertificate:
    """Exact rationalized AM-GM witness that a circuit polynomial is nonnegative."""

    poly: sp.Expr
    symbols: tuple
    vertices: tuple            # exponent tuples α(j) (even, positive coeff)
    interior: tuple            # exponent tuple β
    coeffs: tuple              # (c_0,…,c_k) for the vertices
    lambdas: tuple             # barycentric λⱼ (Rational)
    q: int                     # common denominator of the λⱼ
    lhs_pow: sp.Rational       # |c_β|^q
    rhs_pow: sp.Rational       # Πⱼ (cⱼ/λⱼ)^{q λⱼ}


def _monomial_terms(poly: sp.Expr, syms: tuple):
    """Return {exponent tuple: rational coeff} for an expanded polynomial."""
    p = sp.Poly(sp.expand(poly), *syms)
    return {tuple(mono): sp.Rational(coeff) for mono, coeff in p.terms()}


def find_circuit_certificate(poly: sp.Expr, symbols) -> SONCCertificate | None:
    """Detect a single circuit polynomial and certify nonnegativity exactly.

    Returns None if `poly` is not a circuit polynomial in the required form, or
    if the exact AM-GM condition fails (the circuit is not nonnegative).
    """
    syms = tuple(symbols)
    terms = _monomial_terms(poly, syms)
    if not terms:
        return None

    # vertices: even-exponent monomials with positive coefficient (monomial squares)
    vertices, interiors = [], []
    for exp, c in terms.items():
        even = all(e % 2 == 0 for e in exp)
        if even and c > 0:
            vertices.append(exp)
        else:
            interiors.append((exp, c))

    # exactly one interior (negative / odd-support) term for a single circuit
    if len(interiors) != 1 or len(vertices) < 2:
        return None
    beta, c_beta = interiors[0]

    # barycentric coords: solve β = Σ λⱼ α(j), Σ λⱼ = 1, λⱼ ≥ 0
    k = len(vertices)
    lam = sp.symbols(f"l0:{k}")
    eqs = [sp.Eq(sum(lam[j] * vertices[j][d] for j in range(k)), beta[d])
           for d in range(len(syms))]
    eqs.append(sp.Eq(sum(lam), 1))
    sol = sp.solve(eqs, lam, dict=True)
    if not sol:
        return None
    sol = sol[0]
    lambdas = []
    for j in range(k):
        v = sol.get(lam[j], None)
        if v is None or not v.is_rational or v <= 0:
            return None  # β not strictly interior ⇒ not a circuit
        lambdas.append(sp.Rational(v))
    if sum(lambdas) != 1:
        return None

    coeffs = tuple(terms[v] for v in vertices)

    # rationalize: q = lcm of λ denominators; pⱼ = q λⱼ ∈ ℤ
    q = 1
    for lj in lambdas:
        q = q * lj.q // gcd(q, lj.q)
    ps = [int(q * lj) for lj in lambdas]

    lhs_pow = abs(c_beta) ** q
    rhs_pow = sp.Integer(1)
    for cj, lj, pj in zip(coeffs, lambdas, ps):
        rhs_pow *= (cj / lj) ** pj
    lhs_pow, rhs_pow = sp.Rational(lhs_pow), sp.Rational(rhs_pow)

    if lhs_pow > rhs_pow:
        return None  # |c_β|^q > Θ^q ⇒ circuit is NOT nonnegative

    return SONCCertificate(
        poly=sp.expand(poly), symbols=syms, vertices=tuple(vertices),
        interior=beta, coeffs=coeffs, lambdas=tuple(lambdas), q=q,
        lhs_pow=lhs_pow, rhs_pow=rhs_pow,
    )


def verify_circuit_certificate(cert: SONCCertificate) -> bool:
    """Independently re-check the circuit structure and exact AM-GM inequality."""
    syms = cert.symbols
    terms = _monomial_terms(cert.poly, syms)

    # 1. vertices: even exponents, positive coeff matching the certificate
    for v, c in zip(cert.vertices, cert.coeffs):
        if not all(e % 2 == 0 for e in v):
            return False
        if terms.get(v) != c or c <= 0:
            return False

    # 2. barycentric identity β = Σ λⱼ α(j), Σ λⱼ = 1, λⱼ > 0 (exact)
    if sum(cert.lambdas) != 1:
        return False
    if any(lj <= 0 for lj in cert.lambdas):
        return False
    k = len(cert.vertices)
    for d in range(len(syms)):
        if sum(cert.lambdas[j] * cert.vertices[j][d] for j in range(k)) != cert.interior[d]:
            return False

    # 3. rationalization q λⱼ ∈ ℤ and the exact powers reconstruct
    ps = [cert.q * lj for lj in cert.lambdas]
    if any(pj != int(pj) for pj in ps):
        return False
    c_beta = terms.get(cert.interior)
    if c_beta is None:
        return False
    if abs(c_beta) ** cert.q != cert.lhs_pow:
        return False
    rhs = sp.Integer(1)
    for cj, lj, pj in zip(cert.coeffs, cert.lambdas, ps):
        rhs *= (cj / lj) ** int(pj)
    if sp.Rational(rhs) != cert.rhs_pow:
        return False

    # 4. the load-bearing inequality (coerce sympy relational to a Python bool)
    return bool(cert.lhs_pow <= cert.rhs_pow)
