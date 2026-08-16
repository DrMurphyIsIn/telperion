"""Exact sum-of-squares certificates for the rationalizable subset.

Extends the certifier's reach past Pólya forms to numerators that vanish at
interior points — the shape lifting provably cannot handle.  v1 covers the
exactly-computable cases (no numeric SDP, no float rationalization):

* even powers: ``num = base^(2m)`` — one square;
* quadratic-in-one-variable completion: ``a·x² + b·x + c`` with ``a > 0``
  becomes ``a(x + b/2a)² + (c − b²/4a)``, recursing on the ``x``-free
  residual.  Repeated over the variables this decides exactly the
  "iterated-Schur-complement without pivoting" class of quadratics — enough
  for the ``(u−1)²`` interior-tie shapes, honest refusal beyond.

The emitted Lean shape: ``hkey : body = (Σ cᵢ·(sᵢ)²) / den`` then
``positivity`` (squares times positive rationals over a positive-factored
denominator).  Trust model unchanged: a bad SOS just fails to compile.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class SOSCertificate:
    """num = Σ coeffs[i] · squares[i]² exactly (coeffs positive rationals)."""

    terms: tuple[tuple[sp.Rational, sp.Expr], ...]

    def as_expr(self) -> sp.Expr:
        return sp.Add(*[c * s**2 for c, s in self.terms])


def sos_decompose(num: sp.Expr, syms, _depth: int = 0) -> SOSCertificate | None:
    """Exact rational SOS of a polynomial, or None (a refusal, not a proof
    of non-SOS — the boundary of v1 is documented above)."""
    num = sp.expand(num)
    if num == 0:
        return SOSCertificate(terms=())
    if not syms or num.is_number:
        q = sp.Rational(num)
        return SOSCertificate(terms=((q, sp.Integer(1)),)) if q >= 0 else None
    if _depth > len(syms) + 2:
        return None
    # even power?
    fac = sp.factor(num)
    if isinstance(fac, sp.Pow) and fac.exp % 2 == 0:
        return SOSCertificate(terms=((sp.Integer(1), fac.base ** (fac.exp // 2)),))
    # quadratic completion in each variable in turn
    for x in syms:
        p = sp.Poly(num, x)
        if p.degree() == 2:
            a = p.coeff_monomial(x**2)
            b = p.coeff_monomial(x)
            c = num - a * x**2 - b * x
            if not (a.is_number and a > 0):
                continue
            square = x + b / (2 * a)
            # clear the rational so the square has polynomial entries
            residual = sp.expand(c - b**2 / (4 * a))
            rest = sos_decompose(residual, tuple(s for s in syms if s != x), _depth + 1)
            if rest is not None:
                return SOSCertificate(
                    terms=((sp.Rational(a), sp.together(square)),) + rest.terms
                )
    # all-nonneg-coefficient polynomials are trivially SOS-free but certifiable;
    # signal the caller to use the Polya path instead
    return None


def sos_certify(expr: sp.Expr, syms) -> tuple[SOSCertificate, sp.Expr] | None:
    """SOS certificate for 0 <= expr: (sos of the numerator, positive-factored
    denominator).  None if the numerator is outside the v1 SOS class or the
    denominator does not factor positively."""
    num, den = sp.fraction(sp.together(expr))
    num, den = sp.expand(num), sp.expand(den)
    if syms:
        pd = sp.Poly(den, *syms)
        if all(c < 0 for c in pd.coeffs()):
            num, den = sp.expand(-num), sp.expand(-den)
        const, factors = sp.factor_list(den)
        if const <= 0:
            return None
        for base, _ in factors:
            if not all(c > 0 for c in sp.Poly(base, *syms).coeffs()):
                return None
    cert = sos_decompose(num, tuple(syms))
    if cert is None:
        return None
    # exact self-check: the decomposition IS the numerator
    if sp.simplify(cert.as_expr() - num) != 0:
        return None
    return cert, den
