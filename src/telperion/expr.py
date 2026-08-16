"""Deterministic sympy -> Lean serialization.

The tool owns term ordering — it never trusts sympy's print order, so emitted
text is byte-stable across sympy versions (a hard requirement for the
freeze/diff protocol).  Monomials are sorted graded-lexicographically by the
family's symbol order; factor lists are sorted by (degree, string).
"""
from __future__ import annotations

from typing import Sequence

import sympy as sp


class SerializationError(ValueError):
    """An expression does not fit the certified serializable forms."""


def _monom_key(monom: tuple[int, ...]) -> tuple:
    return (sum(monom), tuple(-e for e in monom))


def poly_lean(p: sp.Poly, syms: Sequence[sp.Symbol]) -> str:
    """A polynomial with all-nonnegative INTEGER coefficients as Lean source.

    Raises SerializationError on any negative or non-integer coefficient —
    this is a self-check, not a formatting choice: only all-nonneg numerators
    are Polya-positivity-closable.
    """
    items = sorted(zip(p.monoms(), p.coeffs()), key=lambda t: _monom_key(t[0]))
    terms = []
    for monom, coeff in items:
        if coeff < 0 or sp.Integer(coeff) != coeff:
            raise SerializationError(
                f"non-Polya numerator coefficient {coeff} at monomial {monom}"
            )
        factors = []
        if int(coeff) != 1 or all(e == 0 for e in monom):
            factors.append(str(int(coeff)))
        for s, e in zip(syms, monom):
            if e == 1:
                factors.append(str(s))
            elif e > 1:
                factors.append(f"{s} ^ {e}")
        terms.append(" * ".join(factors))
    return " + ".join(terms)


def den_lean(den: sp.Expr, syms: Sequence[sp.Symbol]) -> str:
    """A factored positive denominator as Lean source.

    Requires: positive leading constant, and every factor a polynomial with
    all-positive coefficients (so `positivity` closes each factor).
    """
    const, factors = sp.factor_list(den)
    if const <= 0:
        raise SerializationError(f"denominator constant {const} not positive")
    parts = []
    if const != 1:
        parts = [str(int(const))] if sp.Integer(const) == const else [rat_lean(const)]
    for base, exp in sorted(
        factors, key=lambda t: (sp.total_degree(t[0]), sp.sstr(t[0]))
    ):
        pb = sp.Poly(base, *syms)
        if not all(c > 0 for c in pb.coeffs()):
            raise SerializationError(
                f"denominator factor {base} has non-positive coefficients"
            )
        parts.extend([f"({poly_positive_lean(pb, syms)})"] * int(exp))
    return " * ".join(parts) if parts else "1"


def poly_positive_lean(p: sp.Poly, syms: Sequence[sp.Symbol]) -> str:
    """Like poly_lean but for positive-coefficient factors (integers required)."""
    items = sorted(zip(p.monoms(), p.coeffs()), key=lambda t: _monom_key(t[0]))
    terms = []
    for monom, coeff in items:
        if coeff <= 0 or sp.Integer(coeff) != coeff:
            raise SerializationError(f"non-positive factor coefficient {coeff}")
        factors = []
        if int(coeff) != 1 or all(e == 0 for e in monom):
            factors.append(str(int(coeff)))
        for s, e in zip(syms, monom):
            if e == 1:
                factors.append(str(s))
            elif e > 1:
                factors.append(f"{s} ^ {e}")
        terms.append(" * ".join(factors))
    return " + ".join(terms)


def rat_lean(q) -> str:
    """A rational constant as Lean source: `7`, `(3 / 16)`, `(-(3 / 16))`."""
    q = sp.Rational(q)
    if q.q == 1:
        return str(q.p) if q.p >= 0 else f"(-{-q.p})"
    if q.p >= 0:
        return f"({q.p} / {q.q})"
    return f"(-({-q.p} / {q.q}))"


def expr_lean(e: sp.Expr, syms: Sequence[sp.Symbol]) -> str:
    """A general rational expression as Lean source, deterministically ordered.

    Renders as a quotient of deterministic polynomials when a denominator is
    present, else as the ordered polynomial.  Coefficients may be rational.
    """
    num, den = sp.fraction(sp.together(sp.expand(e)))
    num_s = _poly_any_lean(sp.expand(num), syms)
    if sp.simplify(den - 1) == 0:
        return num_s
    den_s = _poly_any_lean(sp.expand(den), syms)
    return f"({num_s}) / ({den_s})"


def _poly_any_lean(e: sp.Expr, syms: Sequence[sp.Symbol]) -> str:
    """Polynomial with arbitrary rational coefficients, ordered, as Lean source."""
    if not syms:
        return rat_lean(e)
    p = sp.Poly(e, *syms)
    items = sorted(zip(p.monoms(), p.coeffs()), key=lambda t: _monom_key(t[0]))
    pos_terms: list[str] = []
    neg_terms: list[str] = []
    for monom, coeff in items:
        c = sp.Rational(coeff)
        if c == 0:
            continue
        mag = abs(c)
        factors = []
        if mag != 1 or all(e_ == 0 for e_ in monom):
            factors.append(rat_lean(mag))
        for s, e_ in zip(syms, monom):
            if e_ == 1:
                factors.append(str(s))
            elif e_ > 1:
                factors.append(f"{s} ^ {e_}")
        term = " * ".join(factors)
        (pos_terms if c > 0 else neg_terms).append(term)
    if not pos_terms and not neg_terms:
        return "0"
    out = " + ".join(pos_terms) if pos_terms else "0"
    for t in neg_terms:
        out += f" - {t}"
    return out


def expr_lean_factored(e: sp.Expr, syms: Sequence[sp.Symbol]) -> str:
    """Like expr_lean, but the denominator is rendered in positive-FACTORED form
    (via den_lean).  This is the load-bearing spelling rule: `field_simp` matches
    `≠ 0` hypotheses syntactically, and the hypotheses are stated per factor —
    so every denominator the tactic sees must be spelled as that product.
    """
    num, den = sp.fraction(sp.together(sp.expand(e)))
    num_s = _poly_any_lean(sp.expand(num), syms)
    if sp.simplify(den - 1) == 0:
        return num_s
    return f"({num_s}) / ({den_lean(den, syms)})"


def expr_lean_raw(e: sp.Expr, syms: Sequence[sp.Symbol]) -> str:
    """Render the expression TREE as written — no together, no expand, no
    cancellation — for identity statements where the user's spelling IS the
    theorem.  Caveat: sympy evaluates at construction ((1+u)/(1+u) is already
    1 before any renderer runs); wrap with sp.UnevaluatedExpr or build with
    evaluate=False when construction-time simplification must be prevented."""

    def rec(e, prec=0):
        # prec: 0 add-level, 1 mul-level, 2 atom/pow-level
        if isinstance(e, sp.UnevaluatedExpr):
            return rec(e.args[0], prec)
        if e.is_Symbol:
            return str(e)
        if e.is_Rational:
            return rat_lean(e)
        if e.is_Add:
            inner = " + ".join(rec(a, 1) for a in e.args)
            return f"({inner})" if prec >= 1 else inner
        if e.is_Mul:
            num_parts, den_parts = [], []
            for a in e.args:
                if a.is_Pow and a.args[1].is_Integer and a.args[1] < 0:
                    den_parts.append(rec(a.args[0] ** (-a.args[1]), 2))
                elif a.is_Rational and a.q != 1 and a.p in (1, -1):
                    den_parts.append(str(a.q))
                    if a.p == -1:
                        num_parts.insert(0, "-1")
                else:
                    num_parts.append(rec(a, 2))
            num_s = " * ".join(num_parts) if num_parts else "1"
            if den_parts:
                den_s = " * ".join(den_parts)
                out = f"{num_s} / ({den_s})" if len(den_parts) > 1 else f"{num_s} / {den_s}"
                return f"({out})" if prec >= 2 else out
            return f"({num_s})" if prec >= 2 and len(num_parts) > 1 else num_s
        if e.is_Pow:
            base, exp = e.args
            if exp.is_Integer and exp > 0:
                return f"{rec(base, 2)} ^ {int(exp)}"
            if exp.is_Integer and exp < 0:
                return f"(1 / {rec(base ** (-exp), 2)})"
            raise SerializationError(f"non-integer exponent in raw render: {e}")
        raise SerializationError(f"unsupported node in raw render: {e.func}")

    return rec(e)


def canonical_srepr(e: sp.Expr) -> str:
    """Construction-canonical serialization for hashing.

    ``order="none"`` is load-bearing: srepr's DEFAULT term ordering calls
    ``as_terms`` -> ``__complex__`` -> ``evalf`` on every Add node —
    catastrophic on large exact-rational trees (the R7 hash stall: 972 cells
    x ~15 candidates projected to ~6 h in the default path).  Likewise no
    ``expand``/``together``: semantic canonicalization is deliberately NOT
    attempted — the input hash captures the *specified* construction (which
    is deterministic for a fixed family definition); emission drift is caught
    by the freeze/diff byte comparison, not the hash.  Hash values are
    tool-version-scoped; changing this function requires a version bump."""
    return sp.srepr(e, order="none")
