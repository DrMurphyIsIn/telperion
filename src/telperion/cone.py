"""Exact cone membership: express a target in the nonnegative span of a basis.

The origin campaign searched for potential certificates by LP cutting-planes
over finite bases.  This is that maneuver's exactly-solvable core: given a
target polynomial/rational function and a basis of known-nonnegative
expressions, find rational λᵢ ≥ 0 with

    target ≡ Σ λᵢ · basisᵢ      (exact identity),

by matching monomial coefficients — an exact rational linear system.  A found
combination IS a certificate (each basis element nonneg, weights nonneg);
refusal is honest (the determined/overdetermined case is decided exactly; a
genuinely underdetermined cone-membership needs LP and is a named-open —
float-guided-then-exact-verified — extension).
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class ConeCombination:
    weights: tuple[sp.Rational, ...]
    basis: tuple[sp.Expr, ...]

    def as_expr(self) -> sp.Expr:
        return sp.Add(*[w * b for w, b in zip(self.weights, self.basis)])


def cone_combination(
    target: sp.Expr, basis, syms
) -> ConeCombination | None:
    """Solve target = Σ λ b exactly with λ ≥ 0, or refuse (None).

    Rational functions allowed: everything is put over the common denominator
    first; the matching then happens on numerator polynomials."""
    basis = list(basis)
    lam = sp.symbols(f"_lam0:{len(basis)}", nonnegative=True)
    combo = sp.Add(*[l * b for l, b in zip(lam, basis)])
    diff = sp.together(target - combo)
    num, _ = sp.fraction(diff)
    poly = sp.Poly(sp.expand(num), *syms) if syms else sp.Poly(sp.expand(num), *lam)
    # coefficients of each monomial in syms are LINEAR in lam — collect equations
    eqs = []
    if syms:
        for coeff in poly.coeffs():
            eqs.append(sp.expand(coeff))
    else:
        eqs.append(sp.expand(num))
    sol = sp.solve(eqs, list(lam), dict=True)
    if not sol:
        return None
    s = sol[0]
    weights = []
    for l in lam:
        w = s.get(l, sp.Integer(0))
        if not w.is_number or w < 0:
            return None   # negative or still-free weight: outside the (decided) cone
        weights.append(sp.Rational(w))
    cc = ConeCombination(weights=tuple(weights), basis=tuple(basis))
    # exact self-check
    if sp.simplify(sp.together(target - cc.as_expr())) != 0:
        return None
    return cc
