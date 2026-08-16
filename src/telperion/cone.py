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
class FarkasDual:
    """A PROOF that the target lies outside the cone: an exact rational
    functional y over the monomial-coefficient space with y·basisᵢ ≤ 0 for
    every basis element and y·target > 0.  verify() re-checks both, exactly —
    the refusal is a theorem, not a shrug (the campaign's 'the polytope
    accumulates' pattern: dead ends proven dead)."""

    y: tuple[sp.Rational, ...]
    monomials: tuple
    basis_values: tuple[sp.Rational, ...]   # y·basis_i  (all <= 0)
    target_value: sp.Rational               # y·target   (> 0)

    def verify(self) -> bool:
        return all(v <= 0 for v in self.basis_values) and self.target_value > 0

    def render(self) -> str:
        return (
            f"IMPOSSIBLE over this basis (Farkas dual): a functional y with "
            f"y·basisᵢ ≤ 0 (values {[str(v) for v in self.basis_values]}) and "
            f"y·target = {self.target_value} > 0 exists — no nonnegative "
            "combination can ever work; change the basis, not the search."
        )


@dataclass(frozen=True)
class ConeCombination:
    weights: tuple[sp.Rational, ...]
    basis: tuple[sp.Expr, ...]

    def as_expr(self) -> sp.Expr:
        return sp.Add(*[w * b for w, b in zip(self.weights, self.basis)])


def _coeff_matrix(exprs, syms):
    """Common monomial basis + exact coefficient vectors (over the common
    denominator of all expressions)."""
    denoms = [sp.fraction(sp.together(e))[1] for e in exprs]
    common = sp.Integer(1)
    for d in denoms:
        common = sp.lcm(common, d)
    polys = [sp.expand(sp.cancel(e * common)) for e in exprs]
    monoms = set()
    ps = []
    for p in polys:
        poly = sp.Poly(p, *syms) if syms else None
        ps.append(poly if syms else p)
        if syms:
            monoms.update(poly.monoms())
    monoms = sorted(monoms) if syms else [()]
    vecs = []
    for poly in ps:
        if syms:
            vecs.append([sp.Rational(poly.coeff_monomial(
                sp.prod([s**e for s, e in zip(syms, m)])) or 0) for m in monoms])
        else:
            vecs.append([sp.Rational(poly)])
    return monoms, vecs


def cone_decide(target: sp.Expr, basis, syms):
    """Decide cone membership: a ConeCombination (certificate of membership),
    a FarkasDual (certificate of IMPOSSIBILITY over this basis), or None
    (undecided — genuinely underdetermined systems need LP; named-open)."""
    cc = cone_combination(target, basis, syms)
    if cc is not None:
        return cc
    monoms, vecs = _coeff_matrix([target] + list(basis), syms)
    c = sp.Matrix(vecs[0])
    A = sp.Matrix([vecs[1 + i] for i in range(len(basis))]).T  # cols = basis
    # Case (a): equality system Aλ = c inconsistent — left-null functional
    for y in A.T.nullspace():
        val = (y.T * c)[0]
        if val != 0:
            yy = y if val > 0 else -y
            bvals = tuple(sp.Rational((yy.T * A[:, i])[0]) for i in range(A.cols))
            dual = FarkasDual(
                y=tuple(sp.Rational(v) for v in yy),
                monomials=tuple(monoms),
                basis_values=bvals,
                target_value=sp.Rational((yy.T * c)[0]),
            )
            if dual.verify():
                return dual
    # Case (b): a solution exists but forces a negative weight — extract it
    lam = sp.symbols(f"_lm0:{len(basis)}")
    sols = sp.solve((A * sp.Matrix(lam) - c), list(lam), dict=True)
    if sols:
        sol = sols[0]
        for j, l in enumerate(lam):
            w = sol.get(l)
            if w is not None and w.is_number and w < 0:
                # y with yᵀA = -e_j  =>  y·basis_i = -δ_ij ≤ 0, y·target = -λ_j > 0
                ysol = sp.solve(
                    (A.T * sp.Matrix(sp.symbols(f"_y0:{A.rows}"))
                     + sp.Matrix([1 if i == j else 0 for i in range(len(basis))])),
                    list(sp.symbols(f"_y0:{A.rows}")),
                    dict=True,
                )
                if ysol:
                    yv = sp.Matrix(
                        [ysol[0].get(sym, sp.Integer(0))
                         for sym in sp.symbols(f"_y0:{A.rows}")]
                    )
                    bvals = tuple(
                        sp.Rational((yv.T * A[:, i])[0]) for i in range(A.cols)
                    )
                    dual = FarkasDual(
                        y=tuple(sp.Rational(v) for v in yv),
                        monomials=tuple(monoms),
                        basis_values=bvals,
                        target_value=sp.Rational((yv.T * c)[0]),
                    )
                    if dual.verify():
                        return dual
    return None


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
