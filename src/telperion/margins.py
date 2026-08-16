"""Tie-variety extraction and margin reports: WHERE is the family tight?

For a mathematician the equality cases are the theorem — the extremal
structure lives exactly where the inequality degenerates.  This module answers
"where is this family tight, and by how much elsewhere?" exactly.

The certified/refused dichotomy does the heavy lifting:

* A CERTIFIED instance has an all-nonnegative-coefficient numerator, so on the
  closed orthant ``num = 0`` iff every monomial vanishes — the tie variety is
  a finite union of coordinate faces ``{x_i = 0 : i in H}`` over the MINIMAL
  HITTING SETS ``H`` of the monomial supports.  Purely combinatorial, exact.
  Corollary: certified instances have NO interior ties (an interior zero of a
  nonneg-coefficient polynomial forces it to vanish identically) — which is
  precisely why interior-tie claims (the campaign's Φ = 1 tie variety) admit
  no Polya certificate and need the arithmetic treatment.

* A refused-but-true claim gets exact root extraction instead: univariate
  numerators via ``real_roots`` (exact algebraic numbers, filtered to the
  orthant), multivariate via ``solve`` where sympy can.

Margins are exact rationals: the numerator's constant term is a global orthant
floor for ``num``; the empirical minimum is an exact evaluation over a
deterministic dyadic + seeded-random sample (a bound witness, not a proof of
the minimum).
"""
from __future__ import annotations

import random
from dataclasses import dataclass
from itertools import combinations

import sympy as sp

from .certify import CertifiedFamily


# ---------------------------------------------------------------- tie variety
def tie_faces(num: sp.Expr, syms) -> list[tuple[sp.Symbol, ...]]:
    """The exact tie variety of an all-nonneg-coefficient numerator on the
    orthant, as minimal coordinate faces (each face = set of symbols forced
    to 0).  Empty list means NO ties (positive constant term).  Raises
    ValueError on numerators with negative coefficients — use tie_points."""
    p = sp.Poly(sp.expand(num), *syms)
    if any(c < 0 for c in p.coeffs()):
        raise ValueError("tie_faces requires an all-nonneg-coefficient numerator")
    supports = []
    for monom, coeff in zip(p.monoms(), p.coeffs()):
        if coeff == 0:
            continue
        supp = frozenset(i for i, e in enumerate(monom) if e > 0)
        if not supp:
            return []  # positive constant term: num >= c0 > 0 on the orthant
        supports.append(supp)
    if not supports:
        return [()]  # num is identically zero: ties everywhere
    # minimal hitting sets of the supports (n is small in practice)
    n = len(syms)
    hitting: list[frozenset[int]] = []
    for size in range(1, n + 1):
        for combo in combinations(range(n), size):
            cs = frozenset(combo)
            if any(h <= cs for h in hitting):
                continue
            if all(cs & s for s in supports):
                hitting.append(cs)
    return [tuple(syms[i] for i in sorted(h)) for h in hitting]


def tie_points(num: sp.Expr, syms) -> list[dict]:
    """Exact zeros of a (possibly mixed-sign) numerator on the closed orthant.

    Univariate: exact real roots filtered to >= 0.  Multivariate: sympy solve
    where it succeeds (may be incomplete — a returned list is exact, an empty
    list is not a proof of no ties)."""
    num = sp.expand(num)
    if len(syms) == 1:
        s = syms[0]
        out, seen = [], set()
        for root in sp.Poly(num, s).real_roots():
            if root >= 0 and root not in seen:
                seen.add(root)
                out.append({str(s): sp.nsimplify(root)})
        return out
    try:
        sols = sp.solve(sp.Eq(num, 0), list(syms), dict=True)
    except (NotImplementedError, TypeError):
        return []
    out = []
    for sol in sols:
        if all(v.is_number and v >= 0 for v in sol.values()):
            out.append({str(k): v for k, v in sol.items()})
    return out


# -------------------------------------------------------------------- margins
@dataclass(frozen=True)
class MarginReport:
    lean_name: str
    point: dict
    corner: str | None            # bilinear corner index "00".."11", or None
    constant_term: sp.Rational    # orthant floor of the certificate numerator
    ties: tuple                   # tie faces (certified) — () means strict
    empirical_min: sp.Rational    # exact min of expr over the sample set
    argmin: dict                  # where the empirical min was attained
    lift_n: int = 0

    @property
    def is_tight(self) -> bool:
        return bool(self.ties) or self.constant_term == 0

    def render(self) -> str:
        loc = f"{self.lean_name}" + (f" corner {self.corner}" if self.corner else "")
        if self.ties:
            faces = "; ".join(
                "{" + ", ".join(f"{s} = 0" for s in face) + "}" for face in self.ties
            )
            tie_s = f"TIES on {faces}"
        else:
            tie_s = f"strict (num >= {self.constant_term})"
        return (
            f"{loc}: {tie_s}; sample min {self.empirical_min} at "
            + ", ".join(f"{k}={v}" for k, v in self.argmin.items())
        )


def _sample_points(syms, samples: int, seed: int = 0):
    rng = random.Random(seed)
    dyadics = [sp.Integer(0), sp.Rational(1, 4), sp.Integer(1), sp.Integer(4)]
    pts = []
    # small deterministic grid first (includes the all-zero corner)
    def grid(i, acc):
        if i == len(syms):
            pts.append(dict(acc))
            return
        for d in dyadics:
            acc[syms[i]] = d
            grid(i + 1, acc)
        acc.pop(syms[i], None)

    grid(0, {})
    for _ in range(samples):
        pts.append(
            {s: sp.Rational(rng.randint(0, 160), rng.randint(1, 16)) for s in syms}
        )
    return pts


def _empirical_min(expr: sp.Expr, syms, samples: int, seed: int = 0):
    best, arg = None, None
    for sub in _sample_points(syms, samples, seed):
        val = expr.subs(sub)
        if val.is_number and (best is None or val < best):
            best, arg = val, sub
    return best, {str(k): v for k, v in (arg or {}).items()}


def margin_report(
    cf: CertifiedFamily, samples: int = 60, seed: int = 0
) -> list[MarginReport]:
    """Per-instance (per-corner, for bilinear) tightness analysis, sorted with
    the tight/marginal entries first."""
    syms = cf.family.symbols
    reports: list[MarginReport] = []
    for inst in cf.instances:
        corner_labels = (
            [None] if inst.decomposition is None else ["00", "01", "10", "11"]
        )
        for cert, label in zip(inst.corners, corner_labels):
            p = sp.Poly(sp.expand(cert.numerator), *syms) if syms else None
            c0 = (
                sp.Rational(p.coeff_monomial(1)) if p is not None
                else sp.Rational(cert.numerator)
            )
            ties = tuple(tie_faces(cert.numerator, syms)) if syms else ()
            emin, argmin = _empirical_min(cert.expr, syms, samples, seed)
            reports.append(
                MarginReport(
                    lean_name=inst.lean_name,
                    point=inst.point,
                    corner=label,
                    constant_term=c0,
                    ties=ties,
                    empirical_min=emin,
                    argmin=argmin,
                    lift_n=cert.lift_n,
                )
            )
    reports.sort(key=lambda r: (not r.is_tight, r.empirical_min))
    return reports
