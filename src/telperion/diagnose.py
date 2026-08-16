"""Diagnosis: when certification refuses, say WHY and WHAT TO DO.

A refusal has exactly three possible causes, and confusing them wastes days
(the origin campaign's log is full of hours spent on each):

1. **The inequality is FALSE** — there is a rational counterexample.  No
   certificate shape will ever work; the family design (box, corners, claim)
   is wrong.  `find_counterexample` hunts for an exact witness.
2. **True but not Polya in this spelling** — the numerator has negative
   coefficients that a different decomposition might remove.  The remedy
   hints check the cheap transformations (positive factorization, box
   subdivision) and name the offending monomials.
3. **True and certifiable, tool misuse** — e.g. symbols missing
   `nonnegative=True`, wrong box axes.  The diagnosis reports what it sees.

Everything is exact rational arithmetic; a reported counterexample is a
theorem (the claim is false), never a float artifact.
"""
from __future__ import annotations

import random
from dataclasses import dataclass, field
from fractions import Fraction as Fr

import sympy as sp

from .certify import polya_certify
from .family import InequalityFamily


@dataclass(frozen=True)
class Diagnosis:
    verdict: str          # "CERTIFIABLE" | "FALSE" | "NOT_POLYA_IN_THIS_FORM"
    detail: str
    counterexample: dict | None = None
    hints: tuple[str, ...] = ()

    def render(self) -> str:
        out = [f"{self.verdict}: {self.detail}"]
        if self.counterexample:
            wit = ", ".join(f"{k} = {v}" for k, v in self.counterexample.items())
            out.append(f"  witness: {wit}")
        out.extend(f"  hint: {h}" for h in self.hints)
        return "\n".join(out)


def _rand_rational(rng: random.Random, span: int = 40, den: int = 8) -> sp.Rational:
    return sp.Rational(rng.randint(0, span * den), den)


def find_counterexample(
    expr: sp.Expr,
    syms,
    trials: int = 400,
    seed: int = 0,
) -> dict | None:
    """Exact-rational search for a point with expr < 0 (symbols >= 0).

    Mixes uniform draws with boundary-biased draws (zeros and small values —
    where sign changes hide).  Returns the witness substitution or None.
    None does NOT prove truth; a witness DOES prove falsity."""
    rng = random.Random(seed)
    special = [sp.Integer(0), sp.Rational(1, 8), sp.Rational(1, 2), sp.Integer(1)]
    for t in range(trials):
        sub = {}
        for s in syms:
            if t % 3 == 0:
                sub[s] = special[rng.randrange(len(special))]
            else:
                sub[s] = _rand_rational(rng)
        val = expr.subs(sub)
        if val.is_number and val < 0:
            return {str(k): v for k, v in sub.items()}
    return None


def _remedy_hints(expr: sp.Expr, syms, num: sp.Expr) -> tuple[str, ...]:
    from .lift import polya_lift

    hints: list[str] = []
    lifted = polya_lift(sp.expand(sp.fraction(sp.together(expr))[0]), syms, 8)
    if lifted is not None and lifted[0] > 0:
        hints.append(
            f"certifiable via Pólya lift N={lifted[0]} — set auto_lift={lifted[0]} "
            "on the family (or pass lift_max to polya_certify)"
        )
    elif lifted is None:
        hints.append(
            "Pólya lifting does not converge by N=8 — the claim likely touches an "
            "equality case (a tie); lifting certifies strict positivity only. "
            "Subdivide to isolate the tie region (auto_subdivide / force_subdivide)"
        )
    pn = sp.Poly(sp.expand(num), *syms)
    bad = [(m, c) for m, c in zip(pn.monoms(), pn.coeffs()) if c < 0]
    if bad:
        mono = ", ".join(
            "*".join(f"{s}^{e}" if e > 1 else str(s) for s, e in zip(syms, m) if e)
            or "1"
            for m, _ in bad[:4]
        )
        hints.append(
            f"{len(bad)} negative numerator coefficient(s), at monomial(s): {mono}"
        )
    # cheap transformation 1: positive factorization (product of positive-coeff
    # factors IS positivity-closable if rendered factored)
    try:
        const, factors = sp.factor_list(sp.expand(num))
        if factors and all(
            all(c > 0 for c in sp.Poly(b, *syms).coeffs()) for b, _ in factors
        ):
            if const > 0:
                hints.append(
                    "numerator FACTORS into all-positive-coefficient factors — "
                    "certifiable if spelled factored; consider a custom skeleton "
                    "or refactor the family so together() keeps the product"
                )
            else:
                hints.append(
                    "numerator factors positively but with a NEGATIVE constant — "
                    "the claim direction may be flipped"
                )
    except sp.PolynomialError:
        pass
    # cheap transformation 2: is it a perfect square times something positive?
    sq = sp.factor(sp.expand(num))
    if isinstance(sq, sp.Pow) and sq.exp % 2 == 0:
        hints.append("numerator is an even power — certifiable via a squared spelling")
    if not hints:
        hints.append(
            "no negative numerator coefficients found — check symbol assumptions "
            "(nonnegative=True) and the denominator's factor signs"
        )
    hints.append(
        "if the claim lives on a box: tightening/subdividing the box moves the "
        "corners — a corner failing here can pass on a half-box (bisect the axis)"
    )
    return tuple(hints)


def diagnose_expr(expr: sp.Expr, syms, trials: int = 400) -> Diagnosis:
    """The full triage for a single 0 <= expr claim."""
    try:
        cert = polya_certify(expr, syms)
        return Diagnosis(
            "CERTIFIABLE",
            f"0 <= ({cert.numerator}) / ({cert.denominator})",
        )
    except ValueError as refusal:
        wit = find_counterexample(expr, syms, trials=trials)
        if wit is not None:
            return Diagnosis(
                "FALSE",
                "the claim itself is false — no certificate shape can work",
                counterexample=wit,
            )
        num, _ = sp.fraction(sp.together(expr))
        return Diagnosis(
            "NOT_POLYA_IN_THIS_FORM",
            str(refusal),
            hints=_remedy_hints(expr, syms, num),
        )


def diagnose_family(family: InequalityFamily, trials: int = 200) -> list[tuple[dict, Diagnosis]]:
    """Diagnose every failing instance of a family (passing instances skipped).

    For bilinear families each corner is diagnosed independently; the corner
    index is included in the reported point."""
    results: list[tuple[dict, Diagnosis]] = []
    for pt in family.grid.points():
        if family.kind == "direct":
            d = diagnose_expr(family.target(pt), family.symbols, trials)
            if d.verdict != "CERTIFIABLE":
                results.append((dict(pt), d))
        else:
            qa, ra = family.box(pt)
            q, r = qa.symbol, ra.symbol
            diff = sp.expand(sp.together(family.after(pt) - family.before(pt)))
            try:
                pdiff = sp.Poly(diff, q, r)
                c1 = pdiff.coeff_monomial(1)
                c2 = pdiff.coeff_monomial(q)
                c3 = pdiff.coeff_monomial(r)
                c4 = pdiff.coeff_monomial(q * r)
            except sp.PolynomialError as e:
                results.append((dict(pt), Diagnosis("NOT_POLYA_IN_THIS_FORM", str(e))))
                continue
            for qi, qv in enumerate((qa.lo, qa.hi)):
                for ri, rv in enumerate((ra.lo, ra.hi)):
                    corner = c1 + c2 * qv + c3 * rv + c4 * qv * rv
                    d = diagnose_expr(corner, family.symbols, trials)
                    if d.verdict != "CERTIFIABLE":
                        ptc = dict(pt)
                        ptc["corner"] = f"{qi}{ri}"
                        results.append((ptc, d))
    return results
