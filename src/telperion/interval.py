"""Interval symbols: bracket-quantified claims, lowered onto the box machinery.

The origin campaign's G1 floor layer — the largest certificate stratum not yet
kernel-checked — proves claims involving the transcendental ρ_B by working
with rational BRACKETS: every floor certificate is really

    ∀ ρ ∈ [lo, hi] :   rational-claim(ρ, u, ...),

with the claim LINEAR in each bracketed constant (slack_lower is linear in
L_LO, G_HI, T0 separately).  A multilinear claim on a product of intervals is
nonnegative iff it is nonnegative at the corners — which is EXACTLY the
bilinear-box certificate the tool already emits, with the bracket's lower end
as a floor hypothesis.  So interval symbols are a transformer, not a new
emitter: `interval_family` lowers the bracket-quantified claim onto the
existing machinery, and the emitted `_cell` theorem IS the quantified interval
statement (hypotheses `lo ≤ ρ`, `ρ ≤ hi`).

Composes with the ExactFact emitter: the bracket facts themselves
((1+t_lo)^11 ≤ 621/64 etc.) are emittable kernel facts, so a claim chain
"transcendental constant ∈ bracket" + "claim on the bracket" becomes fully
kernel-checked end to end.

v1: one or two interval symbols (k=1 uses a dummy second axis), claims of
degree ≤ 1 in each interval symbol (checked at certification — the bilinear
guard refuses higher degree), direct-family targets.
"""
from __future__ import annotations

import sympy as sp

from .family import BoxAxis, InequalityFamily


def interval_family(
    name: str,
    symbols,
    grid,
    lean_name,
    target,
    brackets: dict,
    **kwargs,
) -> InequalityFamily:
    """Lower `∀ ρᵢ ∈ [loᵢ, hiᵢ]: 0 ≤ target(pt)` (target multilinear in the
    ρᵢ) onto the bilinear-box machinery.

    symbols: the ordinary nonnegative symbols (NOT the interval ones).
    brackets: {interval_symbol: (lo, hi)} with rational lo < hi — one or two.
    target(pt): expression in symbols + interval symbols.
    """
    items = list(brackets.items())
    if not 1 <= len(items) <= 2:
        raise ValueError("v1 supports one or two interval symbols")
    for rho, (lo, hi) in items:
        if not (sp.Rational(lo) < sp.Rational(hi)):
            raise ValueError(f"bracket for {rho} must have lo < hi")
    if len(items) == 1:
        # dummy second axis: a fresh symbol on [0, 1] the target ignores
        dummy = sp.Symbol(f"_iv_dummy_{name}", nonnegative=True)
        items.append((dummy, (sp.Integer(0), sp.Integer(1))))
    (rho1, (lo1, hi1)), (rho2, (lo2, hi2)) = items

    def box(pt):
        return (
            BoxAxis(rho1, sp.Rational(lo1), sp.Rational(hi1),
                    lo_is_floor=sp.Rational(lo1) != 0),
            BoxAxis(rho2, sp.Rational(lo2), sp.Rational(hi2),
                    lo_is_floor=sp.Rational(lo2) != 0),
        )

    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        before=lambda pt: sp.Integer(0),
        after=lambda pt: target(pt),
        box=box,
        **kwargs,
    )
