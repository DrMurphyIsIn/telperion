"""Unimodality certificates: the campaign's arithmetic endgame as a shape.

The near-star proof's integrality argument (the first rigorous family proof of
Φ ≤ 1): clear the root, form the successor ratio
``r(s) = f(s+1)/f(s)``, show the ratio CROSSES 1 EXACTLY ONCE (it is
monotone), pin the tie ``R(5) = 1`` exactly — and the maximum of ``f`` over
the integers falls out.  Every ingredient is a Telperion primitive; this
module composes them:

1. **log-concavity**: ``r(s) − r(s+1) ≥ 0`` for all real ``s ≥ s0`` — a
   symbolic-tail Polya claim (``s = s0 + t``, ``t ≥ 0``), so ``r`` is
   decreasing and crosses 1 at most once;
2. **crossing localization**: exact rational facts ``r(s*−1) ≥ 1`` and
   ``r(s*) ≤ 1`` (ExactFact-emittable);
3. **tie detection**: ``r(s*) = 1`` exactly means the maximum is attained at
   BOTH ``s*`` and ``s*+1`` — the origin's double tie, reported rather than
   glossed.

Conclusion (the induction, documented as a skeleton — the generic Lean lemma
is v2): ``max over integers s ≥ s0 of f(s)`` is at ``s*`` (and ``s*+1`` on a
tie).  This closes the loop the relaxation probe opens: the tool that says
"ARITHMETIC — use unimodality" now supplies the unimodality.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .certify import PolyaCertificate, polya_certify

UNIMODAL_SKELETON = """-- The integer-maximum induction (instantiate per your f : ℕ → ℝ; the emitted
-- pieces close each hypothesis):
--
-- theorem f_max (n : ℕ) (hn : s0 ≤ n) : f n ≤ f sstar := by
--   -- hdec : ∀ s ≥ s0, r (s+1) ≤ r s        («ratio_decreasing», tail claim)
--   -- hup  : 1 ≤ r (sstar - 1)              («cross_lo», exact fact)
--   -- hdn  : r sstar ≤ 1                    («cross_hi», exact fact)
--   -- climb below sstar with hup·hdec, descend above with hdn·hdec
--   «induction on n - s0 / sstar - n via Nat.le_induction»
"""


@dataclass(frozen=True)
class UnimodalityCertificate:
    s0: int
    s_star: int
    ratio: sp.Expr                     # r(s), symbolic in s
    decreasing_cert: PolyaCertificate  # r(s0+t) - r(s0+t+1) >= 0 over t >= 0
    cross_lo: sp.Rational              # r(s*-1)  (>= 1; only if s* > s0)
    cross_hi: sp.Rational              # r(s*)    (<= 1)
    exact_tie: bool                    # r(s*) == 1: max at BOTH s* and s*+1

    def render(self) -> str:
        tie = (
            f"EXACT TIE: r({self.s_star}) = 1 — the maximum is attained at "
            f"both s = {self.s_star} and s = {self.s_star + 1} (the R(5)=1 "
            "pattern; declare both as ties)"
            if self.exact_tie
            else f"strict crossing: r({self.s_star}) = {self.cross_hi} < 1"
        )
        return (
            f"UNIMODAL over integers s ≥ {self.s0}: ratio decreasing "
            f"(Polya-certified), crosses 1 at s* = {self.s_star} "
            f"(r({self.s_star - 1}) = {self.cross_lo} ≥ 1); maximum at s*.\n{tie}"
        )


def unimodal_certificate(
    ratio,
    s0: int,
    s_symbol: sp.Symbol | None = None,
    search_hi: int = 10_000,
    lift_max: int = 4,
) -> UnimodalityCertificate:
    """Certify that a positive sequence with successor ratio ``ratio(s)`` has
    its integer maximum at the ratio's crossing of 1.

    ratio: callable s_expr -> r(s) (a rational function), or a sympy expr in
    ``s_symbol``.  Raises ValueError when the ratio is not certifiably
    decreasing, or no crossing is found by ``search_hi`` (the sequence may be
    increasing forever — that is a different theorem)."""
    s = s_symbol or sp.Symbol("s", nonnegative=True)
    r = ratio(s) if callable(ratio) else ratio
    t = sp.Symbol("t", nonnegative=True)
    r_at = lambda k: sp.nsimplify(r.subs(s, sp.Integer(k)))

    # 1. decreasing: r(s0+t) - r(s0+t+1) >= 0 over t >= 0
    diff = sp.together(r.subs(s, s0 + t) - r.subs(s, s0 + t + 1))
    try:
        dec = polya_certify(diff, (t,), lift_max=lift_max)
    except ValueError as e:
        raise ValueError(
            f"ratio not certifiably decreasing on s >= {s0}: {e} — unimodality "
            "via monotone ratio does not apply (try a larger s0, or the claim "
            "is not log-concave)"
        ) from e

    # 2. locate the crossing exactly
    s_star = None
    for k in range(s0, search_hi + 1):
        if r_at(k) <= 1:
            s_star = k
            break
    if s_star is None:
        raise ValueError(
            f"no crossing of 1 found for s in [{s0}, {search_hi}] — the "
            "sequence is still increasing there (raise search_hi, or the "
            "maximum is at infinity)"
        )
    cross_hi = sp.Rational(r_at(s_star))
    cross_lo = sp.Rational(r_at(s_star - 1)) if s_star > s0 else sp.Integer(1)
    if s_star > s0 and cross_lo < 1:
        raise ValueError(
            f"inconsistent crossing: r({s_star - 1}) = {cross_lo} < 1 below "
            "the located crossing — decreasing certificate contradicted; "
            "check the ratio"
        )
    return UnimodalityCertificate(
        s0=s0,
        s_star=s_star,
        ratio=r,
        decreasing_cert=dec,
        cross_lo=cross_lo,
        cross_hi=cross_hi,
        exact_tie=(cross_hi == 1),
    )
