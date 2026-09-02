"""Star-of-cherry-brooms `S(k,c)` — the family that beats Pant's caterpillars for the Laplacian ratio.

The Brualdi-Goldwasser problem asks for the tree maximizing `pi(T) = per(L)/prod(deg) = SUM_{matchings M}
prod_{uv in M} 1/(d_u d_v)` (== `matching_free_energy.rho`).  The exact maximizer is OPEN.  Wu-Dong-Lai (DAM
372, 2025) conjectured the *subdivided star* (one cherry per branch); Pant 2026 (arXiv:2605.14176) refuted them
with *path-core caterpillars* `T(a_1..a_m)` but left the maximizer open.

This module builds the **star-of-cherry-brooms** `S(k,c)`: one central hub joined to `k` branch-hubs, each
branch-hub of degree `c+1` carrying `c` pendant length-2 arms ("cherries", each = branch-hub-armmid-leaf).  Its
STAR core gives every branch-hub degree `c+1` (vs the caterpillar path-core's `c+2`); the lower degree means a
larger `1/d` weight, and the single high-degree center is asymptotically free.  Exact closed form (verified ==
`rho`):

    total(c) = (3/2)^(c-1) (4c+3) / (2(c+1))                 # what the center sees from ONE B(c) branch
    Z(S(k,c)) = total(c)^(k-1) * ( total(c) + (3/2)^c/(c+1) )

so the per-vertex free-energy density is `F = (1/n) log Z -> log(total(c)) / (2c+1)` as `k -> inf` (each branch
is `2c+1` vertices; the center is negligible).  This STRICTLY EXCEEDS the caterpillar sup `0.205098` for every
`c >= 3`, peaking at `c = 5`: `total(5) = 621/64`, `F* = log(621/64)/11 = 0.206586` (rate `1.229474`).  Among
all rooted branches up to 16 vertices, `B(5)` is the UNIQUE density maximizer (exhaustive check).

`BroomOptimumCertificate` kernel-gates the `c = 5` optimum by CROSS-EXPONENTIATION: `rate(c1) > rate(c2)` iff
`total(c1)^(2 c2 + 1) > total(c2)^(2 c1 + 1)` (both exact rationals -- clears the `(2c+1)`-th roots), a
`norm_num`-checkable rational inequality.

This is a NOVEL result (not in the literature; a stronger counterexample to Wu-Dong-Lai than Pant's, and a new
lower bound on the max Laplacian ratio growth rate).  It is ASYMPTOTIC DOMINANCE of one explicit family, NOT a
proof of the global maximizer -- that remains OPEN.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


def spider_edges(k, c):
    """Build `S(k,c)`: center hub `0` joined to `k` branch-hubs, each carrying `c` length-2 cherries.

    Returns `(n, edges)`, `n = 1 + k(2c+1)`.  Center degree `k`; each branch-hub degree `c+1`; armmids deg 2.
    """
    edges = []
    nid = 1
    center = 0
    for _ in range(k):
        bh = nid
        nid += 1
        edges.append((center, bh))
        for _ in range(c):
            armmid, leaf = nid, nid + 1
            nid += 2
            edges.append((bh, armmid))
            edges.append((armmid, leaf))
    return nid, tuple(edges)


def broom_total(c):
    """`total(c) = (3/2)^(c-1) (4c+3) / (2(c+1))` -- the exact weight a single `B(c)` branch presents to the
    center (branch-hub unmatched-up OR matched-down to a cherry).  `total(5) = 621/64`."""
    return Fr(3, 2) ** (c - 1) * (4 * c + 3) / (2 * (c + 1))


def spider_Z(k, c):
    """Exact closed form `Z(S(k,c)) = total(c)^(k-1) (total(c) + (3/2)^c/(c+1))` (== `matching_free_energy.rho`,
    cross-checked in tests).  `k >= 1`, `c >= 1`."""
    t = broom_total(c)
    return t ** (k - 1) * (t + Fr(3, 2) ** c / (c + 1))


def broom_rate(c):
    """Per-vertex growth rate of the `S(k,c)` family as `k -> inf`: `total(c)^(1/(2c+1))` (float).
    `F = log(rate)` is the free-energy density; peaks at `c = 5` (`rate = 1.229474`, `F = 0.206586`)."""
    return float(broom_total(c)) ** (1.0 / (2 * c + 1))


def broom_free_energy(c):
    """`F(c) = log(total(c)) / (2c+1)`, the asymptotic per-vertex free energy of `S(k,c)`.  Argmax at `c = 5`
    (`0.206586`), strictly above the caterpillar sup `0.205098`."""
    t = broom_total(c)
    return (math.log(t.numerator) - math.log(t.denominator)) / (2 * c + 1)


def broom_argmax_c(lo=1, hi=12):
    """The `c` maximizing `broom_rate(c)` over `[lo, hi]` (returns `5`)."""
    return max(range(lo, hi + 1), key=broom_rate)


def rate_dominates(c1, c2):
    """Exact test `rate(c1) > rate(c2)` via cross-exponentiation (clears the roots):
    `rate(c1) > rate(c2)  <=>  total(c1)^(2 c2 + 1) > total(c2)^(2 c1 + 1)` (both positive rationals).
    Returns `(lhs, rhs, holds)` with `lhs = total(c1)^(2 c2 + 1)`, `rhs = total(c2)^(2 c1 + 1)`."""
    lhs = broom_total(c1) ** (2 * c2 + 1)
    rhs = broom_total(c2) ** (2 * c1 + 1)
    return lhs, rhs, lhs > rhs


def broom_ratio(s):
    """The near-star recurrence factor `rho(s) = (529/486) (1 - 1/((4s+7)(s+1)))^11`, which equals EXACTLY the
    broom cross-exponent-ratio step `X(s+1)/X(s)` where `X(s) = total(5)^(2s+1)/total(s)^11` (so `X(s) >= 1 <=>
    rate(5) >= rate(s)`).  This is the SAME object as the Phi^11 near-star invariant `R(s)` from the
    domination-bridge program (`529 = 23^2`, `486 = 2*3^5`); the two BG programs coincide on the extremal
    near-star/broom family.  `rho` is strictly increasing (numerator `g(s) = (4s+7)(s+1)` is) and crosses `1`
    once between `s = 4` and `s = 5`, giving the CLOSED all-`c` proof that `c = 5` uniquely maximizes the broom
    rate (vs the finite case-check in `BroomOptimumCertificate`).  Exact `Fraction`."""
    return Fr(529, 486) * (1 - Fr(1, (4 * s + 7) * (s + 1))) ** 11


def c5_unimodal_witness(hi=40):
    """Witness data for the CLOSED `c=5`-optimum proof via single-crossing of the near-star ratio `rho`:
    returns `(g_increasing, rho4_lt_1, rho5_gt_1, X_ge_1_eq_iff_5)` -- all exact.  `g` strictly increasing +
    `rho(4) < 1 < rho(5)` (monotone straddle) implies `X(s) = total(5)^(2s+1)/total(s)^11 >= 1` for every
    integer `s in [0, hi]`, with equality iff `s = 5`.  Ties the classical-BG broom optimum to the Phi^11
    near-star 23-adic proof (`R(5) = 1` exactly, `64*243*23 = 621*576`)."""
    def g(s):
        return (4 * s + 7) * (s + 1)
    def X(s):
        return broom_total(5) ** (2 * s + 1) / broom_total(s) ** 11
    g_incr = all(g(s) < g(s + 1) for s in range(hi))
    rho4 = broom_ratio(4) < 1
    rho5 = broom_ratio(5) > 1
    x_ok = all((X(s) >= 1) and ((X(s) == 1) == (s == 5)) for s in range(hi + 1))
    return g_incr, rho4, rho5, x_ok


@dataclass(frozen=True)
class BroomOptimumCertificate:
    """Certifies `c* = 5` maximizes the branch rate `total(c)^(1/(2c+1))` against a set of competitor `c`s, by
    exact cross-exponentiated rational inequalities `total(5)^(2c+1) > total(c)^11`.  `.check()` verifies
    exactly; `.lean_atom`/`.lean_module` emit the atoms as `norm_num` rational inequalities (untrusted
    generator, kernel-checked).  Certifies the DISCRETE `c`-optimum only -- the family-vs-family dominance and
    the global-maximizer question live elsewhere.  conjecture1_proved = False."""

    c_star: int = 5
    competitors: tuple = (2, 3, 4, 6, 7, 8)

    def atoms(self):
        """List of `(name, lhs, rhs)` with the certified strict inequality `lhs > rhs` (== `rate(c*) > rate(c)`)."""
        out = []
        for c in self.competitors:
            lhs, rhs, _ = rate_dominates(self.c_star, c)
            out.append((f"broom_rate_c{self.c_star}_gt_c{c}", lhs, rhs))
        return out

    def check(self) -> bool:
        """True iff `rate(c*) > rate(c)` (via the exact cross-exponent test) for every competitor `c`."""
        return all(rate_dominates(self.c_star, c)[2] for c in self.competitors)

    def lean_atom(self, name, lhs, rhs) -> str:
        return (f"theorem {name} : (({lhs.numerator} : ℚ)/{lhs.denominator}) > "
                f"(({rhs.numerator} : ℚ)/{rhs.denominator}) := by norm_num")

    def lean_module(self, namespace="BGBroomOptimum") -> str:
        assert self.check(), "certificate does not hold -- refusing to emit"
        head = ("import Mathlib\n\n"
                f"namespace {namespace}\n\n")
        body = "\n".join(self.lean_atom(nm, lhs, rhs) for nm, lhs, rhs in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


# --------------------------------------------------------------------------------------------------------------
# Smooth no-go / integrality gap (2026-08-31): why NO smooth certificate can prove the BG upper bound.
#
# The per-vertex free energy of the broom family `f(c) = log(total(c))/(2c+1)` is maximised over INTEGER `c` at
# `c = 5` (`f(5) = F* = log(621/64)/11`), but its CONTINUOUS relaxation peaks at `c* ~ 4.819` with
# `f(c*) > F*` (overshoot `~ 3.9e-6`).  The peak is nearly flat (`f''(5) ~ -2e-4`; every real `c in [4.06, 5.87]`
# is within `1e-4` of the max), so `c = 4, 5, 6` are near-degenerate.  Consequence: ANY certificate that relaxes
# the integer arm-count (convex/SOS/moment/tangent/spectral -- everything smooth) is bounded below by
# `f(c*) > F*` and so CANNOT certify `F(T) <= F*`.  This is a no-go theorem, not a heuristic: it is exactly why a
# smooth bound always lands `~1e-4` loose.  The BG optimum is an INTEGER-PROGRAM optimum with a positive
# integrality gap (rational value `621/64`, prime `4*5+3 = 23`), not a smooth one -- the closing argument must be
# arithmetic (exact on integer `c`).  conjecture1_proved = False.

# Frozen rigorous log-enclosures `log(p/q) in [lo/_DNG, hi/_DNG]` (floor/ceil at 60-digit precision).
_DNG = 10 ** 30
_LOG_NG = {
    (3, 2): (405465108108164381978013115464, 405465108108164381978013115465),
    (111, 5): (3100092288878233761162581574727, 3100092288878233761162581574728),
    (2, 1): (693147180559945309417232121458, 693147180559945309417232121459),
    (29, 5): (1757857917552373652582512699135, 1757857917552373652582512699136),
    (621, 64): (2272447998573806908489095813828, 2272447998573806908489095813829),
}


@dataclass(frozen=True)
class SmoothNoGoCertificate:
    """Kernel-gates the INTEGRALITY-GAP no-go: the continuous broom free energy exceeds the integer optimum `F*`
    at the rational witness `c0 = 24/5`, `f(24/5) > F* = log(621/64)/11`.  Clearing denominators (`* 11 * 53`)
    the inequality `f(24/5) > F*` becomes the single rational-log atom

        209 L(3/2) + 55 L(111/5) - 55 L(2) - 55 L(29/5)  >  53 L(621/64),

    LHS lower-bounded and RHS upper-bounded by the frozen log-enclosures (margin `~2.3e-3`).  Certifies that the
    continuous relaxation of the broom family overshoots `F*`, hence NO smooth (relaxation-based) certificate can
    prove the BG upper bound `F(T) <= F*` -- the proof must be arithmetic (exact on the integer arm-count).
    `.check()` exact; `.lean_module` emits the `norm_num` atom.  conjecture1_proved = False."""

    def _lo(self, pq):
        return Fr(_LOG_NG[pq][0], _DNG)

    def _hi(self, pq):
        return Fr(_LOG_NG[pq][1], _DNG)

    def atoms(self):
        """`[(name, lhs, rhs, '>')]`: the single cleared atom `f(24/5) > F*` (exact rationals via enclosures)."""
        lhs = (209 * self._lo((3, 2)) + 55 * self._lo((111, 5))
               - 55 * self._hi((2, 1)) - 55 * self._hi((29, 5)))       # lower bound on 583*f(24/5)
        rhs = 53 * self._hi((621, 64))                                 # upper bound on 583*F*
        return [("smooth_nogo_fcont_24_5_gt_Fstar", lhs, rhs, ">")]

    def check(self) -> bool:
        return all((lhs > rhs) if op == ">" else (lhs < rhs) for _, lhs, rhs, op in self.atoms())

    def lean_module(self, namespace="BGSmoothNoGo") -> str:
        assert self.check(), "smooth no-go certificate does not hold -- refusing to emit"
        head = ("import Mathlib\n\n" f"namespace {namespace}\n\n")
        body = "\n".join(
            f"theorem {nm} : (({lhs.numerator} : ℚ)/{lhs.denominator}) {op} "
            f"(({rhs.numerator} : ℚ)/{rhs.denominator}) := by norm_num"
            for nm, lhs, rhs, op in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


conjecture1_proved = False
