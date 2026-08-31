"""Exact spine-transfer recurrence for the length-2-arm caterpillar `T(a_1,..,a_m)`.

The Brualdi-Goldwasser maximizer over trees is the length-2-arm caterpillar: a spine of
`m` hubs (a path `0-1-...-(m-1)`), where hub `i` carries `a_i` pendant length-2 arms (each
arm = hub-armmid-leaf).  Its monomer-dimer partition function

    Z(T) = per(L)/prod(deg) = SUM_{matchings M} prod_{v matched} (1/d_v)

(`matching_free_energy.rho`) collapses to a **linear tridiagonal / transfer recurrence** along
the spine, because every length-2 arm contributes the SAME two exact local weights: an arm
subtree rooted at its armmid (deg 2) has `unm = 1` and `mat = 1/2`, so its total is `3/2` and
its matched-through weight uses `unm = 1`.  Sweeping the cavity DP hub-by-hub therefore updates
a 2-vector `(U_i, M_i) = (unm, mat)` of the partial subtree by a per-hub linear map.

Pant 2026 (arXiv:2605.14176) writes this as `Z = (3/2)^{sum a_i} * f_m` with a two-term
recurrence.  We DERIVED and cross-checked the exact coefficients against `rho` on the full
caterpillar family (single-hub, both endpoints, interior, zero-arm hubs, and random lists):
`Z_recurrence(arms) == rho(*caterpillar_edges(arms))` as exact `Fraction`.  The clean two-term
Pant form matches for `m >= 2` but its stated single-hub base case is a boundary artifact (the
lone hub has NO spine neighbour, so `d_0 = a_0`, not `a_0 + 1`); the primitive `(U, M)` spine
sweep here handles every `m >= 1` uniformly and is the certified path.

For the UNIFORM caterpillar (all hubs = `a` arms, interior degree `d = a + 2`) the per-hub map
is a fixed 2x2 exact rational matrix whose Perron eigenvalue `lam(a)` is the per-hub growth
rate; the per-vertex matching free energy is `F(a) = log(lam(a)) / (2a + 1)`.  `F(a)` has an
interior maximum at `a = 7` (`F(7) = logrho* ~ 0.205098`), the analytic signature of why
length-2 legs uniquely maximize the matching entropy density (`rho^(1/V) -> sqrt(3/2)`).

`TransferCaterpillarCertificate.check()` re-verifies `Z_recurrence == rho` exactly over a family
of arms.  This is a computational tool for competitor extremality (crux-b), not a proof of it;
the all-n statement remains OPEN.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction as Fr

from telperion.matching_free_energy import rho

# Each length-2 arm rooted at its armmid (deg 2): unm=1, mat=1/2 -> total 3/2, matched-weight unm=1.
_ARM_TOTAL = Fr(3, 2)


def caterpillar_edges(arms):
    """Build `T(a_1,..,a_m)`: spine `0-1-...-(m-1)`, hub `i` carries `a_i` length-2 arms.

    Returns `(n, edges)`.  Hub ids are `0..m-1`; arm vertices follow.  Hub degree is
    `d_i = a_i + (#spine neighbours)`: `a_0` for a lone hub (`m == 1`), `a_i + 1` at an
    endpoint of a longer spine, `a_i + 2` in the interior.
    """
    m = len(arms)
    edges = []
    for i in range(m - 1):
        edges.append((i, i + 1))                       # spine edge
    nid = m
    for i in range(m):
        for _ in range(arms[i]):
            armmid, leaf = nid, nid + 1
            nid += 2
            edges.append((i, armmid))                  # hub - armmid
            edges.append((armmid, leaf))               # armmid - leaf
    return nid, tuple(edges)


def hub_degrees(arms):
    """Exact hub degrees `d_i` of `T(arms)` (spine-neighbour count depends on position)."""
    m = len(arms)
    if m == 1:
        return [arms[0]]
    return [arms[i] + (2 if 0 < i < m - 1 else 1) for i in range(m)]


def Z_recurrence(arms):
    """`Z(T(arms))` via the exact spine cavity/transfer recurrence (== `rho`, exact Fraction).

    Sweeps hubs `0..m-1`, carrying `(U, M) = (unm, mat)` of the partial subtree rooted at the
    current hub.  Each hub folds in its `a_i` length-2 arms (each an exact `(1, 1/2)` leaf on a
    deg-2 armmid, total `3/2`) and the incoming spine child, exactly as `rho`'s postorder DP does.
    """
    m = len(arms)
    if m == 0 or sum(arms) == 0:
        # empty / all-monomer spine: rho of a bare path (handled directly for completeness)
        n, edges = caterpillar_edges(arms)
        return rho(n, edges)
    d = hub_degrees(arms)
    U_prev = M_prev = None
    for i in range(m):
        di = d[i]
        Ui = _ARM_TOTAL ** arms[i]                     # product of arm totals
        if i > 0:
            Ui *= (U_prev + M_prev)                     # times spine-child total
        Mi = Fr(0)
        if arms[i] > 0:
            # match hub to one of a_i armmids (deg 2, unm=1); other children keep their totals
            Mi += arms[i] * Fr(1, di) * Fr(1, 2) * (Ui / _ARM_TOTAL)
        if i > 0:
            # match hub along the spine to hub i-1 (deg d_{i-1}), which must then be unmatched (U_prev)
            Mi += Fr(1, di) * Fr(1, d[i - 1]) * U_prev * (Ui / (U_prev + M_prev))
        U_prev, M_prev = Ui, Mi
    return U_prev + M_prev


def two_hub_Z(a, b):
    """Exact CLOSED FORM for the two-hub caterpillar `T(a, b)` (== `rho`, exact Fraction):

        Z(T(a,b)) = (3/2)^(a+b-2) * ( (4a+3)(4b+3) + 9 ) / ( 4 (a+1)(b+1) ).

    Derived from the `(U, M)` cavity of each hub: an arm presents `(1, 1/2)` on a deg-2 armmid,
    a hub with `k` arms + one spine child has `U+M = (3/2)^{k-1}(4k+3)/(2(k+1))`.  Verified against
    `matching_free_energy.rho` on the full `0<=a,b<=7` grid.  Base check: `T(0,0) = P_2`, `Z = 2`.
    """
    a, b = Fr(a), Fr(b)
    return _ARM_TOTAL ** (a + b - 2) * ((4 * a + 3) * (4 * b + 3) + 9) / (4 * (a + 1) * (b + 1))


def _two_hub_g(a, b):
    """Split-dependent factor `g(a,b) = ((4a+3)(4b+3)+9)/((a+1)(b+1))`; `Z(T(a,b)) = (3/2)^{s-2}/4 * g`
    with `s = a+b` fixed, so at fixed spine-arm-total the split maximizing `Z` maximizes `g`."""
    a, b = Fr(a), Fr(b)
    return ((4 * a + 3) * (4 * b + 3) + 9) / ((a + 1) * (b + 1))


def arm_balance_delta_g(a, b):
    """Exact `g(a-1, b+1) - g(a, b)` for the toward-balance arm move, in FACTORED form:

        g(a-1,b+1) - g(a,b) = 2 (a - b - 1)(2a + 2b - 1) / ( a (a+1)(b+1)(b+2) ).

    Every factor is > 0 for integers `a >= b + 2` (`a-b-1 >= 1`, `2a+2b-1 >= 3`, positive denom since
    `a >= 2`), so moving one arm from the fuller hub to the emptier one **strictly increases** `Z`
    until `|a-b| <= 1` (`a = b+1` gives `a-b-1 = 0`, the balanced tie).  This is the rigorous, ALL-`(a,b)`
    m=2 arm-balancing lemma -- a clean `ring` + factor-positivity proof, not finite instances -- and the
    one salvaged monotone move after local Z-monotone reduction to the caterpillar family was refuted at
    n=16 (see docs/BG_PIECE3_OBSTRUCTION_MAP.md).  Returns the exact Fraction (positive iff `a >= b+2`).

    LEAN PROOF OBLIGATION (for the `bg_arm_balancing` CI gate): over `a b : Nat`, `h : b + 2 <= a`,
    the identity `g(a-1,b+1) - g(a,b) = 2*(a-b-1)*(2*a+2*b-1)/(a*(a+1)*(b+1)*(b+2))` by `field_simp; ring`,
    then `> 0` by `positivity`/factor signs.  conjecture1_proved = False.
    """
    a, b = Fr(a), Fr(b)
    return 2 * (a - b - 1) * (2 * a + 2 * b - 1) / (a * (a + 1) * (b + 1) * (b + 2))


def uniform_transfer_matrix(a):
    """Exact rational 2x2 per-hub transfer matrix for the uniform interior hub (`d = a + 2`).

    Acts on the cavity state `(U, M)^T`:
        U' = (3/2)^a (U + M)
        M' = [ a/(2(a+2)) (3/2)^{a-1} ] (U + M)  +  [ (3/2)^a / (a+2)^2 ] U
    The top eigenvalue is the per-hub growth rate `lam(a)` (see `perron_eigenvalue`).
    """
    g = _ARM_TOTAL
    d = a + 2
    ga = g ** a
    gam1 = g ** (a - 1) if a >= 1 else Fr(2, 3)
    c = Fr(a, 2 * d) * gam1                             # coefficient on (U + M) in M'
    e = ga / (d * d)                                    # coefficient on U in M'
    # rows: [U', M'] in basis (U, M)
    return [[ga, ga],
            [c + e, c]]


def perron_eigenvalue(a):
    """Top eigenvalue `lam(a)` of the uniform transfer matrix, as `(trace, det, disc, float)`.

    `lam = (trace + sqrt(disc)) / 2` with exact rational `trace`, `det`, `disc = trace^2 - 4 det`.
    Returns `(trace, det, disc, lam_float)` so the surd is exact where it matters and numeric for
    the free-energy readout.
    """
    T = uniform_transfer_matrix(a)
    trace = T[0][0] + T[1][1]
    det = T[0][0] * T[1][1] - T[0][1] * T[1][0]
    disc = trace * trace - 4 * det
    lam = (float(trace) + math.sqrt(float(disc))) / 2.0
    return trace, det, disc, lam


def free_energy(a):
    """Per-vertex matching free energy of the uniform caterpillar: `F(a) = log(lam(a))/(2a+1)`.

    Each hub contributes `2a + 1` vertices (hub + `a` arms of 2).  As `m -> inf` this equals
    `(1/n) log rho` of a long uniform caterpillar.  `F(a)` peaks at `a = 7` (`~0.205098`).
    """
    _, _, _, lam = perron_eigenvalue(a)
    return math.log(lam) / (2 * a + 1)


_DEFAULT_CHECK_ARMS = (
    [3], [7], [6], [4, 4], [3, 4, 3], [7, 7, 7], [2, 5, 2, 5], [6, 6, 6, 6],
    [1, 1], [3, 0, 3], [0, 0, 3], [5, 0, 0, 5], [2, 1, 4, 1, 2],
)


@dataclass(frozen=True)
class TransferCaterpillarCertificate:
    """Certifies `Z_recurrence(arms) == rho(*caterpillar_edges(arms))` exactly over a family.

    The witness is that the linear spine transfer reproduces the monomer-dimer partition function
    on every tested caterpillar (single-hub near-star through multi-hub balanced), so `Z_recurrence`
    is a validated exact surrogate for `rho` on this family.  This discharges the *computational*
    engine for competitor extremality (crux-b); the all-n extremality statement remains OPEN.
    conjecture1_proved = False.
    """

    arms_family: tuple = field(default=_DEFAULT_CHECK_ARMS)

    def mismatches(self):
        """List of `(arms, rho, Z_recurrence)` triples where the two disagree (should be empty)."""
        bad = []
        for arms in self.arms_family:
            if sum(arms) == 0:
                continue
            n, edges = caterpillar_edges(list(arms))
            r = rho(n, edges)
            z = Z_recurrence(list(arms))
            if r != z:
                bad.append((list(arms), r, z))
        return bad

    def check(self) -> bool:
        """True iff the transfer recurrence equals `rho` exactly on every arms list in the family."""
        return not self.mismatches()

    def free_energy_table(self, lo=3, hi=12):
        """`{a: F(a)}` over `a in [lo, hi]` (interior max at a=7 ~ 0.205098)."""
        return {a: free_energy(a) for a in range(lo, hi + 1)}


conjecture1_proved = False
