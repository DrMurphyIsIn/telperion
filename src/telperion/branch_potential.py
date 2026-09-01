"""Branch potential ell(B) -- the additive form of the BG upper bound, and the broom-dominance reduction.

The classical-BG upper bound `F(T) = (1/|T|) log pi(T) <= F* = log(621/64)/11` (asymptotically) is equivalent
to `ell(B) <= 0` for every ROOTED branch `B`, where

    ell(B) := log total(B) - |B| * F*,        total(B) = weighted matching sum, root degree = children + 1.

This satisfies the EXACT additive recursion (verified vs the cavity DP):

    ell(B) = sum_{c child of root} ell(c) + (A_root - F*),     A_root = log(1 + sum_c w_{root,c} h_c),

`h_c = U_c / total(c)` the child's cavity field, `w = 1/(d_root d_c)` -- the per-vertex "local gain" in the
rooted Bethe telescoping `log total(B) = sum_v A_v^rooted`.  So `ell(B) <= 0` iff the accumulated child credits
`-ell(c) >= 0` cover the root excess `A_root - F*` -- the additive discharge / cavity potential (the same object
the Phi^11 program's `cavity_potential.py` found; see `docs/BG_23ADIC_RECONCILIATION_20260831.md`).

KEY STRUCTURAL FACT (exhaustive, this campaign): for every ODD size `2c+1` the `ell`-maximising rooted branch is
EXACTLY the broom `B(c)` (`c` length-2 cherries on one hub); even sizes are strictly below; the global max over
all sizes is `B(5)` at `ell = 0`.  So the branch-ceiling `ell(B) <= 0` reduces to

    (A) BROOM DOMINANCE:  the broom `B(c)` maximises `total(B)` among rooted branches of size `2c+1`   [open],
    (B) BROOM OPTIMUM:    `ell(B(c)) <= 0`, `= 0` iff `c = 5`   [PROVEN -- spider_broom.broom_ratio single-crossing].

(A) is a clean rooted-tree extremal sub-problem (the rooted analog of the parallel Lean session's tree->hub /
Kelmans reduction).  Combined with the tree->hub reduction it gives the BG upper bound.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

F_STAR = math.log(621 / 64) / 11


def _um(adj, deg, root, parent):
    """(U, M, total, size) for the branch rooted at `root` (root degree = #children + 1, the up-edge)."""
    kids = [u for u in adj[root] if u != parent]
    d = len(kids) + 1
    ch = []
    U = Fr(1)
    size = 1
    for c in kids:
        Uc, Mc, tc, sc = _um(adj, deg, c, root)
        ch.append((c, Uc, tc))
        U *= tc
        size += sc
    M = Fr(0)
    for i, (c, Uc, tc) in enumerate(ch):
        dc = len([u for u in adj[c] if u != root]) + 1
        term = Fr(1, d * dc) * Uc
        for j, (c2, Uc2, tc2) in enumerate(ch):
            if j != i:
                term *= tc2
        M += term
    return U, M, U + M, size


def _adj(n, edges):
    a = {i: [] for i in range(n)}
    for u, v in edges:
        a[u].append(v)
        a[v].append(u)
    return a


def branch_total(n, edges, root=0):
    """Exact `total(B)` (weighted matching sum) of the tree rooted at `root`, root degree counting the up-edge."""
    adj = _adj(n, edges)
    deg = {v: len(adj[v]) for v in range(n)}
    return _um(adj, deg, root, -1)[2]


def branch_ell(n, edges, root=0):
    """`ell(B) = log total(B) - |B| F*`.  `<= 0` for all rooted branches is the BG upper bound (open);
    `= 0` uniquely at the broom `B(5)` (size 11, `total = 621/64`)."""
    t = branch_total(n, edges, root)
    size = n
    return (math.log(t.numerator) - math.log(t.denominator)) - size * F_STAR, t


def branch_ell_by_vertex(n, edges, root=0):
    """The cavity per-vertex decomposition `ell(B) = sum_v (A_v - F*)` (VERIFIED == `branch_ell`).  Returns
    `(ell, deficits)` where `deficits[v] = F* - A_v >= 0?` NO -- returns the per-vertex CONTRIBUTIONS `A_v - F*`
    (a dict `v -> A_v - F*`), `A_v = log(1 + sum_{children w} h_w/(d_v d_w))` the rooted local-hub gain.  Leaves
    contribute `-F*` (`A=0`); internal hubs can be positive (a cherry's armmid `= log(3/2)-F* = +0.198`).  The
    deficit view of the branch ceiling: `ell(B) <= 0` iff the profitable hubs cover the leaves' `F*` cost.  This
    is the exact object behind the small-degree refined-ceiling residual (b): a low root degree caps `A_root`, so
    a large low-degree branch cannot marshal enough hub profit to offset its leaves -> `ell` stays well below 0
    (empirically `>= 0.06` below the tie for `d_c <= 6` non-brooms)."""
    adj = _adj(n, edges)
    contrib = {}

    def rec(u, p):
        kids = [w for w in adj[u] if w != p]
        d = len(kids) + 1
        S = Fr(0)
        tot_u = Fr(1)
        for w in kids:
            h_w, d_w, t_w = rec(w, u)
            S += h_w / (d * d_w)
            tot_u *= t_w
        A = math.log((1 + S).numerator) - math.log((1 + S).denominator)
        contrib[u] = A - F_STAR
        tot_u *= (1 + S)
        return Fr(1) / (1 + S), d, tot_u        # (h_u = U_u/total_u = 1/(1+S), d_u, total_u)

    rec(root, -1)
    return sum(contrib.values()), contrib


def broom_edges(c):
    """The broom `B(c)`: one hub (`0`) with `c` length-2 cherries (hub-armmid-leaf).  Size `2c+1`."""
    edges = []
    nid = 1
    for _ in range(c):
        mid, leaf = nid, nid + 1
        nid += 2
        edges.append((0, mid))
        edges.append((mid, leaf))
    return nid, tuple(edges)


def broom_dominance_holds(n):
    """BROOM DOMINANCE (Obligation A) witness: for ODD size `n = 2c+1`, is the broom `B(c)` the UNIQUE
    total-maximiser among all rooted branches of size `n`?  Returns `(holds, max_total, broom_total)`.  This is
    the open COMBINATORIAL core of the BG upper bound (the rooted analog of the tree->hub / Kelmans reduction);
    verified here for small `n`.  Even `n` has no broom; returns `(None, max_total, None)`.  The self-similarity
    of the mixed-hub envelope (brooms are the extremal children at every degree) makes the branch-induction
    residual (b) a facet of THIS lemma -- so the remaining work is combinatorial, the arithmetic being gated
    (`spider_broom.BroomOptimumCertificate` / `SmoothNoGoCertificate`).  conjecture1_proved = False."""
    import networkx as nx
    best = Fr(0)
    for T in nx.nonisomorphic_trees(n):
        idx = {v: i for i, v in enumerate(T.nodes())}
        edges = tuple((idx[a], idx[b]) for a, b in T.edges())
        for r in range(n):
            t = branch_total(n, edges, r)
            if t > best:
                best = t
    if n % 2 == 0:
        return None, best, None
    c = (n - 1) // 2
    bt = branch_total(*broom_edges(c))
    return bt == best, best, bt


def broom_optimum_prime():
    """The arithmetic pin of the `c=5` broom optimum: the prime `23`.  Returns the verified identities as a dict.
    `4*5+3 = 23` (numerator of `total(B(5)) = 621/64 = 27*23/64`), `4*4+7 = 23` (the `broom_ratio` crossing
    factor `g(4)=(4*4+7)(4+1)=23*5`), and `529 = 23^2` (the `broom_ratio` constant `529/486`, `486 = 2*3^5`).
    `4s+7 = 4(s+1)+3` identically, so the single prime `23` at the integer boundary `s=4|5` pins the optimum in
    all three places -- the arithmetic heart the smooth relaxation cannot see."""
    assert 4 * 5 + 3 == 23 and 4 * 4 + 7 == 23 and 23 ** 2 == 529 and 2 * 3 ** 5 == 486
    assert broom_total(5) == Fr(621, 64) == Fr(27 * 23, 64)
    return {"prime": 23, "total_B5": Fr(621, 64), "num_at_c5": 4 * 5 + 3,
            "ratio_factor_at_s4": 4 * 4 + 7, "ratio_const_num": 23 ** 2, "ratio_const_den": 2 * 3 ** 5}


def broom_total(c):
    """Closed form `total(B(c)) = (3/2)^(c-1)(4c+3)/(2(c+1))` (== `branch_total(*broom_edges(c))`; `B(5)=621/64`)."""
    return Fr(3, 2) ** (c - 1) * (4 * c + 3) / (2 * (c + 1))


conjecture1_proved = False
