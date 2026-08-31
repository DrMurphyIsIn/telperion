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


def broom_total(c):
    """Closed form `total(B(c)) = (3/2)^(c-1)(4c+3)/(2(c+1))` (== `branch_total(*broom_edges(c))`; `B(5)=621/64`)."""
    return Fr(3, 2) ** (c - 1) * (4 * c + 3) / (2 * (c + 1))


conjecture1_proved = False
