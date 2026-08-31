"""Tests for the branch potential ell(B) and the broom-dominance reduction of the BG upper bound.

Verifies: branch_total == the broom closed form; the additive recursion ell(B) = sum_c ell(c) + (A_root - F*);
ell(B(5)) = 0 (the unique tie); and -- exhaustively for small odd sizes -- the broom B(c) is the unique
total-maximising rooted branch of size 2c+1.  conjecture1_proved = False.
"""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

import networkx as nx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.branch_potential import (  # noqa: E402
    F_STAR, branch_ell, branch_total, broom_edges,
)
from telperion.spider_broom import broom_total  # noqa: E402


def _edges(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), [(idx[a], idx[b]) for a, b in T.edges()], idx


def test_branch_total_matches_broom_closed_form():
    for c in range(1, 9):
        n, e = broom_edges(c)
        assert branch_total(n, e) == broom_total(c), f"broom B({c}) total mismatch"


def test_ell_of_B5_is_zero_unique_tie():
    ell5, t5 = branch_ell(*broom_edges(5))
    assert t5 == Fr(621, 64)
    assert abs(ell5) < 1e-12                                  # ell(B(5)) = 0
    for c in (3, 4, 6, 7, 8):
        ellc, _ = branch_ell(*broom_edges(c))
        assert ellc < -1e-9, f"ell(B({c})) must be < 0"       # strict for c != 5


def test_ell_additive_recursion():
    """ell(B) = sum_{c child} ell(c) + (A_root - F*), exact per the rooted Bethe telescoping."""
    def um(adj, r, p):
        kids = [u for u in adj[r] if u != p]
        d = len(kids) + 1
        ch = [(c,) + um(adj, c, r) for c in kids]
        U = Fr(1)
        for c, Uc, Mc, tc, sc in ch:
            U *= tc
        M = Fr(0)
        for i, (c, Uc, Mc, tc, sc) in enumerate(ch):
            dc = len([u for u in adj[c] if u != r]) + 1
            term = Fr(1, d * dc) * Uc
            for j, (c2, Uc2, Mc2, tc2, sc2) in enumerate(ch):
                if j != i:
                    term *= tc2
            M += term
        return U, M, U + M, 1 + sum(sc for *_, sc in ch)
    import random
    for seed in range(20):
        T = nx.random_labeled_tree(random.Random(seed).randint(3, 13), seed=seed)
        n, e, idx = _edges(T)
        adj = {i: [] for i in range(n)}
        for u, v in e:
            adj[u].append(v)
            adj[v].append(u)
        root = 0
        lhs, _ = branch_ell(n, e, root)
        # A_root - F*
        d = len(adj[root]) + 1
        s = Fr(0)
        rhs = 0.0
        for c in adj[root]:
            Uc, Mc, tc, sc = um(adj, c, root)
            dc = len([u for u in adj[c] if u != root]) + 1
            s += Fr(1, d * dc) * (Uc / tc)
            rhs += (math.log(tc.numerator) - math.log(tc.denominator)) - sc * F_STAR
        rhs += math.log(float(1 + s)) - F_STAR
        assert abs(lhs - rhs) < 1e-9, f"recursion fails at seed {seed}"


def test_broom_dominance_exhaustive_small():
    """The broom B(c) is the UNIQUE total-maximising rooted branch of size 2c+1 (exhaustive, odd N<=13)."""
    for N in (3, 5, 7, 9, 11, 13):
        c = (N - 1) // 2
        best = Fr(0)
        for T in nx.nonisomorphic_trees(N):
            for r in T.nodes():
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = [(idx[a], idx[b]) for a, b in T.edges()]
                best = max(best, branch_total(N, e, idx[r]))
        assert best == broom_total(c), f"broom does not dominate at N={N}"
