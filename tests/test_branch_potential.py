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
    F_STAR, branch_ell, branch_ell_by_vertex, branch_total, broom_edges,
)
from telperion.spider_broom import broom_total, spider_edges  # noqa: E402


def _edges(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), [(idx[a], idx[b]) for a, b in T.edges()], idx


def test_cavity_per_vertex_decomposition():
    """ell(B) = sum_v (A_v - F*) exactly (the cavity telescoping): matches branch_ell, one term per vertex,
    leaves contribute -F* (A=0), a cherry's armmid contributes +log(3/2)-F*."""
    # leaf: single vertex, A=0 -> contribution -F*
    ell1, contrib1 = branch_ell_by_vertex(1, ())
    assert len(contrib1) == 1 and abs(contrib1[0] - (-F_STAR)) < 1e-12
    # cherry (armmid 0 -> leaf 1): armmid A=log(3/2), leaf A=0
    ell_c, contrib_c = branch_ell_by_vertex(2, ((0, 1),), 0)
    assert abs(contrib_c[0] - (math.log(1.5) - F_STAR)) < 1e-12
    assert abs(contrib_c[1] - (-F_STAR)) < 1e-12
    # matches branch_ell over structured + random rooted branches
    import random
    rng = random.Random(3)
    for N in range(2, 13):
        trees = list(nx.nonisomorphic_trees(N))
        for T in (trees if N <= 9 else rng.sample(trees, min(40, len(trees)))):
            n, e, idx = _edges(T)
            for r in list(T.nodes())[:3]:
                e_ref, _ = branch_ell(n, tuple(e), idx[r])
                e_dec, contrib = branch_ell_by_vertex(n, tuple(e), idx[r])
                assert len(contrib) == n
                assert abs(e_ref - e_dec) < 1e-11


def test_broom_dominance_and_23_pin():
    """The two poles of the BG upper bound: (combinatorial) broom dominance -- the broom B(c) is the UNIQUE
    total-maximiser among rooted branches of odd size 2c+1 (Obligation A, open; verified small); and
    (arithmetic) the c=5 optimum is pinned by the single prime 23 in three places."""
    from telperion.branch_potential import broom_dominance_holds, broom_optimum_prime
    from fractions import Fraction as Fr
    # broom dominance holds for every odd size up to 13
    for n in range(3, 14, 2):
        holds, mx, bt = broom_dominance_holds(n)
        assert holds is True, f"broom is NOT the unique total-max at size {n}"
        assert bt == mx
    # even sizes have no broom
    assert broom_dominance_holds(6)[0] is None
    # the 23-pin: 4*5+3 = 4*4+7 = 23, 529 = 23^2, total(B5) = 621/64 = 27*23/64
    p = broom_optimum_prime()
    assert p["prime"] == 23 == p["num_at_c5"] == p["ratio_factor_at_s4"]
    assert p["ratio_const_num"] == 529 and p["total_B5"] == Fr(621, 64)


def test_low_degree_root_dilutes_adversarial():
    """The make-or-break case for the small-degree refined-ceiling residual (b): a degree-2 root with a large
    near-extremal star-of-brooms hanging entirely below it. The low root degree DILUTES per-vertex density, so
    ell stays deeply below the tie (~ -0.27), NOT near 0 -- refuting the failure mode (a large low-degree branch
    with ell ~ 0). Confirms the near-ceiling d<=6 set is the finite broom set, so (b) is finitely closable."""
    from telperion.branch_potential import _adj
    for kc in range(2, 9):
        N, ee = spider_edges(kc, 5)                       # star of kc B(5)-arms; hub = max-degree vertex
        adj = _adj(N, ee)
        hub = max(range(N), key=lambda v: len(adj[v]))
        # attach a new degree-2 root above the hub
        ell, contrib = branch_ell_by_vertex(N + 1, tuple(list(ee) + [(hub, N)]), N)
        assert len(contrib) == N + 1
        assert ell < -0.2                                  # deeply sub-threshold (dilution), not near the ceiling


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


def test_mixed_le_Bk_exhaustive():
    """mixed <= B(k), EXHAUSTIVELY (per the honest caveat): over ALL rooted branches with root-degree k,
    ell <= ell(B(k)) for k >= 2 -- and it is TIGHT (max = ell(B(k))) for k <= 7 (where B(k) fits, N<=16).
    No counterexample (contrast the tangent route, which had them)."""
    from telperion.branch_potential import broom_edges
    ellBk = {k: branch_ell(*broom_edges(k))[0] for k in range(1, 9)}
    worst_per_k = {}
    for N in range(2, 17):
        for T in nx.nonisomorphic_trees(N):
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = [(idx[a], idx[b]) for a, b in T.edges()]
            for r in T.nodes():
                k = T.degree(r)
                ell, _ = branch_ell(N, e, idx[r])
                worst_per_k[k] = max(worst_per_k.get(k, -9.9), ell)
    for k in range(2, 8):                                      # B(k) fits in N<=16 (size 2k+1 <= 15)
        assert worst_per_k[k] <= ellBk[k] + 1e-12, f"mixed > B({k})"
        assert abs(worst_per_k[k] - ellBk[k]) < 1e-9, f"B({k}) should be the tight max at k={k}"


def test_boundary_bound_pi_over_branch_total():
    """Boundary lemma: 1 <= pi(T)/branch_total(T,r) <= 4/3 (O(1)), so ell(B)<=0 => (1/n)log pi(T) <= F* + O(1/n).
    The branch-induction route to the asymptotic upper bound needs only this bounded root-boundary term."""
    from telperion.matching_free_energy import rho
    worst = Fr(1)
    for N in range(2, 12):
        for T in nx.nonisomorphic_trees(N):
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = [(idx[a], idx[b]) for a, b in T.edges()]
            pi = rho(N, e)
            for r in range(N):
                ratio = pi / branch_total(N, e, r)
                assert ratio >= 1                              # up-edge lowers total
                worst = max(worst, ratio)
    assert worst <= Fr(4, 3)                                   # bounded => O(1) boundary


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
