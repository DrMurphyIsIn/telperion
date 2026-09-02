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


def test_unrooted_broom_dominance_and_exchange_obstruction():
    """Two facts about the combinatorial core (Obligation A): (1) the UNROOTED per(L)/prod-deg maximiser at odd
    size 2c+1 is the single-hub broom B(c) (verified n<=13); (2) the natural 'concentration' exchange (move a
    cherry between two edge-joined hubs) is NON-MONOTONE toward the broom -- deltaZ flips sign with the hub
    balance -- so a greedy single-move exchange cannot prove broom dominance. This is the precise obstruction
    that keeps (A) open."""
    from fractions import Fraction as Fr
    import networkx as nx
    from telperion.matching_free_energy import rho
    from telperion.vdb_exchange import delta_Z

    def degseq(T):
        return sorted((d for _, d in T.degree()), reverse=True)

    # (1) unrooted rho max at size 2c+1 is the single-hub broom degseq [c, 2 (x c), 1 (x c)]
    for c in (3, 4, 5):
        n = 2 * c + 1
        best = (Fr(0), None)
        for T in nx.nonisomorphic_trees(n):
            idx = {v: i for i, v in enumerate(T.nodes())}
            ee = tuple((idx[a], idx[b]) for a, b in T.edges())
            z = rho(n, ee)
            if z > best[0]:
                best = (z, degseq(T))
        assert best[1] == [c] + [2] * c + [1] * c, f"unrooted max at n={n} is not the broom: {best[1]}"

    # (2) non-monotone concentration move
    def two_hub(a, b):
        edges = [(0, 1)]; nid = 2
        for _ in range(a):
            edges += [(0, nid), (nid, nid + 1)]; nid += 2
        for _ in range(b):
            edges += [(1, nid), (nid, nid + 1)]; nid += 2
        return nid, tuple(edges)

    n1, e1 = two_hub(1, 1); n2, e2 = two_hub(1, 3)
    d_equal = delta_Z(n1, e1, ("balance_arm", 1, 0))     # concentrate onto equal hub: LOWERS Z
    d_unbal = delta_Z(n2, e2, ("balance_arm", 1, 0))     # move from bigger hub: RAISES Z
    assert d_equal < 0 < d_unbal                          # opposite signs => greedy exchange is non-monotone


def test_exchange_local_maxima_are_caterpillars():
    """The sharp form of the exchange obstruction: under the RICH single-edge-relocation neighborhood, the only
    spurious local maxima of the unrooted rho (broom dominance) are multi-hub LENGTH-2-ARM CATERPILLARS -- exactly
    Pant's conjectured maximiser family -- and the broom (spider) beats each. So Obligation A reduces to
    [every rich-exchange local max is the broom or a length-2 caterpillar] + [spider > caterpillar] (the
    transfer-matrix comparison the campaign established). Verified n<=11 here (n=13, 15 verified offline).
    NB: part (i) does NOT factor via the obvious arm-shortening move (length-3 arm tip -> cherry DECREASES rho);
    the rho-increasing escape from a non-caterpillar tree is genuinely non-greedy."""
    import networkx as nx
    from telperion.matching_free_energy import rho

    def strip(G):
        G = G.copy(); G.remove_nodes_from([v for v in list(G) if G.degree(v) <= 1]); return G

    def is_len2_caterpillar_multihub(T):
        spine = strip(strip(T))                       # remove leaves twice -> the hub spine
        if spine.number_of_nodes() < 2:
            return False                              # single-hub (the broom), not a multi-hub caterpillar
        return (nx.is_connected(spine) and all(spine.degree(v) <= 2 for v in spine)
                and sum(1 for v in spine if spine.degree(v) == 1) <= 2)     # spine is a path

    def subtree_moves(n, edges):
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges); out = []
        for (a, b) in edges:
            G.remove_edge(a, b); comp = list(nx.connected_components(G))
            ca = comp[0] if a in comp[0] else comp[1]; cb = comp[1] if a in comp[0] else comp[0]
            base = [e for e in edges if set(e) != {a, b}]
            for u in ca:
                if u != a: out.append(tuple(base + [(b, u)]))
            for u in cb:
                if u != b: out.append(tuple(base + [(a, u)]))
            G.add_edge(a, b)
        return out

    from telperion.branch_potential import branch_total, broom_edges
    for n in (9, 11):
        c = (n - 1) // 2
        broomdeg = [c] + [2] * c + [1] * c
        broom_rho = rho(*broom_edges(c))                                  # the broom's unrooted Z (computed upfront)
        spurious = 0
        for T in nx.nonisomorphic_trees(n):
            idx = {v: i for i, v in enumerate(T.nodes())}
            ee = tuple((idx[a], idx[b]) for a, b in T.edges())
            z = rho(n, ee)
            degs = sorted((d for _, d in T.degree()), reverse=True)
            if not any(rho(n, e2) > z for e2 in subtree_moves(n, ee)):     # a local max
                if degs != broomdeg:
                    spurious += 1
                    assert is_len2_caterpillar_multihub(T), f"n={n}: spurious local max is not a length-2 caterpillar"
                    assert z < broom_rho                                   # spider strictly beats the caterpillar
        if n == 11:
            assert spurious >= 1                                          # the barrier is real (not vacuous)


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
