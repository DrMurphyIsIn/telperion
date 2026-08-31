"""S0a: the VDB-weighted matching generating polynomial M(T,t)=sum_k Z_k t^k.

Cross-checks: M(T,1) == matching_free_energy.rho (= Z = per(L)/prod deg) exactly on structured + random +
exhaustive-small trees; Z_1 == the reciprocal Randic index; coefficientwise-domination certificate.
"""
import random
from fractions import Fraction as Fr

import networkx as nx

from telperion.matching_free_energy import rho
from telperion.weighted_matching import (
    CoefficientwiseDomination,
    matching_generating_poly,
    weighted_Z,
)


def _edges(G):
    idx = {v: i for i, v in enumerate(G.nodes())}
    return G.number_of_nodes(), [(idx[a], idx[b]) for a, b in G.edges()]


def _caterpillar(spine, a, L=2):
    G = nx.Graph()
    nid = spine
    for i in range(spine - 1):
        G.add_edge(i, i + 1)
    for i in range(spine):
        for _ in range(a):
            p = i
            for _ in range(L):
                G.add_edge(p, nid)
                p = nid
                nid += 1
    return G


def test_generating_poly_sums_to_rho():
    trees = [nx.path_graph(1), nx.path_graph(2), nx.path_graph(6), nx.star_graph(5),
             _caterpillar(4, 3), _caterpillar(3, 7), nx.balanced_tree(2, 4)]
    rng = random.Random(0)
    for s in range(15):
        trees.append(nx.random_labeled_tree(rng.randint(6, 30), seed=s))
    for G in trees:
        n, e = _edges(G)
        assert weighted_Z(n, e) == rho(n, e)


def test_Z1_is_reciprocal_randic():
    G = _caterpillar(4, 3)
    n, e = _edges(G)
    deg = dict(G.degree())
    randic = sum(Fr(1, deg[a] * deg[b]) for a, b in G.edges())
    assert matching_generating_poly(n, e)[1] == randic


def test_Z0_is_one_and_exact_small():
    # exhaustive: M(T,1) == rho for every tree up to N=9
    for N in range(2, 10):
        for T in nx.nonisomorphic_trees(N):
            n, e = _edges(T)
            poly = matching_generating_poly(n, e)
            assert poly[0] == Fr(1)
            assert sum(poly) == rho(n, e)


def test_coefficientwise_domination_certificate():
    # star (deg-concentrated) vs path on same N: check the certificate machinery on a known pair
    n1, e1 = _edges(nx.star_graph(5))
    n2, e2 = _edges(nx.path_graph(6))
    ps, pb = matching_generating_poly(n1, e1), matching_generating_poly(n2, e2)
    cert = CoefficientwiseDomination("star_vs_path", tuple(ps), tuple(pb))
    # whichever direction, check()/first_violation are consistent
    assert cert.check() == (cert.first_violation() is None)
