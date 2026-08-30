"""Girardeau duality -- the bridge between the bosonic and fermionic toolkits.

The tree matchings are HARD-CORE bosons (each vertex lies in at most one dimer -- occupation capped at 1).
By the Girardeau / Tonks-Girardeau correspondence, hard-core bosons are DUAL to free fermions.  On a tree
this duality is exact and takes three equal forms:

    per(L)/prod(deg)   =   prod_{lambda > 0} (1 + lambda^2)   =   |det(I + iN)|,
    ^^^^^^^^^^^^^^^^        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^        ^^^^^^^^^^^^^
    hard-core boson        free-fermion spectral product           functional
    partition function     (N = D^{-1/2} A D^{-1/2})                determinant

The first is the BOSONIC permanent (symmetric, matchings); the second is the FREE-FERMION partition
function over the positive normalized-adjacency modes (the half-spectrum, since a tree is bipartite so the
spectrum is +-symmetric); the third exposes both as a spectral / functional determinant.  VERIFIED for all
trees n <= 9.

This is WHY the boson and fermion readings of the Brualdi-Goldwasser object gave the same arithmetic all
along: they are one object with two dual descriptions, and Phi^11 = (64/621)^n |det(D+iA)|^11 / (...)  is a
functional determinant to the 11th power.  The duality is EXACT and descriptive; it proves nothing new
about the conjecture (conjecture1_proved = False), it explains the coincidence and unifies the two toolkits.
"""
from __future__ import annotations

from dataclasses import dataclass

from .matching_free_energy import rho as _matching_rho
from .spectral import spectral_rho


def hard_core_boson_partition(n, edges):
    """The hard-core BOSON partition function per(L)/prod(deg) = sum over matchings of prod 1/deg
    (symmetric permanent; each vertex in <=1 dimer)."""
    return _matching_rho(n, edges)


def free_fermion_product(n, edges):
    """The FREE-FERMION partition function prod_{lambda>0}(1+lambda^2) over the positive normalized-
    adjacency modes (N = D^{-1/2} A D^{-1/2})."""
    return spectral_rho(n, edges)


def functional_determinant(n, edges):
    """|det(I + iN)| -- the spectral/functional-determinant form of both partition functions."""
    import networkx as nx
    import numpy as np
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    deg = A.sum(1)
    N = np.diag(1 / np.sqrt(deg)) @ A @ np.diag(1 / np.sqrt(deg))
    return abs(np.linalg.det(np.eye(n) + 1j * N))


@dataclass(frozen=True)
class GirardeauDualityCertificate:
    """Certifies the Girardeau (hard-core-boson <-> free-fermion) duality on trees:
    per(L)/prod(deg) = prod_{lambda>0}(1+lambda^2) = |det(I+iN)|, over all trees up to n_max."""

    n_max: int = 9
    tol: float = 1e-7

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def duality_holds(self):
        """(total_trees, satisfying) with the three forms equal within tol, over all trees n<=n_max."""
        import networkx as nx
        total = ok = 0
        for n in range(2, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                total += 1
                hcb = float(hard_core_boson_partition(nn, e))
                ff = free_fermion_product(nn, e)
                fd = functional_determinant(nn, e)
                if abs(hcb - ff) < self.tol and abs(hcb - fd) < self.tol:
                    ok += 1
        return total, ok

    def check(self) -> bool:
        total, ok = self.duality_holds()
        return total > 0 and ok == total
