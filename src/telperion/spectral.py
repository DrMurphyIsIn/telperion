"""Free-fermion / Green's-function toolkit for the tree matching problem.

The tree Laplacian matching model IS a free-fermion system (Kasteleyn; Godsil-Gutman: a forest's
matching polynomial equals the adjacency characteristic polynomial).  This module ports the verified
spectral structure -- the honest, grounded pieces, not open-ended physics.

Established / verified identities (see docs and the session record):

  1. Raw matching sum (GLOBAL free-fermion partition function).  For a tree,
        rho(T) = per(L)/prod(deg) = PROD_{lambda > 0 of N}(1 + lambda^2),   N = D^{-1/2} A D^{-1/2},
     verified for all trees n <= 11.  The near-star N(0,s) has an (s-1)-fold degenerate mode at
     1/sqrt(2) (identical fermion modes = the arms) plus a mode at 1, giving rho = (4/3)(3/2)^s.

  2. Rooted branch Phi (LOCAL Green's function = the ACTUAL BG quantity).  The cavity recursion
     m_v = z/(1 + z sum_children m_c) is the Bethe-lattice continued-fraction Green's function
     (Abou-Chacra-Anderson-Thouless 1973).  It spectralizes as a benchmarked IMPURITY determinant:
        Phi^11(rooted at r) = (64/621)^n * det(H_r)^11 / (prod_v d'_v)^11,
        H_r = D + i A  (imaginary hopping),  D'_rr = deg(r)+1  (a virtual-parent impurity at r),
     verified exactly for all trees / all roots n <= 9.  BG's max-over-roots = the RESONANT IMPURITY
     site; the near-star hub is the optimal impurity; the tie (Phi=1) is a spectral resonance.

Spectra are floating-point (eigenvalues are irrational); the exact Phi lives in rooted_phi.py.  This
module is the spectral LENS on that exact object.
"""
from __future__ import annotations

from collections import Counter

try:
    import numpy as np
    import networkx as nx
    _SPECTRAL = True
except Exception:  # pragma: no cover
    _SPECTRAL = False


def _graph(n, edges):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    return G


def normalized_adjacency_spectrum(n, edges):
    """Eigenvalues of N = D^{-1/2} A D^{-1/2} (the free-fermion single-particle energies)."""
    G = _graph(n, edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    deg = A.sum(1)
    Dm = np.diag(1.0 / np.sqrt(deg))
    return np.linalg.eigvalsh(Dm @ A @ Dm)


def free_fermion_modes(n, edges, tol=1e-6):
    """{energy: multiplicity} for the positive normalized-adjacency modes (degeneracy = symmetry)."""
    ev = normalized_adjacency_spectrum(n, edges)
    return dict(Counter(round(float(l), 4) for l in ev if l > tol))


def spectral_rho(n, edges):
    """rho = per(L)/prod(deg) as the free-fermion partition function PROD_{lambda>0}(1+lambda^2)."""
    ev = normalized_adjacency_spectrum(n, edges)
    out = 1.0
    for l in ev:
        if l > 1e-9:
            out *= (1.0 + l * l)
    return out


def impurity_determinant_phi11(n, edges, root):
    """Phi^11(rooted at `root`) via the benchmarked impurity determinant
    (64/621)^n det(D'+iA)^11 / (prod d')^11, D' = deg with a +1 impurity at the root.  Complex-float;
    matches the exact rooted_phi.phi11_rooted."""
    G = _graph(n, edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    dprime = np.array([G.degree(v) for v in range(n)], dtype=complex)
    dprime[root] += 1
    H = np.diag(dprime) + 1j * A
    detH = np.linalg.det(H)
    return (64.0 / 621.0) ** n * detH ** 11 / np.prod(dprime) ** 11


def resonant_impurity_site(n, edges):
    """(max Phi^11, root) -- the vertex whose virtual-parent impurity maximizes the benchmarked
    determinant.  This is BG's max-over-roots read as a resonant-impurity selection."""
    best = None
    for r in range(n):
        v = impurity_determinant_phi11(n, edges, r).real
        if best is None or v > best[0]:
            best = (v, r)
    return best


# ---- Friedel impurity toolkit ----------------------------------------------
# By the matrix-determinant lemma, a +1 on-site impurity at r multiplies the host determinant by
# (1 + G_rr), G_rr = [(D+iA)^{-1}]_rr the HOST local Green's function.  So the root-dependence of Phi^11
# collapses onto the local Friedel RESPONSE  R(r) = (1 + G_rr) * deg_r/(deg_r+1):
#     Phi^11(rooted at r) = [root-independent const] * R(r)^11        (when the host is non-singular).
# For the near-star, G_hub = 3/(4s) and R = (4s+3)/(4(s+1)); at the tie s=5, R = 23/24 -- the exceptional
# prime 23 is the numerator of the resonance condition (the arithmetic tie in scattering language).
# CAVEAT: the factorization degenerates when the host D+iA is singular (a zero mode = itself a resonance);
# the exact Phi always lives in rooted_phi.

def host_green_diagonal(n, edges):
    """Diagonal of the host Green's function G_vv = [(D+iA)^{-1}]_vv (complex), or None if singular."""
    G = _graph(n, edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    H0 = np.diag([G.degree(v) for v in range(n)]).astype(complex) + 1j * A
    if abs(np.linalg.det(H0)) < 1e-12:
        return None
    return np.diag(np.linalg.inv(H0))


def friedel_response(n, edges, root):
    """The Friedel impurity response R(root) = (1 + G_rr) * deg_r/(deg_r+1) -- the sole carrier of the
    root-dependence of Phi^11.  Returns None if the host is singular."""
    g = host_green_diagonal(n, edges)
    if g is None:
        return None
    G = _graph(n, edges)
    d = G.degree(root)
    return (1 + g[root]) * d / (d + 1)


def friedel_phase_shift(n, edges, root):
    """The impurity phase shift delta = arg(1 + G_rr) (Friedel).  Real host Green's function (as at a
    symmetric hub) => delta = 0 = an on-resonance non-scattering response.  None if host singular."""
    g = host_green_diagonal(n, edges)
    if g is None:
        return None
    import cmath
    return cmath.phase(1 + g[root])
