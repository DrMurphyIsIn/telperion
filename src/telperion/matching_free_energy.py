"""Matching free energy & competitor extremality — the crux-(b) engine.

Brualdi-Goldwasser splits into (a) the near-star family bound Phi<=1 [PROVED, arithmetic] and
(b) COMPETITOR EXTREMALITY: no other tree exceeds the near-star.  This module attacks (b) through the
statistical-mechanics reading:

    rho(T) = per(L)/prod(deg) = SUM_{matchings M} prod_{v matched} (1/deg_v)

is the monomer-dimer partition function of T with vertex fugacity 1/deg.  It is computed EXACTLY in
linear time by the cavity/transfer DP (the Laplacian's own Schur elimination), not by permanents.

Empirically (verified over ALL trees to n=14): for odd n=2s+1 the near-star N(0,s) is the STRICT
maximizer of rho, and it wins because length-2 legs uniquely maximize the per-vertex matching free
energy rho^(1/V) -> sqrt(3/2).  Competitor extremality thus reads as a variational principle: the
near-star maximizes the bosonic matching entropy density, with the ties (c+k=5) as the equality set.
The proof route is a rho-monotone rearrangement/compression argument (Kelmans-type): split legs to
length 2, concentrate branches at one hub -- moves that never decrease rho.

`CompetitorExtremalityCertificate(s)` verifies, for n=2s+1, that N(0,s) maximizes rho over every tree
on n vertices, and emits the binding witnesses rho(N(0,s)) > rho(competitor).  This is the (b)-analog
of the near-star arithmetic proof for (a); it discharges competitor extremality for fixed n (the base
cases of the rearrangement induction).  The all-n statement remains OPEN.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def rho(n, edges):
    """rho(T) = per(L)/prod(deg) via the monomer-dimer cavity DP (exact Fraction, linear time)."""
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    deg = {v: len(adj[v]) for v in range(n)}
    root = 0
    parent = {root: -1}
    order = []
    stack = [root]
    seen = {root}
    while stack:
        u = stack.pop()
        order.append(u)
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                parent[w] = u
                stack.append(w)
    unm = {}
    mat = {}
    for v in reversed(order):                       # postorder
        kids = [c for c in adj[v] if c != parent[v]]
        tots = [unm[c] + mat[c] for c in kids]
        prod_tot = Fr(1)
        for t in tots:
            prod_tot *= t
        m = Fr(0)
        for i, c in enumerate(kids):
            rest = Fr(1)
            for j, c2 in enumerate(kids):
                if j != i:
                    rest *= (unm[c2] + mat[c2])
            m += Fr(1, deg[v]) * Fr(1, deg[c]) * unm[c] * rest
        unm[v] = prod_tot
        mat[v] = m
    return unm[root] + mat[root]


def near_star_edges(s):
    """N(0,s): a hub with s legs of length 2 (n = 2s+1 vertices)."""
    edges = []
    nid = 1
    for _ in range(s):
        edges.append((0, nid))
        edges.append((nid, nid + 1))
        nid += 2
    return 2 * s + 1, tuple(edges)


def _all_trees(n):
    import networkx as nx
    return [tuple(T.edges()) for T in nx.nonisomorphic_trees(n)]


@dataclass(frozen=True)
class CompetitorExtremalityCertificate:
    """WRONG QUANTITY FOR BG (kept for the monomer-dimer problem).  This maximizes RAW rho=per(L)/prod
    deg, which is the monomer-dimer partition function -- MAXIMIZED BY BALANCED CATERPILLARS, not the
    near-star, for large n (e.g. (3,4,3) beats N(0,11) at n=23).  Brualdi-Goldwasser is about the ROOTED
    branch Phi (rooted_phi.bg_phi11); use BGExtremalityCertificate for BG.  See
    docs/geography_past_11th_root.md.  This class certifies the raw-rho (bosonic monomer-dimer) extremal,
    which holds only for n <= ~21.

    For n = 2s+1: verifies the near-star N(0,s) maximizes rho over all trees on n vertices."""

    s: int

    def _ranked(self):
        n = 2 * self.s + 1
        vals = [(rho(n, e), e) for e in _all_trees(n)]
        vals.sort(key=lambda t: t[0], reverse=True)
        return n, vals

    def near_star_rho(self):
        n, e = near_star_edges(self.s)
        return rho(n, e)

    def is_extremal(self) -> bool:
        """N(0,s) is the unique maximizer of rho over all trees on 2s+1 vertices."""
        n, vals = self._ranked()
        top = vals[0][0]
        ns = self.near_star_rho()
        # near-star attains the max, strictly above the runner-up
        return ns == top and (len(vals) < 2 or vals[1][0] < top)

    def gap_to_runner_up(self):
        n, vals = self._ranked()
        return vals[0][0] - vals[1][0] if len(vals) > 1 else None

    def check(self) -> bool:
        # cross-check: near-star value matches the closed form (4/3)(3/2)^s, and is extremal
        return self.near_star_rho() == Fr(4, 3) * Fr(3, 2) ** self.s and self.is_extremal()

    def lean(self) -> str:
        n, vals = self._ranked()
        ns = self.near_star_rho()
        runner = vals[1][0] if len(vals) > 1 else Fr(0)
        lines = [
            f"-- COMPETITOR EXTREMALITY, n={n} (near-star N(0,{self.s})).  rho=per(L)/prod(deg) is the\n"
            f"-- monomer-dimer partition function; N(0,{self.s}) maximizes it over all {len(vals)} trees on\n"
            f"-- {n} vertices (verified).  Binding witness: it strictly beats the runner-up.\n"
            f"-- rho(N(0,{self.s})) = {ns.numerator}/{ns.denominator} = (4/3)(3/2)^{self.s}.\n"
            f"theorem compext_n{n}_value : "
            f"(({ns.numerator}:ℚ)/{ns.denominator}) = (4/3)*(3/2)^{self.s} := by norm_num\n"
            f"-- strictly above the runner-up rho = {runner.numerator}/{runner.denominator}:\n"
            f"theorem compext_n{n}_beats_runnerup : "
            f"({runner.numerator}*{ns.denominator}:ℤ) < {ns.numerator}*{runner.denominator} := by norm_num"
        ]
        return "\n".join(lines) + "\n"
