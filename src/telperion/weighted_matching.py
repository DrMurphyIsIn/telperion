"""Weighted matching generating polynomial — the VDB-weighted monomer-dimer coefficient vector.

`matching_free_energy.rho(n, edges)` computes only the value `Z(T) = per(L)/prod(deg) =
sum_{matchings M} prod_{v matched} 1/d_v = sum_k Z_k`.  For the combinatorial extremality program
(Brualdi-Goldwasser route b) we need the FULL coefficient vector

    M(T, t) = sum_{k>=0} Z_k t^k,   Z_k = sum_{k-matchings M} prod_{(u,v) in M} 1/(d_u d_v),

the vertex-degree-based (VDB) weighted matching generating polynomial (weight phi(i,j) = 1/(i j), the
`c = -1` / decreasing case of the Cambie-Wagner VDB-weighted Hosoya family, arXiv:2209.03408).  Z_k is the
`k`-th weighted matching number; `Z_1 = sum_edges 1/(d_u d_v)` is the (reciprocal) Randic index, `M(T,1) = Z`.

Coefficientwise domination `Z_k(T) <= Z_k(T')` for all k underlies the GTS / leaf-exchange competitor-exclusion
step (P4/P1).  Computed EXACTLY in linear time by the same rooted matching DP as `rho`, carrying polynomials
in `t` instead of scalars.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def _padd(p, q):
    r = [Fr(0)] * max(len(p), len(q))
    for i, x in enumerate(p):
        r[i] += x
    for i, x in enumerate(q):
        r[i] += x
    return r


def _pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x == 0:
            continue
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def matching_generating_poly(n, edges):
    """Return [Z_0, Z_1, ..., Z_kmax], the VDB-weighted matching generating polynomial coefficients
    (exact Fraction).  Z_k = sum over k-matchings of prod_{(u,v) in M} 1/(d_u d_v).  Linear-time rooted DP.

    dp[v] = (A_v, B_v): A_v = generating poly of matchings of v's subtree with v UNMATCHED (to a child),
    B_v = with v matched to one child.  A_v = prod_c (A_c + B_c);  B_v = sum_c (1/(d_v d_c)) t * A_c *
    prod_{c'!=c} (A_{c'}+B_{c'}).  The tree's poly is A_root + B_root.
    """
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    deg = {v: len(adj[v]) for v in range(n)}
    if n == 1:
        return [Fr(1)]
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
    A = {}
    B = {}
    for v in reversed(order):                             # postorder
        kids = [c for c in adj[v] if c != parent[v]]
        tot = [Fr(1)]
        for c in kids:
            tot = _pmul(tot, _padd(A[c], B[c]))
        Av = tot
        Bv = [Fr(0)]
        for i, c in enumerate(kids):
            term = [Fr(0), Fr(1, deg[v]) * Fr(1, deg[c])]  # (1/(d_v d_c)) t
            term = _pmul(term, A[c])
            for j, c2 in enumerate(kids):
                if j != i:
                    term = _pmul(term, _padd(A[c2], B[c2]))
            Bv = _padd(Bv, term)
        A[v] = Av
        B[v] = Bv
    poly = _padd(A[root], B[root])
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def weighted_Z(n, edges):
    """Z(T) = M(T, 1) = sum_k Z_k.  Equals matching_free_energy.rho (cross-checked in tests)."""
    return sum(matching_generating_poly(n, edges))


@dataclass(frozen=True)
class CoefficientwiseDomination:
    """Certifies Z_k(T_small) <= Z_k(T_big) for EVERY k (weighted matching numbers), the input to the
    GTS / leaf-exchange competitor-exclusion step.  `.check()` verifies exactly; `holds` records the verdict
    and (if it fails) the first k where domination breaks."""

    name: str
    poly_small: tuple
    poly_big: tuple

    def check(self) -> bool:
        ps, pb = list(self.poly_small), list(self.poly_big)
        K = max(len(ps), len(pb))
        ps += [Fr(0)] * (K - len(ps))
        pb += [Fr(0)] * (K - len(pb))
        return all(pb[k] >= ps[k] for k in range(K))

    def first_violation(self):
        ps, pb = list(self.poly_small), list(self.poly_big)
        K = max(len(ps), len(pb))
        ps += [Fr(0)] * (K - len(ps))
        pb += [Fr(0)] * (K - len(pb))
        for k in range(K):
            if pb[k] < ps[k]:
                return k, ps[k], pb[k]
        return None
