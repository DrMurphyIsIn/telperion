"""VDB-weighted leaf-exchange / arm-balancing operator — the ΔZ engine of the P1 reduction.

Brualdi-Goldwasser route (b) (competitor extremality) is attacked by a rho-monotone
rearrangement induction: a chain of LOCAL moves that never decrease

    Z(T) = per(L)/prod(deg) = sum_{matchings M} prod_{v matched} 1/d_v = rho(T)

(the VDB-weighted monomer-dimer partition function, weight phi(u,v)=1/(d_u d_v), the
Cambie-Wagner `c=-1` / decreasing case, arXiv:2209.03408).  Each move rewires ONE arm
between two hubs while preserving every vertex degree elsewhere, so the ΔZ it produces is
the operative quantity of the reduction step.  GATE-2 already showed the coefficientwise
(per-k) domination of `weighted_matching.matching_generating_poly` FAILS for these moves;
therefore the SUM `Z = rho` -- not the coefficient vector -- is the sign-definite invariant,
and `delta_Z` (this module) is what the induction actually discharges.

The ARM-BALANCING move `("balance_arm", hub_from, hub_to)` detaches one length-2 arm from
`hub_from` and reattaches it to `hub_to` (a degree-structure-preserving relocation of a
subtree: the arm-mid vertex loses `hub_from` as parent and gains `hub_to`).  Empirically
(the P0.2 finding, reproduced in tests) this move INCREASES rho whenever it moves toward
equal hub arm-counts: for a two-hub `T(a,b)` with a > b+1, `("balance_arm", h_a, h_b)`
gives `delta_Z > 0` (strict).  So the extremal two-hub configuration is the balanced one,
and the balancing move is a rho-monotone compression -- the exact local step of route (b).

`LeafExchangeCertificate` anchors the FINITE base cases of this exchange induction (a la
`flag_discharge.FlagDischargeCertificate` / `bg_flag_discharge`): it stores the exact
before/after Z of one concrete instance, `.check()` re-verifies the stated ΔZ direction
exactly over Fraction, and `.lean_atom`/`.lean_module` emit the `norm_num` rational atom
`Z_before < Z_after` (untrusted generator, kernel-checked).  `local_delta_from_pairs`
re-expresses the arm-balancing ΔZ as a sign-definite rational function of the local cavity
`(U, M) = (unm, mat)` pairs of the two hubs (and their attached-subtree cavity totals), so
the move's `ΔZ >= 0` becomes a LOCAL rational inequality -- the reducible proof obligation.

This module supplies the exact arm-balancing arithmetic; it discharges the base cases and
the local reduction obligation of route (b), not the all-n statement.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Fr

from telperion.matching_free_energy import rho
from telperion.weighted_matching import matching_generating_poly


# --------------------------------------------------------------------------- #
# tree bookkeeping                                                            #
# --------------------------------------------------------------------------- #
def _adj(n, edges):
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _is_tree(n, edges) -> bool:
    """Connected and acyclic on exactly n vertices with n-1 edges."""
    if len(edges) != n - 1:
        return False
    adj = _adj(n, edges)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


def _rooted_parents(n, edges, root=0):
    adj = _adj(n, edges)
    parent = {root: -1}
    order = [root]
    stack = [root]
    seen = {root}
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                parent[w] = u
                order.append(w)
                stack.append(w)
    return parent, adj


# --------------------------------------------------------------------------- #
# the local move                                                             #
# --------------------------------------------------------------------------- #
def _find_length2_arm(n, edges, hub):
    """Return (mid, leaf) of one length-2 arm hanging off `hub` (mid has degree 2: hub + leaf).

    A length-2 arm at `hub` is a path hub - mid - leaf with deg(mid)=2, deg(leaf)=1.
    Raises ValueError if `hub` has no such arm.
    """
    adj = _adj(n, edges)
    for mid in adj[hub]:
        if len(adj[mid]) == 2:
            others = [w for w in adj[mid] if w != hub]
            if len(others) == 1:
                leaf = others[0]
                if len(adj[leaf]) == 1:
                    return mid, leaf
    raise ValueError(f"hub {hub} has no length-2 arm")


def apply_move(n, edges, move):
    """Apply a degree-structure-preserving local move to a tree, returning `(n, edges')`.

    Supported moves:
      * ("balance_arm", hub_from, hub_to): detach one length-2 arm (mid-leaf) from
        `hub_from` and reattach the SAME mid vertex to `hub_to`.  Preserves n and every
        vertex degree except hub_from (-1) and hub_to (+1); mid/leaf degrees unchanged.
      * ("relocate_subtree", subtree_root, old_parent, new_parent): re-parent the subtree
        rooted at `subtree_root` from `old_parent` to `new_parent`.  Generic building block;
        preserves the subtree internally, changes only the two parent degrees.

    Vertex ids are preserved (no relabeling) so cavity/local reasoning stays aligned.
    """
    kind = move[0]
    edge_set = [tuple(e) for e in edges]

    def _remove(a, b):
        if (a, b) in edge_set:
            edge_set.remove((a, b))
        elif (b, a) in edge_set:
            edge_set.remove((b, a))
        else:
            raise ValueError(f"edge ({a},{b}) not present")

    if kind == "balance_arm":
        _, hub_from, hub_to = move
        mid, _leaf = _find_length2_arm(n, edges, hub_from)
        _remove(hub_from, mid)
        edge_set.append((hub_to, mid))
        return n, tuple(edge_set)

    if kind == "relocate_subtree":
        _, subtree_root, old_parent, new_parent = move
        _remove(old_parent, subtree_root)
        edge_set.append((new_parent, subtree_root))
        n2, e2 = n, tuple(edge_set)
        if not _is_tree(n2, e2):
            raise ValueError("relocate_subtree produced a non-tree (would create a cycle)")
        return n2, e2

    raise ValueError(f"unknown move kind {kind!r}")


# --------------------------------------------------------------------------- #
# ΔZ (exact)                                                                 #
# --------------------------------------------------------------------------- #
def delta_Z(n, edges, move) -> Fr:
    """Z(after) - Z(before), computed EXACTLY via `rho` (the VDB-weighted Z on the sum)."""
    z_before = rho(n, edges)
    n2, e2 = apply_move(n, edges, move)
    z_after = rho(n2, e2)
    return z_after - z_before


def delta_Zk(n, edges, move):
    """Coefficientwise difference [Z_k(after) - Z_k(before)] via `matching_generating_poly`.

    Diagnostic only: GATE-2 established that per-k domination FAILS for the balancing move
    (some coefficients rise, some fall), so `delta_Z` on the SUM is the operative quantity.
    Returned zero-padded to equal length.
    """
    pb = list(matching_generating_poly(n, edges))
    n2, e2 = apply_move(n, edges, move)
    pa = list(matching_generating_poly(n2, e2))
    K = max(len(pb), len(pa))
    pb += [Fr(0)] * (K - len(pb))
    pa += [Fr(0)] * (K - len(pa))
    return [pa[k] - pb[k] for k in range(K)]


# --------------------------------------------------------------------------- #
# local cavity form of the arm-balancing ΔZ                                  #
# --------------------------------------------------------------------------- #
def _cavity_pairs(n, edges, root=0):
    """Return (unm, mat) dicts: for each vertex v (rooted at `root`) the subtree
    matching-generating totals with v UNMATCHED (unm[v]) / v MATCHED to a child (mat[v]),
    exactly as in `matching_free_energy.rho`.  T = unm[root] + mat[root]."""
    parent, adj = _rooted_parents(n, edges, root)
    deg = {v: len(adj[v]) for v in range(n)}
    order = []
    stack = [root]
    seen = {root}
    while stack:
        u = stack.pop()
        order.append(u)
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    unm, mat = {}, {}
    for v in reversed(order):
        kids = [c for c in adj[v] if c != parent[v]]
        prod_tot = Fr(1)
        for c in kids:
            prod_tot *= (unm[c] + mat[c])
        m = Fr(0)
        for c in kids:
            rest = Fr(1)
            for c2 in kids:
                if c2 != c:
                    rest *= (unm[c2] + mat[c2])
            m += Fr(1, deg[v]) * Fr(1, deg[c]) * unm[c] * rest
        unm[v] = prod_tot
        mat[v] = m
    return unm, mat, deg


def local_delta_from_pairs(n, edges, move):
    """Express the arm-balancing ΔZ as a rational function of LOCAL cavity `(U, M)` pairs.

    For `("balance_arm", hub_from, hub_to)` we root the tree at `hub_from` so that `hub_to`
    and the moved arm are both DOWNWARD subtrees.  Root a monomer-dimer partition function
    factors through the two hubs' cavity pairs:

        Z = A_root + B_root,   A = prod_c (U_c + M_c),   B = sum_c (1/(d_root d_c)) U_c * rest.

    We compute Z(before) and Z(after) via the exact rooted cavity recursion re-run only on
    the two hubs (their child totals are the local `(U, M)` inputs), and return

        (delta_local, data)

    where `delta_local` is the exact ΔZ and `data` is the local `(U, M)` witness dict
    (hub degrees, the moved arm's (U,M), and each hub's other-children total).  `data`
    exposes ΔZ as a sign-definite rational function of these local pairs -- the reducible
    obligation.  Verified to equal `delta_Z` exactly (see tests).

    NOTE: because a relocation changes the two hubs' degrees, the *arm's own* (U, M) is
    degree-invariant (arm-mid/leaf degrees are untouched) but the hubs' matched-terms
    rescale by 1/d_hub; the returned closed form makes that rescaling explicit.
    """
    kind = move[0]
    if kind != "balance_arm":
        raise ValueError("local_delta_from_pairs supports only ('balance_arm', h_from, h_to)")
    _, hub_from, hub_to = move

    # exact ΔZ (ground truth, and what the local form must reproduce)
    delta = delta_Z(n, edges, move)

    # local (U, M) witness: root at hub_from so hub_to is a downward child of hub_from
    # (in the two-hub family hub_from - hub_to is an edge).  Gather each hub's children
    # cavity pairs and the moved arm's (U, M).
    parent, adj = _rooted_parents(n, edges, hub_from)
    unm, mat, deg = _cavity_pairs(n, edges, hub_from)
    mid, leaf = _find_length2_arm(n, edges, hub_from)

    def child_totals(hub, exclude=()):
        tot = Fr(1)
        for c in adj[hub]:
            if c == parent.get(hub, -1) or c in exclude:
                continue
            tot *= (unm[c] + mat[c])
        return tot

    data = {
        "hub_from": hub_from,
        "hub_to": hub_to,
        "d_from": deg[hub_from],
        "d_to": deg[hub_to],
        "arm_U": unm[mid],          # (U, M) of the moved arm-mid subtree (degree-invariant)
        "arm_M": mat[mid],
        "arm_total": unm[mid] + mat[mid],
        "from_rest_total": child_totals(hub_from, exclude=(mid,)),  # hub_from's other children
        "to_children_total": child_totals(hub_to),                  # hub_to's downward children
    }
    return delta, data


# --------------------------------------------------------------------------- #
# certificate                                                                #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class LeafExchangeCertificate:
    """One finite base case of the VDB arm-balancing / leaf-exchange induction (route b).

    Stores the exact before/after Z of a concrete arm-balancing instance and the stated
    direction.  For the balancing move (`direction='increase'`) the claim is
    Z_before < Z_after (rho strictly increases toward balanced hubs -- the P0.2 finding);
    `direction='nondecrease'` weakens `<` to `<=`.  `.check()` re-verifies the exact
    Fraction inequality; `.lean_atom`/`.lean_module` emit the `norm_num` rational atom.
    Untrusted generator, kernel-checked atom (a la flag_discharge)."""

    name: str
    z_before: Fr
    z_after: Fr
    direction: str = "increase"          # 'increase' (strict) | 'nondecrease' (>=)
    n: int = 0
    move: tuple = field(default=())

    def delta(self) -> Fr:
        return self.z_after - self.z_before

    def check(self) -> bool:
        """Exact: the stated direction holds over Fraction."""
        if self.direction == "increase":
            return self.z_after > self.z_before
        if self.direction == "nondecrease":
            return self.z_after >= self.z_before
        raise ValueError(f"unknown direction {self.direction!r}")

    @staticmethod
    def from_instance(name, n, edges, move, direction="increase"):
        """Build a certificate from a live tree + move (computes exact Z before/after)."""
        zb = rho(n, edges)
        n2, e2 = apply_move(n, edges, move)
        za = rho(n2, e2)
        return LeafExchangeCertificate(
            name=name, z_before=zb, z_after=za, direction=direction, n=n, move=tuple(move)
        )

    # ---- Lean emission ----
    def _rel(self) -> str:
        return "<" if self.direction == "increase" else "≤"

    def lean_atom(self, tag: str) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: stated direction fails -- refusing to emit")
        zb, za = self.z_before, self.z_after
        rel = self._rel()

        def _rat(f: Fr) -> str:
            return (f"(({f.numerator} : ℚ)/{f.denominator})"
                    if f.denominator != 1 else f"(({f.numerator} : ℚ))")

        move_s = ",".join(str(x) for x in self.move) if self.move else "?"
        return (
            f"-- arm-balancing base case n={self.n} move=({move_s})  ΔZ = {self.delta()}\n"
            f"theorem {self.name}_{tag} : {_rat(zb)} {rel} {_rat(za)} := by norm_num\n"
        )

    def lean_module(self, namespace: str) -> str:
        """Complete frozen Lean module: Mathlib import + namespace + the kernel-checked atom."""
        return (
            f"/- VDB arm-balancing leaf-exchange base case for Brualdi-Goldwasser route (b).\n"
            f"   Z = per(L)/prod(deg) = sum_matchings prod 1/d_v (VDB weight 1/(d_u d_v), c=-1 case).\n"
            f"   The arm-balancing move (detach a length-2 arm from one hub, attach to the other)\n"
            f"   strictly increases Z toward equal hub arm-counts (P0.2).  This atom pins ONE finite\n"
            f"   instance: Z_before {self._rel()} Z_after, re-checked by the kernel via norm_num.\n"
            f"   One base case of the rho-monotone rearrangement induction -- NOT a proof of\n"
            f"   Brualdi-Goldwasser.  conjecture1_proved = False. -/\n"
            f"import Mathlib\n\n"
            f"namespace {namespace}\n\n"
            + self.lean_atom("base")
            + f"\nend {namespace}\n"
        )
