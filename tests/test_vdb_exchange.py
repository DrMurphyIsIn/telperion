"""Tests for the VDB arm-balancing leaf-exchange operator + certificate (route b).

Verifies (all EXACT, over fractions.Fraction):
  * apply_move produces a valid tree with the intended degree structure;
  * delta_Z equals rho(after) - rho(before) exactly (by construction);
  * arm-balancing toward equal hub counts gives ΔZ > 0 (the P0.2 finding), reproduced
    for two-hub T(a,b) with a > b+1 across several (a,b);
  * LeafExchangeCertificate.check() and its well-formed Lean module;
  * local_delta_from_pairs equals delta_Z exactly on >= 5 instances.

conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import pytest

from telperion.matching_free_energy import rho, near_star_edges
from telperion.vdb_exchange import (
    apply_move,
    delta_Z,
    delta_Zk,
    local_delta_from_pairs,
    LeafExchangeCertificate,
    _is_tree,
    _find_length2_arm,
)


# --------------------------------------------------------------------------- #
# builders                                                                   #
# --------------------------------------------------------------------------- #
def two_hub_edges(a, b):
    """T(a,b): hubs 0,1 joined by an edge; hub 0 has `a` length-2 arms, hub 1 has `b`."""
    edges = [(0, 1)]
    nid = 2
    for _ in range(a):
        edges.append((0, nid)); edges.append((nid, nid + 1)); nid += 2
    for _ in range(b):
        edges.append((1, nid)); edges.append((nid, nid + 1)); nid += 2
    n = 2 + 2 * a + 2 * b
    return n, tuple(edges)


def _deg_multiset(n, edges):
    deg = {i: 0 for i in range(n)}
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    return sorted(deg.values())


# --------------------------------------------------------------------------- #
# apply_move validity + intended structure                                   #
# --------------------------------------------------------------------------- #
def test_balance_arm_produces_valid_tree():
    n, e = two_hub_edges(8, 4)
    n2, e2 = apply_move(n, e, ("balance_arm", 0, 1))
    assert n2 == n
    assert _is_tree(n2, e2)


def test_balance_arm_intended_degree_structure():
    # moving one arm from hub 0 (deg a+1) to hub 1 (deg b+1) gives T(a-1, b+1)
    n, e = two_hub_edges(8, 4)
    n2, e2 = apply_move(n, e, ("balance_arm", 0, 1))
    # T(7,5) should have identical degree multiset to the direct build
    _, e_direct = two_hub_edges(7, 5)
    assert _deg_multiset(n2, e2) == _deg_multiset(*(two_hub_edges(7, 5)))
    # and same exact Z as the canonical T(7,5)
    assert rho(n2, e2) == rho(*two_hub_edges(7, 5))


def test_relocate_subtree_valid_and_degree_preserving():
    # relocate the same arm-mid from hub 0 to hub 1 via the generic move
    n, e = two_hub_edges(6, 6)
    mid, leaf = _find_length2_arm(n, e, 0)
    n2, e2 = apply_move(n, e, ("relocate_subtree", mid, 0, 1))
    assert _is_tree(n2, e2)
    # equivalent to balance_arm here
    n3, e3 = apply_move(n, e, ("balance_arm", 0, 1))
    assert rho(n2, e2) == rho(n3, e3)


def test_relocate_rejects_cycle():
    n, e = two_hub_edges(3, 3)
    # attaching subtree to a vertex already inside it must fail (cycle)
    mid, leaf = _find_length2_arm(n, e, 0)
    with pytest.raises(ValueError):
        apply_move(n, e, ("relocate_subtree", mid, 0, leaf))


# --------------------------------------------------------------------------- #
# delta_Z matches rho(after) - rho(before) exactly                           #
# --------------------------------------------------------------------------- #
@pytest.mark.parametrize("a,b", [(8, 4), (7, 5), (9, 3), (6, 6), (10, 2), (5, 1)])
def test_delta_Z_matches_rho_difference(a, b):
    n, e = two_hub_edges(a, b)
    move = ("balance_arm", 0, 1)
    n2, e2 = apply_move(n, e, move)
    expected = rho(n2, e2) - rho(n, e)
    assert delta_Z(n, e, move) == expected
    assert isinstance(delta_Z(n, e, move), Fr)


# --------------------------------------------------------------------------- #
# arm-balancing toward equal hub counts: ΔZ > 0  (the P0.2 finding)          #
# --------------------------------------------------------------------------- #
@pytest.mark.parametrize("a,b", [(8, 4), (9, 3), (10, 2), (7, 5), (6, 2), (5, 1)])
def test_balancing_increases_Z_strict(a, b):
    # a > b + 1  =>  moving one arm from the fuller hub 0 to hub 1 balances and raises Z
    assert a > b + 1
    n, e = two_hub_edges(a, b)
    d = delta_Z(n, e, ("balance_arm", 0, 1))
    assert d > 0, f"expected ΔZ>0 balancing T({a},{b})->T({a-1},{b+1}), got {d}"


def test_p02_eight_four_to_seven_five():
    # the named P0.2 instance: (8,4) -> (7,5) increases Z
    n, e = two_hub_edges(8, 4)
    before = rho(n, e)
    n2, e2 = apply_move(n, e, ("balance_arm", 0, 1))
    after = rho(n2, e2)
    assert after > before
    assert after == Fr(7105563, 32768)     # rho T(7,5)
    assert before == Fr(2211057, 10240)    # rho T(8,4)


def test_over_balancing_decreases_Z():
    # moving PAST balance (from the emptier hub) should not increase Z: T(6,6)->T(5,7) symmetric = equal;
    # T(5,7): moving from hub 0 (fuller? no, 5<7) toward hub1 unbalances -> ΔZ < 0
    n, e = two_hub_edges(5, 7)
    d = delta_Z(n, e, ("balance_arm", 0, 1))   # 5->4, 7->8 : more unbalanced
    assert d < 0


# --------------------------------------------------------------------------- #
# coefficientwise (delta_Zk) is genuinely mixed-sign (GATE-2)                 #
# --------------------------------------------------------------------------- #
def test_delta_Zk_mixed_sign_gate2():
    n, e = two_hub_edges(8, 4)
    dk = delta_Zk(n, e, ("balance_arm", 0, 1))
    signs = {(1 if x > 0 else (-1 if x < 0 else 0)) for x in dk}
    # some coefficients rise, some fall: per-k domination FAILS -> must use the sum
    assert 1 in signs and -1 in signs
    # yet the SUM (= delta_Z) is strictly positive
    assert sum(dk) == delta_Z(n, e, ("balance_arm", 0, 1))
    assert sum(dk) > 0


# --------------------------------------------------------------------------- #
# certificate                                                                #
# --------------------------------------------------------------------------- #
def test_certificate_check_true_for_balancing_instance():
    n, e = two_hub_edges(8, 4)
    cert = LeafExchangeCertificate.from_instance("bg_balance_84", n, e, ("balance_arm", 0, 1))
    assert cert.check()
    assert cert.delta() > 0
    assert cert.z_before == Fr(2211057, 10240)
    assert cert.z_after == Fr(7105563, 32768)


def test_certificate_nondecrease_direction():
    n, e = two_hub_edges(8, 4)
    cert = LeafExchangeCertificate.from_instance(
        "bg_balance_84_nd", n, e, ("balance_arm", 0, 1), direction="nondecrease"
    )
    assert cert.check()


def test_certificate_refuses_wrong_direction():
    # claim 'increase' on a move that DECREASES Z -> check() False, lean_atom refuses
    n, e = two_hub_edges(5, 7)
    cert = LeafExchangeCertificate.from_instance("bg_bad", n, e, ("balance_arm", 0, 1))
    assert not cert.check()
    with pytest.raises(ValueError):
        cert.lean_atom("base")


def test_lean_module_well_formed():
    n, e = two_hub_edges(8, 4)
    cert = LeafExchangeCertificate.from_instance("bg_balance_84", n, e, ("balance_arm", 0, 1))
    mod = cert.lean_module("BG.VDBExchange")
    assert "import Mathlib" in mod
    assert "namespace BG.VDBExchange" in mod
    assert "end BG.VDBExchange" in mod
    assert ":= by norm_num" in mod
    assert "theorem bg_balance_84_base" in mod
    # exact rationals present, correct strict direction
    assert "2211057" in mod and "10240" in mod
    assert "7105563" in mod and "32768" in mod
    assert "<" in mod


def test_lean_atom_rationals_and_relation():
    n, e = two_hub_edges(6, 2)
    cert = LeafExchangeCertificate.from_instance("bg_balance_62", n, e, ("balance_arm", 0, 1))
    atom = cert.lean_atom("t")
    assert atom.strip().endswith(":= by norm_num")
    assert "ℚ" in atom
    assert "<" in atom   # strict, since balancing increases


# --------------------------------------------------------------------------- #
# local (U, M) cavity form equals delta_Z exactly                            #
# --------------------------------------------------------------------------- #
@pytest.mark.parametrize("a,b", [(8, 4), (9, 3), (7, 5), (10, 2), (6, 2), (5, 1)])
def test_local_delta_from_pairs_matches_delta_Z(a, b):
    n, e = two_hub_edges(a, b)
    move = ("balance_arm", 0, 1)
    delta_local, data = local_delta_from_pairs(n, e, move)
    assert delta_local == delta_Z(n, e, move)
    # local witness exposes the (U, M) pairs of the moved arm + hub totals (all exact)
    assert isinstance(data["arm_U"], Fr) and isinstance(data["arm_M"], Fr)
    assert data["arm_total"] == data["arm_U"] + data["arm_M"]
    assert data["d_from"] == a + 1 and data["d_to"] == b + 1


def test_local_delta_arm_UM_is_length2_arm():
    # a length-2 arm rooted at its mid: mid deg 2, one leaf child (deg 1).
    # U_mid = 1 (mid unmatched: leaf may be unmatched)  -> subtree {leaf} matching-gen = 1
    # M_mid = (1/(d_mid d_leaf)) * U_leaf = (1/(2*1)) * 1 = 1/2
    n, e = two_hub_edges(8, 4)
    _, data = local_delta_from_pairs(n, e, ("balance_arm", 0, 1))
    assert data["arm_U"] == Fr(1)
    assert data["arm_M"] == Fr(1, 2)
    assert data["arm_total"] == Fr(3, 2)


# --------------------------------------------------------------------------- #
# cross-check against near-star closed form (sanity on rho path)             #
# --------------------------------------------------------------------------- #
def test_near_star_consistency():
    n, e = near_star_edges(5)
    assert rho(n, e) == Fr(4, 3) * Fr(3, 2) ** 5
