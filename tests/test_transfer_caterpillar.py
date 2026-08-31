"""Tests for the exact spine-transfer recurrence on length-2-arm caterpillars.

The CORE check is exact: `Z_recurrence(arms) == rho(*caterpillar_edges(arms))` as `Fraction`
over a spread of caterpillars (single-hub near-star, both spine endpoints, interior hubs,
zero-arm hubs, and random small lists).  The Perron path is checked two ways: the uniform
transfer matrix's top eigenvalue matches the exact per-hub growth ratio of a long uniform
caterpillar to ~1e-9, and the per-vertex free energy `F(a)` has its interior maximum at `a = 7`
(`~0.205098`).  conjecture1_proved = False.
"""
import math
import random
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.matching_free_energy import rho, near_star_edges  # noqa: E402
from telperion.transfer_caterpillar import (  # noqa: E402
    TransferCaterpillarCertificate,
    Z_recurrence,
    arm_balance_delta_g,
    caterpillar_edges,
    free_energy,
    hub_degrees,
    perron_eigenvalue,
    two_hub_Z,
    uniform_transfer_matrix,
)

_FIXED = [
    [3], [7], [6], [2],
    [4, 4], [3, 4, 3], [7, 7, 7], [2, 5, 2, 5], [6, 6, 6, 6],
    [1, 1], [3, 0, 3], [0, 0, 3], [5, 0, 0, 5], [2, 1, 4, 1, 2],
]


def _random_arms(seed, n):
    rng = random.Random(seed)
    out = []
    for _ in range(n):
        arms = [rng.randint(0, 6) for _ in range(rng.randint(1, 5))]
        if sum(arms) > 0:
            out.append(arms)
    return out


def test_recurrence_equals_rho_exact_fixed():
    """CORE: transfer recurrence == rho exactly (Fraction) on the fixed caterpillar family."""
    for arms in _FIXED:
        n, edges = caterpillar_edges(arms)
        r = rho(n, edges)
        z = Z_recurrence(arms)
        assert isinstance(z, Fr)
        assert z == r, f"arms={arms}: rho={r} != Z_recurrence={z}"


def test_recurrence_equals_rho_exact_random():
    """CORE: transfer recurrence == rho exactly on 60 random small caterpillars."""
    for arms in _random_arms(seed=20260830, n=60):
        n, edges = caterpillar_edges(arms)
        assert Z_recurrence(arms) == rho(n, edges), f"mismatch on arms={arms}"


def test_single_hub_is_near_star():
    """A single-hub caterpillar T([s]) is the near-star N(0,s); rho == (4/3)(3/2)^s."""
    for s in range(1, 9):
        n, edges = caterpillar_edges([s])
        assert (n, edges) == near_star_edges(s) or rho(n, edges) == rho(*near_star_edges(s))
        assert Z_recurrence([s]) == Fr(4, 3) * Fr(3, 2) ** s


def test_hub_degrees_positions():
    """Hub degree = arms + spine-neighbour count (0 lone, 1 endpoint, 2 interior)."""
    assert hub_degrees([5]) == [5]                       # lone hub: no spine neighbour
    assert hub_degrees([3, 4]) == [4, 5]                 # both endpoints: +1
    assert hub_degrees([2, 5, 2]) == [3, 7, 3]           # interior hub: +2


def test_certificate_check():
    """The frozen certificate re-verifies recurrence == rho with no mismatches."""
    cert = TransferCaterpillarCertificate()
    assert cert.mismatches() == []
    assert cert.check() is True


def test_transfer_matrix_is_exact_rational():
    """Uniform transfer matrix entries are exact Fractions."""
    T = uniform_transfer_matrix(7)
    for row in T:
        for entry in row:
            assert isinstance(entry, Fr)


def test_perron_matches_per_hub_growth():
    """lam(a) equals the exact per-hub growth ratio Z([a]*M)/Z([a]*(M-1)) to ~1e-9."""
    for a in [3, 5, 7, 10]:
        _, _, _, lam = perron_eigenvalue(a)
        M = 300
        zM = Z_recurrence([a] * M)
        zM1 = Z_recurrence([a] * (M - 1))
        log_ratio = (math.log(int(zM.numerator)) - math.log(int(zM.denominator))
                     - math.log(int(zM1.numerator)) + math.log(int(zM1.denominator)))
        assert abs(log_ratio - math.log(lam)) < 1e-9, f"a={a}"


def test_free_energy_matches_long_caterpillar():
    """F(a) = log(lam)/(2a+1) matches (1/n) log rho of a long uniform caterpillar (a=7) to ~1e-9.

    Uses the per-hub ratio (boundary-free) as the n->inf limit of (1/n) log rho.
    """
    a = 7
    M = 300
    zM = Z_recurrence([a] * M)
    zM1 = Z_recurrence([a] * (M - 1))
    log_lam_numeric = (math.log(int(zM.numerator)) - math.log(int(zM.denominator))
                       - math.log(int(zM1.numerator)) + math.log(int(zM1.denominator)))
    F_numeric = log_lam_numeric / (2 * a + 1)
    assert abs(free_energy(a) - F_numeric) < 1e-9


def test_two_hub_closed_form_equals_rho():
    """CLOSED FORM Z(T(a,b)) = (3/2)^(a+b-2)((4a+3)(4b+3)+9)/(4(a+1)(b+1)) == rho on the 0..8 grid."""
    for a in range(0, 9):
        for b in range(0, 9):
            n, edges = caterpillar_edges([a, b])
            assert two_hub_Z(a, b) == rho(n, edges), f"closed form != rho at ({a},{b})"
    assert two_hub_Z(0, 0) == Fr(2)                        # T(0,0) = P_2


def test_arm_balance_delta_g_identity_and_sign():
    """arm_balance_delta_g == the factored 2(a-b-1)(2a+2b-1)/(a(a+1)(b+1)(b+2)), and it equals the
    true g-difference from the closed form; strictly > 0 exactly for a >= b+2, == 0 at a = b+1."""
    def g(a, b):
        a, b = Fr(a), Fr(b)
        return ((4 * a + 3) * (4 * b + 3) + 9) / ((a + 1) * (b + 1))
    for a in range(2, 12):
        for b in range(0, a):
            got = arm_balance_delta_g(a, b)
            assert got == g(a - 1, b + 1) - g(a, b), f"identity fails at ({a},{b})"
            if a >= b + 2:
                assert got > 0, f"balancing must strictly increase Z at ({a},{b})"
            if a == b + 1:
                assert got == 0, f"balanced tie must be flat at ({a},{b})"


def test_arm_balance_matches_actual_Z_move():
    """The toward-balance move strictly raises the true Z (via rho), confirming delta_g's sign drives Z."""
    for a in range(2, 10):
        for b in range(0, a - 1):                          # a >= b+2
            n0, e0 = caterpillar_edges([a, b])
            n1, e1 = caterpillar_edges([a - 1, b + 1])
            assert rho(n1, e1) > rho(n0, e0), f"Z(T({a-1},{b+1})) !> Z(T({a},{b}))"


def test_free_energy_interior_max_at_7():
    """F(a) is unimodal with interior maximum at a=7, F(7) ~ 0.205098 (= logrho*)."""
    cert = TransferCaterpillarCertificate()
    table = cert.free_energy_table(3, 12)
    best_a = max(table, key=table.get)
    assert best_a == 7, f"interior max at a={best_a}, table={table}"
    assert abs(table[7] - 0.205098) < 1e-5
    # strictly increasing up to 7, strictly decreasing after
    for a in range(3, 7):
        assert table[a] < table[a + 1]
    for a in range(7, 12):
        assert table[a] > table[a + 1]
