"""Tests for the star-of-cherry-brooms S(k,c) skill.

CORE checks (exact Fraction): the closed form Z(S(k,c)) == matching_free_energy.rho on a grid; total(5)=621/64;
the c=5 branch-rate optimum via exact cross-exponentiation; the certificate + Lean emission are well-formed.
S(k,c) asymptotically beats the caterpillar sup 0.205098. conjecture1_proved = False.
"""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.matching_free_energy import rho  # noqa: E402
from telperion.spider_broom import (  # noqa: E402
    BroomOptimumCertificate,
    broom_argmax_c,
    broom_free_energy,
    broom_rate,
    broom_total,
    rate_dominates,
    spider_Z,
    spider_edges,
)


def test_spider_closed_form_equals_rho():
    """CORE: Z(S(k,c)) closed form == rho exactly over k=1..8, c=1..6."""
    for k in range(1, 9):
        for c in range(1, 7):
            n, e = spider_edges(k, c)
            assert spider_Z(k, c) == rho(n, e), f"closed form != rho at S({k},{c})"


def test_broom_total_values():
    """total(c) = (3/2)^(c-1)(4c+3)/(2(c+1)); total(5) = 621/64 (the 'load-5' constant)."""
    assert broom_total(5) == Fr(621, 64)
    assert broom_total(4) == Fr(513, 80)
    assert broom_total(6) == Fr(6561, 448)


def test_c5_is_branch_rate_argmax():
    """c=5 maximizes the branch rate total(c)^(1/(2c+1)) over a wide window."""
    assert broom_argmax_c(1, 12) == 5
    # strict against both neighbors and further competitors, via exact cross-exponentiation
    for c in (2, 3, 4, 6, 7, 8):
        lhs, rhs, holds = rate_dominates(5, c)
        assert holds, f"rate(5) !> rate({c})"
        # cross-exponent identity: rate(5)>rate(c) <=> total(5)^(2c+1) > total(c)^11
        assert lhs == broom_total(5) ** (2 * c + 1)
        assert rhs == broom_total(c) ** (2 * 5 + 1)


def test_beats_caterpillar_density():
    """The S(k,5) asymptotic density exceeds the caterpillar sup 0.205098 (and every c>=3 does)."""
    assert broom_free_energy(5) > 0.205098
    assert abs(broom_free_energy(5) - 0.206586) < 1e-5
    for c in (3, 4, 5, 6):
        assert broom_free_energy(c) > 0.205098


def test_density_converges_from_below_exact():
    """(1/n)log Z(S(k,5)) increases toward F(5) as k grows (exact rho), staying above the caterpillar sup."""
    prev = -1.0
    for k in (20, 50, 100):
        n, e = spider_edges(k, 5)
        z = rho(n, e)
        F = (math.log(int(z.numerator)) - math.log(int(z.denominator))) / n
        assert F > prev, "density should increase with k"
        assert F > 0.205098
        prev = F
    assert prev < broom_free_energy(5)                    # finite-k below the k->inf limit


def test_certificate_and_lean():
    """The optimum certificate checks exactly and emits a well-formed norm_num Lean module."""
    cert = BroomOptimumCertificate()
    assert cert.check() is True
    mod = cert.lean_module()
    assert "import Mathlib" in mod
    assert "namespace BGBroomOptimum" in mod and "end BGBroomOptimum" in mod
    assert mod.count("by norm_num") == len(cert.competitors)
    # a broken certificate must refuse to emit
    bad = BroomOptimumCertificate(c_star=2, competitors=(5,))   # rate(2) < rate(5): claim false
    assert bad.check() is False
