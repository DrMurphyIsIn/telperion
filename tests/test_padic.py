"""p-adic valuation engine + certificate tests."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    ValuationFact,
    padic_decompose,
    padic_val,
    padic_val_frac,
)


def test_padic_val_basic():
    assert padic_val(621, 23) == 1        # 621 = 27 * 23
    assert padic_val(64, 23) == 0
    assert padic_val(23 ** 11, 23) == 11
    assert padic_val(529, 23) == 2        # 23^2


def test_padic_decompose_roundtrip():
    for n in (621, 23 ** 5 * 7, 1000, -46):
        k, n0 = padic_decompose(n, 23)
        assert 23 ** k * n0 == n
        assert n0 % 23 != 0


def test_padic_val_frac():
    # v_23(N/D) = v_23(N) - v_23(D); the crux quantity for Phi^11 = N/D
    assert padic_val_frac(Fraction(64, 621), 23) == -1     # one 23 in denominator
    assert padic_val_frac(Fraction(1, 23 ** 11), 23) == -11
    assert padic_val_frac(Fraction(7, 5), 23) == 0


def test_padic_val_zero_raises():
    with pytest.raises(ValueError):
        padic_val(0, 23)


def test_valuation_fact_check_and_lean():
    f = ValuationFact("v23_621", 621, 23, 1)
    assert f.check()
    assert not ValuationFact("bad", 621, 23, 2).check()   # 23^2 does not divide 621
    lean = f.lean()
    assert "23 ∣ 621" in lean and "529 ∣ 621" in lean     # p^k | n and not p^(k+1) | n
