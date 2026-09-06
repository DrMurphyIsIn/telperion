# tests/test_arb_enclosure.py
import pytest
pytest.importorskip("flint")

from fractions import Fraction
import mpmath
from telperion.arb_enclosure import enclose_constant, EnclosureRecord


def _contains(lohi, val):
    lo, hi = lohi
    return float(lo) <= val <= float(hi)


def test_pi_enclosure_contains_oracle():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("pi", prec_bits=300)
    assert lo <= hi
    assert _contains((lo, hi), float(mpmath.pi))


def test_zeta_half_enclosure_contains_oracle():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("zeta(1/2)", prec_bits=300)
    assert _contains((lo, hi), float(mpmath.zeta(mpmath.mpf("0.5"))))


def test_gamma_quarter_enclosure():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("gamma(1/4)", prec_bits=300)
    assert _contains((lo, hi), float(mpmath.gamma(mpmath.mpf("0.25"))))


def test_width_shrinks_with_precision():
    lo1, hi1 = enclose_constant("pi", prec_bits=100)
    lo2, hi2 = enclose_constant("pi", prec_bits=300)
    assert (hi2 - lo2) < (hi1 - lo1)


def test_returns_fractions_outward():
    lo, hi = enclose_constant("e", prec_bits=200)
    assert isinstance(lo, Fraction) and isinstance(hi, Fraction)
    import mpmath as mp
    mp.mp.dps = 80
    assert _contains((lo, hi), float(mp.e))


def test_record_roundtrip():
    lo, hi = enclose_constant("pi", prec_bits=200)
    rec = EnclosureRecord(spec="pi", prec_bits=200, lo=lo, hi=hi, radius=(hi - lo) / 2)
    d = rec.to_dict()
    assert d["spec"] == "pi" and Fraction(d["lo"]) == lo
