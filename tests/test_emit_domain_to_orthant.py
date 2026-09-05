"""domain_to_orthant reparametrizes a simplicial cone to the orthant, round-trips the
Kelmans assisted-merge cert, and rejects domains that don't force positivity."""
import sympy as sp
import pytest

from telperion.emit_domain_to_orthant import (
    domain_to_orthant_cert,
    build_slack_substitution,
)


def test_slack_substitution_simplicial_chain():
    pA, pB = sp.symbols("pA pB")
    slacks, subs, exprs = build_slack_substitution([(1, pB), (pB, pA)])
    t0, t1 = slacks
    # pB = 1 + t0 ; pA = pB + t1 = 1 + t0 + t1
    assert sp.expand(subs[pB] - (1 + t0)) == 0
    assert sp.expand(subs[pA] - (1 + t0 + t1)) == 0
    assert sp.expand(exprs[0] - (pB - 1)) == 0
    assert sp.expand(exprs[1] - (pA - pB)) == 0


def test_assisted_merge_c0_roundtrip():
    # Known-good assisted-merge c0 slack numerator (r = pA-pB, s = pB-1), all-nonneg.
    r, s = sp.symbols("r s")
    slack_poly = (4212*s**3 + 6318*r*s**2 + 2106*r**2*s + 92178*s**2 + 92178*r*s
                  + 14742*r**2 + 151848*s + 75924*r + 41310)
    pA, pB = sp.symbols("pA pB")
    # un-shift into the original variables
    poly_orig = slack_poly.subs({r: pA - pB, s: pB - 1})
    cert = domain_to_orthant_cert(
        "assisted_merge_gain_c0", poly_orig, [(1, pB), (pB, pA)],
    )
    assert cert.startswith("theorem assisted_merge_gain_c0")
    assert "(hpB : 1 ≤ pB)" in cert
    assert "(hpA : pB ≤ pA)" in cert
    assert "nlinarith [" in cert
    assert "sub_nonneg.mpr hpB" in cert and "sub_nonneg.mpr hpA" in cert


def test_two_hub_independent_lower_bounds():
    # Two independent constraints pA >= 1, pB >= 1 (a product cone, not a chain).
    pA, pB = sp.symbols("pA pB")
    cert = domain_to_orthant_cert("prod_pos", pA * pB, [(1, pA), (1, pB)])
    assert "(hpA : 1 ≤ pA)" in cert and "(hpB : 1 ≤ pB)" in cert
    assert "(0:ℝ) < pA*pB" in cert


def test_rejects_domain_that_does_not_force_positivity():
    # a*b - 1 is NOT > 0 on a,b >= 1 (it is 0 at a=b=1): constant term after shift is 0.
    a, b = sp.symbols("a b")
    with pytest.raises(ValueError, match="not strictly positive"):
        domain_to_orthant_cert("bad", a * b - 1, [(1, a), (1, b)])


def test_rejects_negative_coefficient_after_shift():
    # a - 2b is negative somewhere on a,b >= 1.
    a, b = sp.symbols("a b")
    with pytest.raises(ValueError, match="negative coefficient"):
        domain_to_orthant_cert("bad2", a - 2 * b + 5, [(1, a), (1, b)])
