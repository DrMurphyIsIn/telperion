"""Tests for the hub-objective engine (the `hub_dom_family` capability core).

Validates (i) exact symbolic `Aobj` closed forms against the known values, and
(ii) Polya domination certificates on the recurring Brualdi-Goldwasser primitives:
the cherry-parity single-vs-multi-hub domination and the near-star arm value.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.hub_objective import (  # noqa: E402
    CHERRY, LONG3, arm, hub_Aobj, hub_dtSub, caterpillar_Aobj, hub_dom_cert,
)

k = sp.Symbol("k", positive=True, integer=True)
m = sp.Symbol("m", positive=True, integer=True)


def cherry_spider(kk):                       # single hub, kk cherries, n = 2*kk+1
    return hub_Aobj([(kk, CHERRY)])


def single_hub_longleg(kk):                  # (kk-1) cherries + 1 long3, n = 2*kk+2
    return hub_Aobj([(kk - 1, CHERRY), (1, LONG3)])


def two_hub(a, b):                           # hubs a+b cherries, spine edge, n = 2*(a+b)+2
    return hub_Aobj([(a, CHERRY)], spine_child=hub_dtSub([(b, CHERRY)]))


def arm_star(K):                             # K load-5 arms (the near-star), n = 1+11K
    return hub_Aobj([(K, arm(5))])


def test_cherry_spider_closed_form():
    # exact symbolic (4/3)(3/2)^k, and concrete values
    assert sp.simplify(cherry_spider(k) - sp.Rational(4, 3) * sp.Rational(3, 2) ** k) == 0
    assert cherry_spider(3) == sp.Rational(9, 2)          # n=7
    assert cherry_spider(5) == sp.Rational(81, 8)         # n=11, =10.125


def test_near_star_exact_value():
    # matches the Lean-formalized nearstar_arms_Aobj: (26/23)(621/64)^K
    for K in range(1, 5):
        assert sp.simplify(arm_star(K) - sp.Rational(26, 23) * sp.Rational(621, 64) ** K) == 0
    assert arm_star(1) == sp.Rational(351, 32)            # n=12, =10.96875


def test_multihub_values_match_enumeration():
    assert two_hub(2, 2) == sp.Rational(65, 8)            # n=10, =8.125 (enum max)
    assert single_hub_longleg(4) == sp.Rational(513, 64)  # n=10, =8.015625
    assert two_hub(2, 3) == sp.Rational(783, 64)          # n=12, =12.234375


def test_cherry_parity_domination_certified():
    # even n: two-hub (m,m) dominates single-hub-with-long-leg (2m), all m -> Polya cert
    A = single_hub_longleg(2 * m)     # n = 4m+2
    B = two_hub(m, m)                 # n = 4m+2
    ok, cert = hub_dom_cert(A, B, m, 1)
    assert ok, cert
    # the certificate is the numerator t^2*(4t+3) (nonneg) over a nonneg denominator
    assert all(c >= 0 for c in cert["num_coeffs"])
    assert all(c >= 0 for c in cert["den_coeffs"])
    # numeric sanity: strict for m>=2, tie at the degenerate m=1
    assert float(two_hub(2, 2) - single_hub_longleg(4)) > 0
    assert float(two_hub(1, 1) - single_hub_longleg(2)) == 0


def test_caterpillar_builder_agrees_with_two_hub():
    # caterpillar_Aobj generalizes the hand-built two_hub
    assert caterpillar_Aobj([[(2, CHERRY)], [(2, CHERRY)]]) == two_hub(2, 2)
    assert caterpillar_Aobj([[(2, CHERRY)], [(3, CHERRY)]]) == two_hub(2, 3)


def test_false_domination_is_refused():
    # single-hub-long-leg does NOT dominate two-hub (it is the smaller one) -> cert fails
    A = two_hub(m, m)
    B = single_hub_longleg(2 * m)
    ok, _ = hub_dom_cert(A, B, m, 2)
    assert not ok
