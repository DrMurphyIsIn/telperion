"""Tests for the multilinear/endpoint-bracketing corner emitter -- BG's actual pattern.

Validates that it regenerates the BG bridge lemmas `linear_nonneg_of_endpoints` (k=1)
and `bilinear_corner_nonneg` (k=2) -- the lemmas the de-load `shed_step_c1..c5` certs
are built on -- via the ring-checkable convex-combination identity.
"""
import itertools
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.multilinear_corner import (  # noqa: E402
    MultilinearCornerCertificate, corner_values, is_multilinear,
)

A, B, C, E, s, t, s0, s1, t0, t1 = sp.symbols("A B C E s t s0 s1 t0 t1")


def test_multilinearity_detection():
    assert is_multilinear(A + B*s, (s,))
    assert is_multilinear(A + B*s + C*t + E*s*t, (s, t))
    assert not is_multilinear(A + B*s**2, (s,))
    assert not is_multilinear(s*t*s, (s, t))         # degree 2 in s


def test_corner_values_k2():
    cv = corner_values(A + B*s + C*t + E*(s*t), (s, t), {s: (s0, s1), t: (t0, t1)})
    assert cv[("lo", "lo")] == sp.expand(A + B*s0 + C*t0 + E*s0*t0)
    assert cv[("hi", "hi")] == sp.expand(A + B*s1 + C*t1 + E*s1*t1)
    assert len(cv) == 4


def test_convex_combination_identity_holds():
    # the ring identity the emitted proof relies on: P*D = sum_c wnum_c * P(c)
    P = A + B*s + C*t + E*(s*t)
    D = (s1 - s0)*(t1 - t0)
    rhs = 0
    for c in itertools.product(("lo", "hi"), ("lo", "hi")):
        wnum = (s1 - s if c[0] == "lo" else s - s0) * (t1 - t if c[1] == "lo" else t - t0)
        Pc = P.subs({s: s0 if c[0] == "lo" else s1, t: t0 if c[1] == "lo" else t1})
        rhs += wnum * Pc
    assert sp.expand(P*D - rhs) == 0


def test_k1_bridge_reproduces_linear_nonneg_of_endpoints():
    c = MultilinearCornerCertificate("linear", A + B*s, (s,), {s: (s0, s1)})
    assert c.check()
    lean = c.lean_bridge()
    assert "theorem linear_corner" in lean
    # the BG shape: box + BOTH endpoint values nonneg -> nonneg on the interval
    assert "(hc0 : 0 ≤ A + B*s0)" in lean and "(hc1 : 0 ≤ A + B*s1)" in lean
    assert "0 ≤ A + B*s := by" in lean
    assert "by ring" in lean and "nlinarith" in lean


def test_k2_bridge_reproduces_bilinear_corner_nonneg():
    c = MultilinearCornerCertificate("bilinear", A + B*s + C*t + E*(s*t), (s, t),
                                     {s: (s0, s1), t: (t0, t1)})
    assert c.check()
    lean = c.lean_bridge()
    assert "theorem bilinear_corner" in lean
    # all four corner hypotheses present (the bilinear_corner_nonneg signature)
    for j in range(4):
        assert f"(hc{j} : 0 ≤" in lean
    assert lean.count("mul_nonneg") >= 4        # weight-product nonneg chains
    assert "0 ≤ A + B*s + C*t + E*s*t := by" in lean


def test_refuses_non_multilinear():
    c = MultilinearCornerCertificate("bad", A + B*s**2, (s,), {s: (s0, s1)})
    assert not c.check()
    try:
        c.lean_bridge()
        assert False, "should have refused"
    except ValueError:
        pass


def test_numeric_corner_must_be_nonneg():
    # a concrete cell whose lo-corner is negative is refused
    c = MultilinearCornerCertificate("neg", -5 + s, (s,), {s: (sp.Integer(1), sp.Integer(2))})
    assert not c.check()                          # corner at s=1 is -4 < 0
