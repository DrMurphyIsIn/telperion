"""Handelman certificate FINDER — upgrading the emitter from checker to searcher.

`find_handelman_certificate` searches (exactly, sympy-only) for a nonnegative
combination of constraint products equal to `p`; the emitter uses it whenever a
family returns ``terms = None``.  The finder is untrusted — every result is
re-verified by the certifier — so these tests cover that it FINDS real
certificates, is DETERMINISTIC (byte-stable output), and that finder-mode
certification refuses when none exists.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, HandelmanEmitter, LeanProfile, ValidationReport,
    certify, check_lean_text, emit, find_handelman_certificate, handelman_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _verify(p, gens, terms):
    recon = sum((sp.Rational(c) * sp.prod([g ** a for g, a in zip(gens, al)])
                 for c, al in terms), sp.Integer(0))
    return sp.expand(p - recon) == 0


def test_finder_finds_and_verifies():
    x, y = sp.symbols("x y")
    cases = [
        (1 - x ** 2, [1 - x, 1 + x]),
        (x * y, [x, y]),
        (2 - x ** 2 - y ** 2, [1 - x, 1 + x, 1 - y, 1 + y]),
    ]
    for p, gens in cases:
        terms = find_handelman_certificate(p, gens, (x, y), max_deg=2)
        assert terms is not None and _verify(p, gens, terms), (p, terms)


def test_finder_is_deterministic():
    x, y = sp.symbols("x y")
    a = find_handelman_certificate(2 - x ** 2 - y ** 2,
                                   [1 - x, 1 + x, 1 - y, 1 + y], (x, y), 2)
    b = find_handelman_certificate(2 - x ** 2 - y ** 2,
                                   [1 - x, 1 + x, 1 - y, 1 + y], (x, y), 2)
    assert a == b  # byte-stability of frozen output depends on this


def test_finder_returns_none_when_no_certificate():
    x = sp.Symbol("x")
    # x - 2 is negative on {x >= 0}: no nonnegative Handelman representation
    assert find_handelman_certificate(x - 2, [x], (x,), max_deg=3) is None


def test_finder_mode_certifies_and_emits():
    x, y = sp.symbols("x y")
    # spec returns terms=None -> Telperion finds the products, then emits
    fam = handelman_family("F", (x, y), GridSpec([("j", [0])]), lambda pt: "f",
                           lambda pt: (1 - x ** 2, [(1 - x, "h1"), (1 + x, "h2")], None))
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [HandelmanEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "mul_nonneg" in body


def test_finder_mode_refuses_when_not_positive():
    x = sp.Symbol("x")
    fam = handelman_family("B", (x,), GridSpec([("j", [0])]), lambda pt: "b",
                           lambda pt: (x - 2, [(x, "hx")], None))
    with pytest.raises(CertificationError):
        certify(fam)


def test_bernstein_fastpath_high_degree_box():
    # BG leaf discharge Q = 621*3^7 - 64*(3+h)^7 >= 0 on [0,1] — degree 7,
    # ~10^6 coefficients: the generic subset-search / SDP-rounding finders stall,
    # the Bernstein fast-path certifies it directly and exactly.
    h = sp.Symbol("h")
    Q = sp.expand(621 * 3 ** 7 - 64 * (3 + h) ** 7)
    terms = find_handelman_certificate(Q, [h, 1 - h], (h,))
    assert terms is not None
    assert _verify(Q, [h, 1 - h], terms)                 # exact reconstruction
    assert all(sp.Rational(c) >= 0 for c, _e in terms)   # nonnegative combination


def test_bernstein_fastpath_shifted_interval():
    # a != 0 interval [1,2]: 10 - (x-1)^2 >= 0 there (min 9 at x=2).
    x = sp.Symbol("x")
    R = sp.expand(10 - (x - 1) ** 2)
    terms = find_handelman_certificate(R, [x - 1, 2 - x], (x,))
    assert terms is not None and _verify(R, [x - 1, 2 - x], terms)
