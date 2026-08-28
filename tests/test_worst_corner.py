"""Tests for the general worst-corner polynomial-positivity emitter.

The acid test: it reproduces the parallel session's hand-written
`toeplitz3_pos_of_enclosure` worst-corner bound exactly, and the corner bound is a
genuine lower bound over the whole box (all-corners check).  Plus BG-shaped
bilinear/cubic corners and refusal on non-positive boxes.
"""
import itertools
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.worst_corner import WorstCornerCertificate, worst_corner_bound  # noqa: E402

g0, g1, g2, g3, g4 = sp.symbols("g0 g1 g2 g3 g4")
GENS = (g0, g1, g2, g3, g4)
# the 3x3 Toeplitz minor (= toeplitz3_pos_of_enclosure's polynomial)
TOEPLITZ3 = g2**3 - 2*g1*g2*g3 + g1**2*g4 + g0*g3**2 - g0*g2*g4


def _box():
    lo = {g0: Fr(1, 10), g1: Fr(1, 10), g2: Fr(2), g3: Fr(1, 10), g4: Fr(1, 10)}
    hi = {g0: Fr(2, 10), g1: Fr(2, 10), g2: Fr(3), g3: Fr(2, 10), g4: Fr(2, 10)}
    return lo, hi


def test_reproduces_toeplitz3_worst_corner_bound_symbolically():
    lo = {g: sp.Symbol(f"lo{i}") for i, g in enumerate(GENS)}
    hi = {g: sp.Symbol(f"hi{i}") for i, g in enumerate(GENS)}
    wc, _ = worst_corner_bound(TOEPLITZ3, GENS, lo, hi)
    target = (lo[g2]**3 + lo[g1]**2*lo[g4] + lo[g0]*lo[g3]**2
              - 2*hi[g1]*hi[g2]*hi[g3] - hi[g0]*hi[g2]*hi[g4])
    assert sp.expand(wc - target) == 0        # exact match to the hand-written RH bridge


def test_worst_corner_is_a_true_lower_bound_at_all_corners():
    lo, hi = _box()
    c = WorstCornerCertificate("toeplitz3", TOEPLITZ3, GENS, lo, hi)
    wc = c.worst_corner()
    for corner in itertools.product(*[(lo[g], hi[g]) for g in GENS]):
        val = TOEPLITZ3.subs(dict(zip(GENS, corner)))
        assert wc <= Fr(sp.nsimplify(val))     # lower bound holds at all 32 corners
    assert c.check() and wc > 0


def test_lean_bridge_shape():
    lo, hi = _box()
    c = WorstCornerCertificate("toeplitz3", TOEPLITZ3, GENS, lo, hi)
    lean = c.lean_bridge()
    assert "theorem toeplitz3_bridge" in lean
    assert "by gcongr" in lean and "nlinarith" in lean
    # one gcongr monomial bound per non-constant term (5 for this minor)
    assert lean.count("by gcongr") == 5
    # every generator appears with its nonneg fact
    for i in range(1, 6):
        assert f"have n{i} : (0:ℝ) ≤ g{i}" in lean


def test_bilinear_bg_shaped_corner():
    # a BG-style bilinear corner: 6*x*y - 1 > 0 over [1,2]^2 (worst corner at floor = 5)
    x, y = sp.symbols("x y")
    c = WorstCornerCertificate("bilin", 6*x*y - 1, (x, y), {x: Fr(1), y: Fr(1)}, {x: Fr(2), y: Fr(2)})
    assert c.check() and c.worst_corner() == 5
    assert "theorem bilin_bridge" in c.lean_bridge()


def test_refuses_when_worst_corner_not_positive():
    x, y = sp.symbols("x y")
    c = WorstCornerCertificate("bad", 6*x*y - 10, (x, y), {x: Fr(1), y: Fr(1)}, {x: Fr(2), y: Fr(2)})
    assert not c.check()                       # 6*1*1 - 10 = -4 at the floor
    with pytest.raises(ValueError, match="refusing to emit"):
        c.lean_bridge()


def test_inverted_box_refused():
    x, y = sp.symbols("x y")
    c = WorstCornerCertificate("inv", x + y, (x, y), {x: Fr(2), y: Fr(1)}, {x: Fr(1), y: Fr(2)})
    assert not c.check()                       # lo_x=2 > hi_x=1
