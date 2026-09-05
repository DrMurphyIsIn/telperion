"""cert_leaf assembles a hazard-safe positivity leaf and catches the two comment/operator
hazards that recurred in the hand-written Kelmans ports."""
import sympy as sp
import pytest

from telperion.cert_leaf import (
    scan_hazards,
    render_leaf,
    positivity_leaf,
    rational_pos_cert,
)


def test_scan_catches_dashslash_prose_hazard():
    # the `3-/4-hub` bug: `-/` inside comment prose closes it early.
    bad = "/-\n  3-/4-hub probes pass\n-/\nimport Mathlib\n"
    hz = scan_hazards(bad)
    assert any("closes the comment early" in h for h in hz)


def test_scan_catches_star_star():
    assert any("`**`" in h for h in scan_hazards("theorem t : 0 < x**2 := by nlinarith"))


def test_scan_clean_text():
    assert scan_hazards("/-- doc -/\ntheorem t (x:ℝ) : 0 ≤ x^2 := by positivity") == []


def test_render_leaf_raises_on_hazard():
    with pytest.raises(ValueError, match="hazards"):
        render_leaf(module_doc="see 3-/4 here", namespace="N", theorems=["theorem t : True := trivial"])


def test_positivity_leaf_end_to_end():
    u, v = sp.symbols("u v", nonnegative=True)
    pA, pB = sp.symbols("pA pB")
    specs = [
        # orthant, plain
        {"kind": "orthant", "suffix": "inc", "poly": 2 * u * v + u + 3, "syms": (u, v),
         "doc": "loaded donor: gain > 0"},
        # orthant, sign-flipped (a decreasing cell certifies -poly >= 0)
        {"kind": "orthant", "suffix": "dec", "poly": -(u + v + 5), "syms": (u, v), "sign": -1,
         "doc": "de-loaded donor: -gain > 0"},
        # domain (simplicial cone pA >= pB >= 1), body positive only on the cone
        {"kind": "domain", "suffix": "cone", "poly": (pA - pB) + (pB - 1) + 1,
         "constraints": [(1, pB), (pB, pA)], "doc": "cone positivity"},
        # finite rational exception
        {"kind": "rational", "suffix": "exc", "value": sp.Rational(113, 3174),
         "doc": "increasing corner"},
    ]
    leaf = positivity_leaf("demo", specs, module_doc="Demo merge cells.\nSecond line.",
                           namespace="R3Cert.Step3")
    assert leaf.startswith("/-\nDemo merge cells.")
    assert "import Mathlib" in leaf
    assert "namespace R3Cert.Step3" in leaf and "end R3Cert.Step3" in leaf
    assert leaf.count("theorem ") == 4
    assert "theorem demo_inc" in leaf and "theorem demo_dec" in leaf
    assert "theorem demo_cone" in leaf and "theorem demo_exc" in leaf
    assert "**" not in leaf                       # no leaked powers
    assert scan_hazards(leaf) == []               # assembled leaf is hazard-free


def test_rational_pos_cert_rejects_nonpositive():
    with pytest.raises(ValueError, match="not strictly positive"):
        rational_pos_cert("bad", sp.Rational(-1, 2))
