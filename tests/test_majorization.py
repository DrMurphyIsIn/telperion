"""Tests for the majorization / Schur-convexity primitive.

The acid tests: the HLP majorization order is exact (partial-sum dominance with
full-sum equality), the Muirhead T-transform chain recomposes to the target, the
Schur-Ostrowski criterion classifies the textbook cases (sum of squares convex;
sum of logs / roots and e_2 concave), and the SchurConvexityCertificate re-checks
its pair sign exactly and emits a well-formed Lean module.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.majorization import (  # noqa: E402
    SchurConvexityCertificate,
    TTransform,
    is_schur_concave,
    is_schur_convex,
    majorization_chain,
    majorizes,
    recompose,
)


# --------------------------------------------------------------------------- #
#  1. majorizes                                                               #
# --------------------------------------------------------------------------- #
def test_majorizes_basic_true():
    assert majorizes([3, 1, 1, 1], [2, 2, 1, 1])


def test_majorizes_basic_false():
    # equal sum but [2,2] does NOT majorize [3,1] (the more-spread vector majorizes)
    assert not majorizes([2, 2], [3, 1])
    assert majorizes([3, 1], [2, 2])


def test_majorizes_reflexive():
    for v in ([1, 2, 3], [Fr(1, 2), Fr(3, 2), 4], [5]):
        assert majorizes(v, v)


def test_majorizes_requires_equal_sum():
    assert not majorizes([3, 1], [2, 2, 0])   # different length
    assert not majorizes([3, 1], [1, 1])      # different sum


def test_majorizes_order_invariance():
    # majorization ignores ordering (sorts descending internally)
    assert majorizes([1, 1, 1, 3], [1, 2, 1, 2])


def test_majorizes_total_order_on_partitions_of_fixed_sum():
    # the majorization lattice on sum=4, length 4: apex [4,0,0,0], floor [1,1,1,1]
    apex = [4, 0, 0, 0]
    mid = [2, 1, 1, 0]
    floor = [1, 1, 1, 1]
    assert majorizes(apex, mid) and majorizes(mid, floor) and majorizes(apex, floor)
    assert not majorizes(floor, mid) and not majorizes(mid, apex)


def test_majorizes_exact_rationals():
    assert majorizes([Fr(5, 2), Fr(1, 2), 0], [1, 1, 1])
    assert not majorizes([1, 1, 1], [Fr(5, 2), Fr(1, 2), 0])


# --------------------------------------------------------------------------- #
#  2. majorization_chain (T-transforms)                                       #
# --------------------------------------------------------------------------- #
def test_chain_recomposes_to_target():
    x, y = [3, 1, 1, 1], [2, 2, 1, 1]
    chain = majorization_chain(x, y)
    assert chain, "expected at least one T-transform"
    result = recompose(x, chain)
    assert sorted(result, reverse=True) == sorted(map(Fr, y), reverse=True)


def test_chain_every_step_is_valid_ttransform():
    x, y = [4, 0, 0, 0], [1, 1, 1, 1]
    chain = majorization_chain(x, y)
    assert all(isinstance(s, TTransform) and s.is_valid() for s in chain)
    # each step moves from a strictly larger to a strictly smaller coordinate
    for s in chain:
        b = list(map(Fr, s.before))
        assert b[s.i_hi] > b[s.i_lo] and s.amount > 0


def test_chain_endpoints_correct():
    x, y = [5, 3, 1], [3, 3, 3]
    chain = majorization_chain(x, y)
    assert tuple(chain[0].before) == tuple(sorted(map(Fr, x), reverse=True))
    assert tuple(chain[-1].after) == tuple(sorted(map(Fr, y), reverse=True))
    assert recompose(x, chain) == sorted(map(Fr, y), reverse=True)


def test_chain_terminates_and_is_short():
    x, y = [4, 0, 0, 0], [1, 1, 1, 1]
    chain = majorization_chain(x, y)
    assert len(chain) <= len(x)  # closes >= 1 coordinate per step


def test_chain_refuses_non_majorizing():
    with pytest.raises(ValueError, match="does not majorize"):
        majorization_chain([2, 2], [3, 1])


def test_chain_empty_when_equal():
    assert majorization_chain([2, 2], [2, 2]) == []


def test_chain_rational():
    x, y = [Fr(5, 2), Fr(1, 2), 0], [1, 1, 1]
    chain = majorization_chain(x, y)
    assert recompose(x, chain) == sorted(map(Fr, [1, 1, 1]), reverse=True)
    assert all(s.is_valid() for s in chain)


# --------------------------------------------------------------------------- #
#  3. Schur-Ostrowski criterion                                               #
# --------------------------------------------------------------------------- #
def _pos_domain(xs):
    return [x > 0 for x in xs]


def test_sum_of_squares_is_schur_convex():
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    v = is_schur_convex(f, n, xs=xs)
    assert v.verdict == "convex" and bool(v)


def test_sum_of_squares_not_schur_concave():
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    v = is_schur_concave(f, n, xs=xs)
    assert v.verdict == "indefinite"


def test_sum_of_logs_is_schur_concave():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    f = sum(sp.log(x) for x in xs)
    v = is_schur_concave(f, n, domain=_pos_domain(xs), xs=xs)
    assert v.verdict == "concave"


def test_sum_of_sqrt_is_schur_concave():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    f = sum(sp.sqrt(x) for x in xs)
    v = is_schur_concave(f, n, domain=_pos_domain(xs), xs=xs)
    assert v.verdict == "concave"


def test_e2_elementary_symmetric_is_schur_concave():
    # e_2 = sum_{i<j} x_i x_j  is Schur-concave
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    e2 = sum(xs[i] * xs[j] for i in range(n) for j in range(i + 1, n))
    v = is_schur_concave(e2, n, domain=_pos_domain(xs), xs=xs)
    assert v.verdict == "concave"


def test_e2_not_schur_convex():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    e2 = sum(xs[i] * xs[j] for i in range(n) for j in range(i + 1, n))
    v = is_schur_convex(e2, n, domain=_pos_domain(xs), xs=xs)
    assert v.verdict == "indefinite"


def test_schur_verdict_carries_certifying_expr():
    n = 2
    xs = sp.symbols(f"x0:{n}", real=True)
    f = xs[0] ** 2 + xs[1] ** 2
    v = is_schur_convex(f, n, xs=xs)
    # (x0 - x1)(2 x0 - 2 x1) = 2 (x0 - x1)^2 >= 0
    assert sp.simplify(v.sign_expr - 2 * (xs[0] - xs[1]) ** 2) == 0


# --------------------------------------------------------------------------- #
#  4. SchurConvexityCertificate                                               #
# --------------------------------------------------------------------------- #
def test_certificate_check_convex_sum_squares():
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    cert = SchurConvexityCertificate("sumsq", f, tuple(xs), convex=True)
    assert cert.check()
    assert cert.verdict().verdict == "convex"


def test_certificate_check_concave_e2():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    e2 = sum(xs[i] * xs[j] for i in range(n) for j in range(i + 1, n))
    cert = SchurConvexityCertificate(
        "e2", e2, tuple(xs), convex=False, domain=tuple(x > 0 for x in xs)
    )
    assert cert.check()


def test_certificate_check_concave_sqrt():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    f = sum(sp.sqrt(x) for x in xs)
    cert = SchurConvexityCertificate(
        "sqrt", f, tuple(xs), convex=False, domain=tuple(x > 0 for x in xs)
    )
    assert cert.check()


def test_certificate_wrong_orientation_fails_check():
    # sum of squares is convex, so a convex=False certificate must NOT check
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    cert = SchurConvexityCertificate("sumsq_bad", f, tuple(xs), convex=False)
    assert not cert.check()


def test_lean_module_well_formed_convex():
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    cert = SchurConvexityCertificate("sumsq", f, tuple(xs), convex=True)
    mod = cert.lean_module("BG.Majorization.SumSq")
    assert mod.startswith("import Mathlib") or mod.lstrip().startswith("/-")
    assert "import Mathlib" in mod
    assert "namespace BG.Majorization.SumSq" in mod
    assert "end BG.Majorization.SumSq" in mod
    assert "norm_num" in mod
    assert "theorem sumsq_witness" in mod


def test_lean_module_well_formed_concave():
    n = 3
    xs = sp.symbols(f"x0:{n}", positive=True)
    e2 = sum(xs[i] * xs[j] for i in range(n) for j in range(i + 1, n))
    cert = SchurConvexityCertificate(
        "e2", e2, tuple(xs), convex=False, domain=tuple(x > 0 for x in xs)
    )
    mod = cert.lean_module("BG.Majorization.E2")
    assert "import Mathlib" in mod
    assert "namespace BG.Majorization.E2" in mod and "end BG.Majorization.E2" in mod
    assert "≤ (0 : ℝ)" in mod  # concave atom orientation


def test_lean_atom_key_inequality():
    n = 2
    xs = sp.symbols(f"x0:{n}", real=True)
    f = xs[0] ** 2 + xs[1] ** 2
    cert = SchurConvexityCertificate("sq2", f, tuple(xs), convex=True)
    atom = cert.lean_atom("w")
    assert "theorem sq2_w" in atom and "norm_num" in atom
    assert "(0 : ℝ) ≤" in atom


def test_lean_module_refuses_bad_certificate():
    n = 3
    xs = sp.symbols(f"x0:{n}", real=True)
    f = sum(x**2 for x in xs)
    cert = SchurConvexityCertificate("bad", f, tuple(xs), convex=False)
    with pytest.raises(ValueError, match="refusing to emit"):
        cert.lean_module("BG.Bad")
