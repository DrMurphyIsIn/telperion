"""Negative controls for the concave_pooled_induction extensions (2026-10-01).

* leaf-exempt: the flat witness 1/12 lowered by 1/1000 -- FALSE at the root with two leaf
  children by exactly 1/1000 (the all-leaves step's norm_num cannot close it);
* log term in g: every log enclosure `log u <= H` forged to `H - 1/1000` (false), the cells
  rebuilt consistently on the true twin's layout (the enclosure lemma's linarith fails).

The adapters are NOT registered (one adapter per emitter: the path-density control); they
live in negctrl_adapters/adapter_concave_pooled_induction.py.  The kernel runs below are
gated on a built examples/concave_pooled_induction/lean; offline tests check the falsity and
the shared skeleton.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_env import lean_env_ready  # noqa: E402
from telperion.negative_control_harness import generic_negative_control  # noqa: E402
from telperion.negctrl_adapters import adapter_concave_pooled_induction as A  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "concave_pooled_induction" / "lean"


def test_exempt_forgery_is_false_by_a_thousandth():
    f = A.make_exempt_false_cert()
    assert not f.checked
    assert max(f.vs) == Fraction(1, 12) - Fraction(1, 1000)
    # the root with two leaf children: ell + 3 alpha = -2/3 + 3/4 = 1/12
    assert Fraction(-2, 3) + 3 * Fraction(1, 4) - max(f.vs) == Fraction(1, 1000)


def test_exempt_twins_share_the_skeleton():
    f = A.EXEMPT_ADAPTER.emit_call(A.make_exempt_false_cert(), "x")
    t = A.EXEMPT_ADAPTER.emit_call(A.make_exempt_true_cert(), "x")
    for needle in ("theorem x_xs_0_2", "theorem x_xhstep", "exempt_induction_core (fun m => m ≤ 2)"):
        assert needle in f and needle in t
    assert len(A.make_exempt_false_cert().cells) == len(A.make_exempt_true_cert().cells)


def test_log_forgery_is_false_and_only_the_log_constants_move():
    import math
    f, t = A.make_log_false_cert(), A.make_log_true_cert()
    assert [(c.s, c.t, c.j) for c in f.cells] == [(c.s, c.t, c.j) for c in t.cells]
    for cf, ct in zip(f.cells, t.cells):
        for bf, bt in zip(cf.logb, ct.logb):
            assert bt.H - bf.H == Fraction(1, 1000)
            assert float(bf.H) < math.log(float(bf.u))   # the forged enclosure is FALSE
            assert float(bt.H) >= math.log(float(bt.u))


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="no built concave_pooled_induction Lean env")
@pytest.mark.parametrize("which", ["EXEMPT_ADAPTER", "LOG_ADAPTER"])
def test_extension_kernel_controls_hold(which):
    res = generic_negative_control(getattr(A, which), env_dir=str(_ENV))
    assert res.kernel_rejects, res.detail
    assert res.true_compiles, res.detail
    assert res.okay
