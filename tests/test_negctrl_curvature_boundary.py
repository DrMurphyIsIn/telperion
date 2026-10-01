"""Negative control for CurvatureBoundaryEmitter (kink-minimum route, 2026-10-01).

The minimum of |x - 1/3| + x^2 on [0, 1] is 1/9 (at the kink); the forgery claims
1/9 + 1/1000.  The kernel run is the generic
`test_certificate_sensitivity::test_generic_negative_control_holds` (it picks the built
examples/curvature_boundary/lean env) and the gated test below.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion.negctrl_adapters  # noqa: E402,F401
from lean_env import lean_env_ready  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "curvature_boundary" / "lean"


def _ad():
    return registered_adapters()["CurvatureBoundaryEmitter"]


def test_forged_claim_is_genuinely_false():
    f = _ad().make_false_cert()
    assert f.value - sp.Rational(1, 9) == sp.Rational(1, 1000)
    # f(1/3) = 1/9 < the forged minimum
    assert abs(Fraction(0)) + Fraction(1, 9) < Fraction(1009, 9000)


def test_twins_differ_only_in_the_claimed_value():
    f = _ad().emit_call(_ad().make_false_cert(), "t")
    t = _ad().emit_call(_ad().make_true_cert(), "t")
    diff = [(a, b) for a, b in zip(f.splitlines(), t.splitlines()) if a != b]
    assert diff and all(("1009 / 9000" in a or "1009/9000" in a)
                        and ("1 / 9" in b or "1/9" in b) for a, b in diff)


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="no built curvature_boundary Lean env")
def test_kink_kernel_control_holds():
    res = generic_negative_control(_ad(), env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail
