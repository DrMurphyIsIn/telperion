"""Negative controls for the rational_identity extensions (2026-10-01).

* multivariate: a two-variable partial fraction plus 1/1000 (false);
* modular: t^5 = 5t + 4 modulo t^2 - t - 1 (wrong: the remainder is -1).

Unregistered adapters in negctrl_adapters/adapter_rational_identity.py; kernel runs gated on
a built examples/rational_identity/lean.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_env import lean_env_ready  # noqa: E402
from telperion.negative_control_harness import generic_negative_control  # noqa: E402
from telperion.negctrl_adapters import adapter_rational_identity as A  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "rational_identity" / "lean"


def test_forgeries_are_false():
    m = A.make_multivariate_false_cert()
    assert sp.cancel(sp.together(m.lhs - m.rhs)) == sp.Rational(-1, 1000)
    q = A.make_modular_false_cert()
    t = q.symbols[0]
    assert sp.rem(sp.expand(q.lhs - q.rhs), q.modulus, t) == -1
    assert not m.checked and not q.checked


def test_true_twins_are_identities():
    m = A.make_multivariate_true_cert()
    assert sp.cancel(sp.together(m.lhs - m.rhs)) == 0
    q = A.make_modular_true_cert()
    assert sp.rem(sp.expand(q.lhs - q.rhs), q.modulus, q.symbols[0]) == 0


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="no built rational_identity Lean env")
@pytest.mark.parametrize("which", ["MULTIVARIATE_ADAPTER", "MODULAR_ADAPTER"])
def test_extension_kernel_controls_hold(which):
    res = generic_negative_control(getattr(A, which), env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail
