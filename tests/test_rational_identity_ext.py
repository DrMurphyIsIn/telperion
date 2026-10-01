"""rational_identity extension (2026-10-01): multivariate identities on a box of rays, and
identities modulo a minimal polynomial (e.g. Q(sqrt 5) = Q[t]/(t^2 - t - 1)).
conjecture1_proved = False.
"""
import subprocess
import sys
from pathlib import Path

import pytest
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion import CertificationError, GridSpec, certify  # noqa: E402
from telperion.emit_rational_identity import (  # noqa: E402
    ExtendedIdentityCert,
    RationalIdentityEmitter,
    extended_identity_certificate,
    rational_identity_family,
)
from telperion.negative_control_harness import emit_via_single_instance_family  # noqa: E402

x, y, t = sp.symbols("x y t")
PHI = t ** 2 - t - 1


def _fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def test_two_variable_partial_fraction():
    c = extended_identity_certificate(symbols=(x, y), lhs=1 / ((x + y) * (x + 2 * y)),
                                      rhs=(1 / (x + y) - 1 / (x + 2 * y)) / y,
                                      domain={"x": 0, "y": 0})
    assert isinstance(c, ExtendedIdentityCert) and c.mode == "multivariate"
    assert {r for _, r in c.atoms} == {"linarith"}


def test_quadratic_factor_uses_positivity():
    c = extended_identity_certificate(symbols=(x,), lhs=1 / (x * (x ** 2 + 1)),
                                      rhs=1 / x - x / (x ** 2 + 1), domain={"x": 0})
    assert sorted(r for _, r in c.atoms) == ["linarith", "positivity"]


@pytest.mark.parametrize("n", range(2, 12))
def test_fibonacci_powers_modulo_the_minimal_polynomial(n):
    c = extended_identity_certificate(symbols=(t,), lhs=t ** n,
                                      rhs=_fib(n) * t + _fib(n - 1), modulus=PHI)
    assert sp.expand(c.quotient * PHI - (t ** n - _fib(n) * t - _fib(n - 1))) == 0


@pytest.mark.parametrize("kw, why", [
    (dict(symbols=(x,), lhs=1 / ((x + 1) * (x + 2)),
          rhs=1 / (x + 1) - 1 / (x + 2) + sp.Rational(1, 1000), domain={"x": -1}), "not cancel"),
    (dict(symbols=(x, y), lhs=1 / (x - y), rhs=1 / (x - y), domain={"x": 0, "y": 0}),
     "cannot certify the denominator"),
    (dict(symbols=(x,), lhs=1 / (x + 2), rhs=1 / (x + 2), domain={"x": -3}),
     "cannot certify the denominator"),
    (dict(symbols=(t,), lhs=t ** 5, rhs=5 * t + 4, modulus=PHI), "not divisible"),
    (dict(symbols=(t,), lhs=t ** 2, rhs=1, modulus=t ** 2 - 1), "reducible"),
    (dict(symbols=(t,), lhs=t ** 2, rhs=1, modulus=2 * t ** 2 - 1), "monic"),
    (dict(symbols=(t,), lhs=1 / t, rhs=t - 1, modulus=PHI), "variable denominator"),
    (dict(symbols=(x,), lhs=x, rhs=x), "exactly one"),
    (dict(symbols=(x,), lhs=x * y, rhs=y * x, domain={"x": 0}), "not declared"),
    (dict(symbols=(x,), lhs=x, rhs=x, domain={"x": 0.5}), "float"),
])
def test_refusals(kw, why):
    with pytest.raises(ValueError, match=why):
        extended_identity_certificate(**kw)


def test_family_dict_spec_and_tuple_spec_coexist():
    fam = rational_identity_family(
        "F", (x,), GridSpec([("i", [0, 1])]), lambda pt: f"i{pt['i']}",
        lambda pt: ((x ** 2 - 1) / (x - 1), x + 1, 1) if pt["i"] == 0
        else dict(lhs=1 / ((x + 1) * (x + 2)), rhs=1 / (x + 1) - 1 / (x + 2), domain={"x": 0}))
    cf = certify(fam)
    assert len(cf.instances) == 2
    bad = rational_identity_family(
        "B", (t,), GridSpec([("i", [0])]), lambda pt: "b",
        lambda pt: dict(lhs=t ** 3, rhs=2 * t + 2, modulus=PHI))
    with pytest.raises(CertificationError):
        certify(bad)


def test_modular_emission_has_the_root_instance():
    c = extended_identity_certificate(symbols=(t,), lhs=(2 * t - 1) ** 2, rhs=5, modulus=PHI)
    text = emit_via_single_instance_family(RationalIdentityEmitter(), lean_name="r5",
                                           instance_kwargs={"payload": c},
                                           family_kwargs={"symbols": (t,)})
    for needle in ("theorem r5 : ∀ t : ℝ,", "linear_combination", "theorem r5_at_root",
                   "Real.sqrt (5 : ℝ)", "Real.sq_sqrt"):
        assert needle in text, needle


@pytest.mark.parametrize("script", ["generate.py", "generate_ext.py"])
def test_examples_regenerate_byte_for_byte(script):
    r = subprocess.run([sys.executable, str(ROOT / "examples" / "rational_identity" / script),
                        "--check"], cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
