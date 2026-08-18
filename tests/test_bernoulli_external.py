"""External-genericity test: Bernoulli's inequality through the telperion core.

This is the Priority-3 "engine is generic" witness — a textbook inequality that
has NOTHING to do with Brualdi-Goldwasser, driven through the enforced
certify -> validate -> emit -> freeze pipeline using ONLY `telperion` core
(never `telperion.bg`).  All checks here are exact-arithmetic pre-CI self-checks;
the Lean kernel remains the sole arbiter (verified in CI `lake build`).
"""
import importlib.util
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    ValidationReport,
    WorkflowError,
    certify,
    diff_frozen,
    emit,
)

# Load the example generator as a module (examples/ is not an importable package).
_GEN_PATH = (
    Path(__file__).resolve().parents[1] / "examples" / "bernoulli" / "generate.py"
)
_spec = importlib.util.spec_from_file_location("bernoulli_generate", _GEN_PATH)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)

x = gen.x


def test_coefficients_are_nonnegative_binomials():
    """The expanded target has all-nonneg integer coeffs = binomials C(k,j),
    j>=2 (and zero below), verified in exact arithmetic."""
    for k in gen.KS:
        poly = sp.Poly(gen.bernoulli_target({"k": k}), x)
        for c in poly.all_coeffs():
            assert c == int(c) and int(c) >= 0
        for j in range(0, k + 1):
            got = poly.coeff_monomial(x**j) if j > 0 else poly.coeff_monomial(1)
            want = comb(k, j) if j >= 2 else 0
            assert sp.Integer(got) == sp.Integer(want), (k, j, got, want)


def test_value_nonnegative_at_exact_rationals():
    """(1+x)^k - 1 - k*x >= 0 at several exact rational x >= 0, and the expanded
    form agrees exactly with the closed form."""
    samples = [Fraction(0), Fraction(1, 7), Fraction(3, 4), Fraction(1),
               Fraction(5, 2), Fraction(37, 3)]
    for k in gen.KS:
        for xf in samples:
            xr = sp.Rational(xf.numerator, xf.denominator)
            val = gen.bernoulli_target({"k": k}).subs({x: xr})
            assert val >= 0, (k, xf, val)
            closed = (1 + xr) ** k - 1 - k * xr
            assert sp.simplify(val - closed) == 0, (k, xf)


def test_certify_succeeds():
    """certify() returns the emission witness for every grid instance."""
    cert = certify(gen.bernoulli_family())
    assert len(cert.instances) == len(gen.KS)
    # Each instance carries a direct Polya certificate over denominator 1.
    for inst in cert.instances:
        assert len(inst.corners) == 1
        assert sp.simplify(inst.corners[0].denominator - 1) == 0


def test_emit_refuses_without_green_validation():
    """Negative control: emit() must refuse when the ValidationReport is not
    green, even with a valid CertifiedFamily witness."""
    cert = certify(gen.bernoulli_family())
    red = ValidationReport(checks=(("intentionally_failed", False),))
    with pytest.raises(WorkflowError):
        emit(cert, gen.bernoulli_profile(), [DirectPolyaEmitter()], red,
             file_name="Bernoulli.lean")


def test_emit_produces_six_theorems():
    """Positive control: the enforced pipeline emits one theorem per grid cell."""
    res = gen.build()
    assert res.n_theorems == len(gen.KS)
    assert set(res.files) == {"Bernoulli.lean"}


def test_regeneration_is_byte_stable_against_frozen():
    """Byte-stability: regenerating reproduces the frozen artifact and its hash."""
    res = gen.build()
    frozen_dir = _GEN_PATH.parent / "frozen"
    rep = diff_frozen(res, frozen_dir)
    assert rep.ok, rep.details
    # And the recorded manifest hash matches the regenerated input hash.
    import json

    manifest = json.loads((frozen_dir / "manifest.json").read_text())
    assert manifest["input_hash"] == res.input_hash
    assert manifest["n_theorems"] == res.n_theorems
