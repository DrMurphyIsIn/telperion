"""PolyGeomClosure emitter: remainder synthesis exactness + emit + refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    poly_geom_closure_certificate, poly_geom_closure_family,
)
from telperion.emit_poly_geom_closure import PolyGeomClosureEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return poly_geom_closure_family(
        name="GeomChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "weighted_geom", spec=lambda pt: spec)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "Geom")),
                [PolyGeomClosureEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(((1, 2, 1), sp.Rational(1, 2))).kind == "poly_geom_closure"


def test_source_instance_synthesis():
    # p(n) = (n+1)^2 = 1 + 2n + n^2, rho = 1/2 -> q(N) = 12 + 8N + 2N^2, B = 12
    cert = poly_geom_closure_certificate((1, 2, 1), sp.Rational(1, 2))
    assert cert.q == (12, 8, 2)
    assert cert.B == 12


def test_general_synthesis_recurrence_holds():
    # p(n) = 3 + n, rho = 1/3: verify q(N) = p(N) + rho*q(N+1) exactly
    cert = poly_geom_closure_certificate((3, 1), sp.Rational(1, 3))
    N = sp.Symbol("N")
    q = lambda x: sum(c * x ** i for i, c in enumerate(cert.q))  # noqa: E731
    p = lambda x: sum(c * x ** i for i, c in enumerate(cert.p))  # noqa: E731
    assert sp.expand(q(N) - p(N) - sp.Rational(1, 3) * q(N + 1)) == 0
    assert cert.B == cert.q[0]


def test_emits_identity_and_transfer():
    text = _emit(_family(((1, 2, 1), sp.Rational(1, 2)))).files["GeomChk.lean"]
    assert "theorem weighted_geom_identity" in text
    assert "theorem weighted_geom" in text
    assert "Finset.sum_range_succ" in text and "push_cast" in text
    assert "pow_le_pow_left₀" in text
    assert "(12)" in text  # the bound


def test_lean_text_clean():
    check_lean_text(_emit(_family(((1, 2, 1), sp.Rational(1, 2)))).files["GeomChk.lean"])
    check_lean_text(_emit(_family(((5,), sp.Rational(2, 3)))).files["GeomChk.lean"])


def test_byte_stability():
    s = ((0, 1), sp.Rational(1, 4))
    assert _emit(_family(s)).files["GeomChk.lean"] == _emit(_family(s)).files["GeomChk.lean"]


def test_negative_control_rate_out_of_range():
    for bad in (0, 1, sp.Rational(3, 2), -sp.Rational(1, 2)):
        with pytest.raises(ValueError, match="anchor"):
            poly_geom_closure_certificate((1,), bad)


def test_negative_control_negative_weight():
    with pytest.raises(ValueError, match="coefficient"):
        poly_geom_closure_certificate((1, -2), sp.Rational(1, 2))


def test_negative_control_zero_weight():
    with pytest.raises(ValueError, match="zero weight"):
        poly_geom_closure_certificate((0, 0), sp.Rational(1, 2))
