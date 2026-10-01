"""Kink-minimum extension of curvature_boundary (2026-10-01).

A continuous piecewise polynomial with ONE interior kink at a rational kappa, left piece
decreasing and right piece increasing (each a Bernstein sign check on the derivative), is
minimized at kappa: IsLeast (f '' Icc a b) (f kappa), plus 0 <= f when f(kappa) >= 0, and the
same for an optional closed form with Abs of affine arguments.  conjecture1_proved = False.
"""
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

import telperion.negctrl_adapters  # noqa: E402,F401
from telperion.emit_curvature_boundary import (  # noqa: E402
    CurvatureBoundaryEmitter,
    KinkMinimumCertificate,
    curvature_boundary_certificate,
    kink_minimum_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    emit_via_single_instance_family,
    registered_adapters,
)

ABS = dict(left="1/3 - x + x**2", right="x - 1/3 + x**2", kappa=sp.Rational(1, 3), a=0, b=1,
           f_expr="Abs(x - 1/3) + x**2")


def test_abs_quadratic_kink_certificate():
    c = kink_minimum_certificate(**ABS, value=sp.Rational(1, 9))
    assert isinstance(c, KinkMinimumCertificate) and c.checked
    assert c.value == sp.Rational(1, 9)
    assert c.abs_args[0][1:] == ("le", "ge")
    assert all(pc.ok() and pc.identity_holds() for pc in c.left_cells + c.right_cells)


def test_minimum_is_attained_and_is_the_minimum_numerically():
    f = lambda x: abs(x - Fraction(1, 3)) + x * x  # noqa: E731
    vals = [f(Fraction(i, 600)) for i in range(601)]
    assert min(vals) == Fraction(1, 9) == f(Fraction(1, 3))


def test_cubic_pieces_need_no_closed_form():
    c = kink_minimum_certificate(left="(x - 1)**2 * (x + 2)", right="x**3 - x", kappa=1,
                                 a=-1, b=2)
    assert c.value == 0 and c.f_expr is None


@pytest.mark.parametrize("kw, why", [
    (dict(ABS, right="x + x**2"), "discontinuous"),
    (dict(ABS, left="1/3 + x**2 - x/10", right="x**2 - x/10 + 1/30 + 1/3 - 1/30 - 1/30 + 1/30"),
     "not certified decreasing|discontinuous"),
    (dict(ABS, kappa=0), "strictly inside"),
    (dict(ABS, kappa=1.0 / 3), "float"),
    (dict(ABS, f_expr="Abs(x - 1/2) + x**2"), "changes sign|does not equal"),
    (dict(ABS, f_expr="Abs(x**2 - 1/9) + x**2"), "non-affine"),
    (dict(ABS, left="1/3 - x + x**2 + sin(x)"), "not a polynomial"),
])
def test_refusals(kw, why):
    with pytest.raises(ValueError, match=why):
        kink_minimum_certificate(**kw)


def test_right_piece_decreasing_somewhere_is_refused_with_a_point():
    with pytest.raises(ValueError, match="not certified increasing"):
        kink_minimum_certificate(left="-x/2", right="x**2 - x/2", kappa=0, a=-1, b=1)


def test_wrong_claimed_minimum_is_refused_by_a_thousandth():
    with pytest.raises(ValueError, match="claimed minimum"):
        kink_minimum_certificate(**ABS, value=sp.Rational(1, 9) + sp.Rational(1, 1000))


def test_emitted_kink_lean_shape():
    c = kink_minimum_certificate(**ABS)
    text = emit_via_single_instance_family(CurvatureBoundaryEmitter(), lean_name="kk",
                                           instance_kwargs={"payload": c})
    for needle in ("theorem kink_min_of_anti_mono", "theorem kk_isLeast",
                   "IsLeast (kk_f '' Set.Icc (0 : ℝ) (1 : ℝ)) (1 / 9 : ℝ)",
                   "antitoneOn_of_deriv_nonpos", "monotoneOn_of_deriv_nonneg",
                   "theorem kk_nonneg", "theorem kk_expr_isLeast", "abs_of_nonpos", "abs_of_nonneg"):
        assert needle in text, needle
    assert "sorry" not in text and "native_decide" not in text
    # the endpoint lemmas are not emitted for an all-kink family
    assert "concave_ge_min_endpoints" not in text


def test_endpoint_modes_unchanged():
    c = curvature_boundary_certificate()
    text = emit_via_single_instance_family(CurvatureBoundaryEmitter(), lean_name="cc",
                                           instance_kwargs={"payload": c})
    assert "kink_min_of_anti_mono" not in text


def test_kink_adapter_registered_and_stance_wired():
    ad = registered_adapters()["CurvatureBoundaryEmitter"]
    assert ad.make_false_cert().value == sp.Rational(1, 9) + sp.Rational(1, 1000)
    assert not ad.make_false_cert().checked
    assert REGISTRY["CurvatureBoundaryEmitter"].neg_control.kind == NEG_CONTROL_ADAPTER


def test_example_regenerates_byte_for_byte():
    r = subprocess.run([sys.executable, str(ROOT / "examples" / "curvature_boundary" / "generate.py"),
                        "--check"], cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
