"""grid_modulus_nonvanishing emitter -- Lipschitz-net ZERO-FREENESS certificate.

Layer-1 self-check pass + the full refusal list (the anti-phantom face): a certificate that
merely restates the numbers it was handed is not an instrument, so every load-bearing quantity
is re-derived from its definition and a disagreement is REFUSED.

The Layer-2 kernel control (forged `delta` rejected, true twin compiles) lives in
`telperion/src/telperion/negctrl_adapters/adapter_grid_modulus_nonvanishing.py` and is driven by
the generic harness.

SCOPE: the shipped instance is the Face-7 pilot box for `deriv riemannZeta` on
`[1/4, 3/8] x [6, 10]`.  That is NOT the Speiser wall -- Speiser (1935) makes non-vanishing of
`zeta'` on the WHOLE open left strip equivalent to RH, and no finite union of boxes exhausts a
strip.  Nothing here is a step toward RH.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS  # noqa: E402
from telperion.emit_grid_modulus_nonvanishing import (  # noqa: E402
    GridModulusNonvanishingEmitter,
    certify_grid_modulus_nonvanishing_point,
    grid_modulus_nonvanishing_certificate,
    grid_modulus_nonvanishing_family,
    register_backend,
)
from telperion.family import GridSpec  # noqa: E402


# A libflint/mpmath-free synthetic backend so the refusal tests are fast and exact:
# |f'| == 1 everywhere, |f''| == 1/10 everywhere, |f'''| == 0.
def _flat_backend(order, re, im, prec):
    return {1: 1.0, 2: 0.1, 3: 0.0}[order]


register_backend("flat_test_double", _flat_backend)

_BASE = dict(
    re0="1/4", re1="3/8", im0="6", im1="10",
    grid_re="5/16",
    grid_im=("25/4", "27/4", "29/4", "31/4", "33/4", "35/4", "37/4", "39/4"),
    half_width="1/16", half_height="1/4",
    delta="13/50", bound_M="3/10", bound_L="1/10",
    backend="flat_test_double", prec=30, sweep_nre=4, sweep_nim=8,
)


def _cert(**over):
    return grid_modulus_nonvanishing_certificate(**{**_BASE, **over})


# --------------------------------------------------------------------------- self-check pass


def test_self_check_passes_and_records_the_rederived_observations():
    c = _cert()
    assert c.trust_class == "mpmath-numeric"
    js = c.to_json_dict()
    assert js["kind"] == "grid_modulus_nonvanishing"
    assert js["constants"] == {"M": "3/10", "delta": "13/50", "L": "1/10"}
    assert js["grid"]["re"] == "5/16" and len(js["grid"]["im"]) == 8
    # the observations are RE-DERIVED, not echoed from the spec
    assert float(js["observed"]["sup_second_deriv"]) == pytest.approx(0.1)
    assert float(js["observed"]["min_first_deriv_on_grid"]) == pytest.approx(1.0)


def test_kind_is_registered_in_both_certify_tables():
    assert "grid_modulus_nonvanishing" in _SPECIAL_KINDS
    assert "grid_modulus_nonvanishing" in _SPECIAL_DISPATCH
    # third tuple element is required for emitter_for(kind)
    assert len(_SPECIAL_DISPATCH["grid_modulus_nonvanishing"]) == 3


# --------------------------------------------------------------------- NEGATIVE CONTROLS (L1)


def test_refuses_understated_delta():
    """delta below the exact cell half-diagonal: the grid does not net the box."""
    with pytest.raises(ValueError, match="understates the cell half-diagonal"):
        _cert(delta="1/5")


def test_refuses_violated_gap_condition():
    """M * delta >= L: the net cannot exclude a zero however good the numbers are."""
    with pytest.raises(ValueError, match="gap condition fails"):
        _cert(bound_M="2", delta="13/50", bound_L="1/10")


def test_refuses_grid_column_that_does_not_span_the_box():
    """A column pushed to the box edge leaves the far side more than half_width away."""
    with pytest.raises(ValueError, match="does not cover"):
        _cert(grid_re="1/4")


def test_refuses_row_gap_larger_than_two_half_heights():
    """Dropping an interior row opens a hole the net does not reach."""
    with pytest.raises(ValueError, match="exceeds"):
        _cert(grid_im=("25/4", "27/4", "29/4", "33/4", "35/4", "37/4", "39/4"))


def test_refuses_rows_that_leave_the_bottom_uncovered():
    with pytest.raises(ValueError, match="leaves the bottom"):
        _cert(grid_im=("27/4", "29/4", "31/4", "33/4", "35/4", "37/4", "39/4"))


def test_refuses_rows_that_leave_the_top_uncovered():
    with pytest.raises(ValueError, match="leaves the top"):
        _cert(grid_im=("25/4", "27/4", "29/4", "31/4", "33/4", "35/4", "37/4"))


def test_refuses_claimed_M_the_independent_sweep_does_not_support():
    """The anti-phantom check on M: |f''| is 1/10 here, so M = 1/100 is NOT an upper bound."""
    with pytest.raises(ValueError, match="is NOT an upper bound"):
        _cert(bound_M="1/100", bound_L="1/10", delta="13/50")


def test_refuses_claimed_L_the_independent_evaluation_does_not_support():
    """The anti-phantom check on L: |f'| is 1 here, so L = 2 is NOT a lower bound."""
    with pytest.raises(ValueError, match="is NOT a lower bound"):
        _cert(bound_L="2", bound_M="3/10", delta="13/50")


def test_refuses_inverted_box():
    with pytest.raises(ValueError, match="inverted box"):
        _cert(re0="3/8", re1="1/4")


def test_refuses_unregistered_backend():
    with pytest.raises(ValueError, match="unknown numeric backend"):
        _cert(backend="no_such_backend")


def test_refuses_unsorted_rows():
    with pytest.raises(ValueError, match="not in increasing order"):
        _cert(grid_im=("27/4", "25/4", "29/4", "31/4", "33/4", "35/4", "37/4", "39/4"))


# ------------------------------------------------------------------------------- emission


def _emit_one():
    fam = grid_modulus_nonvanishing_family(
        "T", GridSpec([("case", [0])]), lambda pt: "gmn_demo", spec=lambda pt: _BASE)
    inst, nthm = certify_grid_modulus_nonvanishing_point(fam, {"case": 0}, "gmn_demo")

    class _V:
        instances = [inst]

    em = GridModulusNonvanishingEmitter()
    body, n = em.emit_body(_V())
    return body, n, nthm, em


def test_emits_five_theorems_including_the_capstone():
    body, n, nthm, em = _emit_one()
    assert n == 5 and nthm == 5
    for t in ("gmn_demo_cover_radius_ok", "gmn_demo_gap_ok", "gmn_demo_column_span_ok",
              "gmn_demo_row_tiling_ok"):
        assert f"theorem {t}" in body
    assert "theorem gmn_demo :" in body, "the capstone must carry the instance name"
    # the certificate's own numbers appear IN the statement -- that is what makes it
    # certificate-sensitive (a corrupted number becomes a false norm_num goal).
    assert "def gmn_demo_delta : ℚ := 13/50" in body
    assert "def gmn_demo_boundM : ℚ := 3/10" in body
    assert "def gmn_demo_boundL : ℚ := 1/10" in body
    assert em._cert_sink and em._cert_sink[0]["kind"] == "grid_modulus_nonvanishing"


def test_emitted_lean_carries_no_sorry():
    body, _, _, _ = _emit_one()
    assert "sorry" not in body and "admit" not in body


def test_scope_disclaimer_is_present_in_the_emitted_doc():
    body, _, _, _ = _emit_one()
    assert "EVIDENCE, NOT A PROOF" in body
