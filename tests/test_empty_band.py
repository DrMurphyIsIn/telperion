"""Tests for the winding-0 empty-band emitter (RH-in-a-box no-low-zeros closure).

The empty-band path certifies that a box `[a,1-a] x [0,H]` with boundary winding
`N = 0` contains NO zeros of zeta (the argument principle gives total multiplicity 0,
and multiplicities are >= 1, so the divisor support is empty).  This is the driver
half of the `55/16` no-low-zeros residual closure: the emitted theorem's conclusion
(`forall rho in box, riemannZeta rho != 0`) is exactly what the dVP-symmetry session's
`no_low_zeros_of_empty_band` consumes.  conjecture1_proved = False.
"""
import importlib.util
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_box_localization import (  # noqa: E402
    EmptyBandCertificate,
    emit_empty_band_instantiation,
    empty_band_certificate,
)

requires_flint = pytest.mark.skipif(
    importlib.util.find_spec("flint") is None,
    reason="python-flint not installed",
)


# --- certificate: acceptance + negative controls ---------------------------------

def test_empty_band_certificate_accepts_n0():
    cert = empty_band_certificate("1/1000", "999/1000", "0", "55/16", n_total=0)
    assert isinstance(cert, EmptyBandCertificate)
    assert cert.n == 0


def test_empty_band_certificate_refuses_nonzero_winding():
    # Negative control: a nonzero winding is NOT an empty band -- there is a zero to exhibit.
    with pytest.raises(ValueError, match="n_total"):
        empty_band_certificate("1/1000", "999/1000", "0", "55/16", n_total=1)


def test_empty_band_certificate_refuses_pole_box():
    # [0,1] x [0,55/16] puts the pole s=1 at corner (1,0) -- must be refused.
    with pytest.raises(ValueError, match="pole"):
        empty_band_certificate("0", "1", "0", "55/16", n_total=0)


def test_empty_band_certificate_refuses_non_straddle():
    # A box whose real range excludes 1/2 cannot participate in the RH-in-box localization.
    with pytest.raises(ValueError, match="straddle"):
        empty_band_certificate("3/5", "4/5", "0", "1", n_total=0)


# --- emitter: Lean shape ---------------------------------------------------------

def test_emit_empty_band_lean_shape():
    cert = empty_band_certificate("1/1000", "999/1000", "0", "55/16", n_total=0)
    text = emit_empty_band_instantiation(cert, "band_test", namespace="EmptyBandTest")

    # Calls the generic counting atom directly with N = 0.
    assert "zeta_count_eq_winding_generic" in text
    # Top-level ball defs so hArb can forward straight to the atom.
    assert "noncomputable def cPB" in text
    assert "noncomputable def RPB" in text
    assert "theorem hs1_PB" in text
    # Conclusion is the empty-band statement (no zero in the box).
    assert "riemannZeta ρ ≠ 0" in text
    # The empty band exhibits NO on-line zeros: none of the count-matching machinery.
    assert "hLine" not in text
    assert "distinct" not in text
    assert "maxHeartbeats" not in text  # O(N^2) blowup is absent for N = 0
    assert "rh_in_box_of_certificate" not in text  # atom-direct, not the localization wrapper
    # Honesty invariant.
    assert "conjecture1_proved = False" in text
    # s = empty derivation present.
    assert "Finset.single_le_sum" in text


def test_emit_empty_band_uses_box_corners():
    cert = empty_band_certificate("1/100", "99/100", "0", "55/16", n_total=0)
    text = emit_empty_band_instantiation(cert, "corners_test", namespace="CornersTest")
    # Box corners appear in the conclusion bounds.
    assert "1 / 100" in text
    assert "99 / 100" in text
    assert "55 / 16" in text


# --- driver: winding is genuinely 0 on the candidate band (Arb) -------------------

@requires_flint
def test_run_empty_band_winding_zero(tmp_path):
    from telperion.driver_empty_band import run_empty_band  # noqa: E402

    text = run_empty_band("1/100", "99/100", "0", "55/16", winding_prec=160,
                          out_dir=tmp_path, write=True)
    assert "zeta_count_eq_winding_generic" in text
    # The driver asserts N == 0 internally; a nonzero winding would have raised.
    assert (tmp_path / "NoZerosInBox_1d100_99d100_0_55d16.lean").exists()


@requires_flint
def test_run_empty_band_refuses_box_with_zero():
    # A box that DOES contain a zero (winding != 0) must be refused by the driver.
    from telperion.driver_empty_band import run_empty_band  # noqa: E402

    with pytest.raises(ValueError, match="winding"):
        # [2/5,3/5] x [10,35] contains 5 zeros -> winding 5 != 0.
        run_empty_band("2/5", "3/5", "10", "35", winding_prec=160, write=False)
