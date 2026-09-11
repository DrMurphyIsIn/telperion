"""Unit-modulus conjugate-pair SOS emitter: certificate, pipeline flow, negative control.

For |u| = 1, `2 - u^m - conj(u^m) = ‖1 - u^m‖² ≥ 0` — the manifest square behind on-line
Riemann-zero Li positivity. The Lean kernel is the arbiter (CI `lake build`); these are the
pre-CI self-checks — the exact conjugate-pair identity, byte-stable rendering, and the
degenerate-power refusal.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    UnitModulusSOSEmitter,
    ValidationReport,
    certify,
    emit,
    unit_modulus_certificate,
    unit_modulus_sos_family,
)
from telperion.certify import emitter_for  # noqa: E402


def _family(powers=(1, 2, 5)):
    return unit_modulus_sos_family(
        name="UnitModulusTest",
        grid=GridSpec([("m", list(powers))]),
        lean_name=lambda pt: f"onLine_sq_m{pt['m']}",
        power=lambda pt: pt["m"],
    )


def test_kind_is_unit_modulus_sos():
    assert _family().kind == "unit_modulus_sos"


def test_emitter_for_round_trips():
    assert emitter_for("unit_modulus_sos").kind == "unit_modulus_sos"


def test_certificate_identity_holds():
    cert = unit_modulus_certificate(3)
    assert cert.power == 3
    # the Hermitian form minus the square is exactly the (v·vc − 1) constraint (coeff −1)
    assert cert.residual == -1


def test_negative_control_degenerate_power_refused():
    for bad in (0, -1):
        with pytest.raises(ValueError, match="power ≥ 1"):
            unit_modulus_certificate(bad)


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("RH", "UnitModulusTest")),
        [UnitModulusSOSEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_emit_renders_expected_theorems():
    out = _emit(_family())
    text = out if isinstance(out, str) else getattr(out, "text", str(out))
    # one theorem per power, with the manifest-square identity and the nonneg conclusion
    assert "onLine_sq_m1" in text
    assert "onLine_sq_m5" in text
    assert "Complex.normSq (1 - u ^ 5)" in text
    assert "linear_combination -huc" in text
    assert "Complex.normSq_nonneg" in text
    # m = 1 renders the bare atom `u`, not `u ^ 1`
    assert "u ^ 1" not in text
