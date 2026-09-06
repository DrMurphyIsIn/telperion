"""emit_borel_caratheodory emits a well-typed re-export of Mathlib's Complex.borelCaratheodory
(both dogfood theorems are kernel-verified in examples/zero_free_bridge/lean/EmittedShapes.lean)."""
import pytest

from telperion.emit_borel_caratheodory import emit_borel_caratheodory_cert, BC_LEMMA


def test_general_form():
    cert = emit_borel_caratheodory_cert("bc_g")
    assert "theorem bc_g {f : ℂ → ℂ}" in cert
    assert "(hM : 0 < M)" in cert and "DifferentiableOn ℂ f (Metric.ball 0 R)" in cert
    assert "Set.MapsTo f (Metric.ball 0 R) {z | z.re ≤ M}" in cert
    assert "‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)" in cert
    assert cert.rstrip().endswith("Complex.borelCaratheodory hM hf hf₁ hR hz")


def test_zero_form():
    cert = emit_borel_caratheodory_cert("bc_z", form="zero")
    assert "(hf₂ : f 0 = 0)" in cert
    assert "‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=" in cert
    assert cert.rstrip().endswith("Complex.borelCaratheodory_zero hM hf hf₁ hR hz hf₂")


def test_lemma_names():
    assert BC_LEMMA["general"] == "Complex.borelCaratheodory"
    assert BC_LEMMA["zero"] == "Complex.borelCaratheodory_zero"


def test_rejects_bad_form():
    with pytest.raises(ValueError, match="form must be"):
        emit_borel_caratheodory_cert("bad", form="derivative")
