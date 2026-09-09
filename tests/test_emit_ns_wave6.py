"""NS/Euler wave-6 emitters (graded_convolution, power_tower,
partition_composition, regular_word, low_order_tail, eventual_threshold):
certify → emit → lint + refusals."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    eventual_threshold_certificate, eventual_threshold_family,
    graded_convolution_family,
    low_order_tail_family,
    partition_composition_family,
    power_tower_family,
    regular_word_family,
)
from telperion.emit_eventual_threshold import EventualThresholdEmitter  # noqa: E402
from telperion.emit_graded_convolution import GradedConvolutionEmitter  # noqa: E402
from telperion.emit_low_order_tail import LowOrderTailEmitter  # noqa: E402
from telperion.emit_partition_composition import PartitionCompositionEmitter  # noqa: E402
from telperion.emit_power_tower import PowerTowerEmitter  # noqa: E402
from telperion.emit_regular_word import RegularWordEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text

_VR = ValidationReport(checks=(("s", True),))
_G = GridSpec([("k", [0])])


def _emit(fam, em, ns):
    return emit(certify(fam), LeanProfile(namespace=("NS", ns)), [em], _VR)


def test_graded_convolution_atoms():
    fam = graded_convolution_family(name="GCChk", grid=_G, lean_name=lambda pt: "g")
    text = _emit(fam, GradedConvolutionEmitter(), "GC").files["GCChk.lean"]
    for nm in ("def gconv", "gconv_congr_below", "gconv_strict_congr", "gconv_next_delta"):
        assert nm in text
    check_lean_text(text)


def test_power_tower_atoms():
    fam = power_tower_family(name="PTChk", grid=_G, lean_name=lambda pt: "p")
    text = _emit(fam, PowerTowerEmitter(), "PT").files["PTChk.lean"]
    for nm in ("succ_le_three_pow", "inverse_majorant_dominates",
               "inverse_majorant_step", "power_tower_closure"):
        assert f"theorem {nm}" in text
    check_lean_text(text)


def test_partition_composition_capstone():
    fam = partition_composition_family(name="PCChk", grid=_G, lean_name=lambda pt: "c")
    text = _emit(fam, PartitionCompositionEmitter(), "PC").files["PCChk.lean"]
    assert "theorem partitionSum_le" in text
    assert "OrderedFinpartition" in text
    assert "extendEquiv" in text
    check_lean_text(text)


def test_regular_word_atoms():
    fam = regular_word_family(name="RWChk", grid=_G, lean_name=lambda pt: "w")
    text = _emit(fam, RegularWordEmitter(), "RW").files["RWChk.lean"]
    assert "def GoodWord" in text and "theorem goodWord_losses" in text
    assert "termination_by" in text
    check_lean_text(text)


def test_low_order_tail_atoms():
    fam = low_order_tail_family(name="LTChk", grid=_G, lean_name=lambda pt: "t")
    text = _emit(fam, LowOrderTailEmitter(), "LT").files["LTChk.lean"]
    for nm in ("sum_geometric_le_two", "sum_geometric_Ico_le", "weighted_low_high_sum_le"):
        assert f"theorem {nm}" in text
    check_lean_text(text)


def test_eventual_threshold_arities():
    fam = eventual_threshold_family(
        name="ETChk", grid=GridSpec([("k", [0, 1, 2])]),
        lean_name=lambda pt: f"thresh_{pt['k']}", spec=lambda pt: [1, 2, 4][pt["k"]])
    text = _emit(fam, EventualThresholdEmitter(), "ET").files["ETChk.lean"]
    assert "theorem thresh_0" in text and "theorem thresh_2" in text
    assert "div_lt_iff₀" in text and "le_max_left" in text
    check_lean_text(text)


def test_eventual_threshold_refusal():
    with pytest.raises(ValueError, match="arity"):
        eventual_threshold_certificate(0)
    with pytest.raises(ValueError, match="arity"):
        eventual_threshold_certificate(7)


def test_byte_stability():
    fam = eventual_threshold_family(
        name="ETChk", grid=_G, lean_name=lambda pt: "t", spec=lambda pt: 3)
    a = _emit(fam, EventualThresholdEmitter(), "ET").files["ETChk.lean"]
    b = _emit(fam, EventualThresholdEmitter(), "ET").files["ETChk.lean"]
    assert a == b
