"""box_localization emitter: emit-shape + negative-control refusal tests (Stage 3 capstone).

The emitted `box_localization_<name>` is the counting exhaustion step (total divisor = on-line
count ⟹ every zero in the box is on Re=1/2).  It is real-geometry: the integral is already
discharged upstream, so the emitted body must NOT re-derive a `2πi` winding.  The certificate is the
negative-control gate: `n_line > n_total` (impossible) and `n_line != n_total` (no exhaustion) are
REFUSED.  conjecture1_proved = False.
"""
import pytest

from telperion.emit_box_localization import (
    BoxLocalizationEmitter,
    box_localization_certificate,
    box_localization_family,
    certify_box_localization_point,
)
from telperion.family import GridSpec
from telperion.lean import LeanProfile


def _emit(n_line=5, n_total=5):
    fam = box_localization_family(
        "T", GridSpec([("case", [0])]), lambda pt: "box_localization_a",
        spec=lambda pt: {"n_line": n_line, "n_total": n_total},
    )
    inst, _ = certify_box_localization_point(fam, {"case": 0}, "box_localization_a")

    class _V:
        instances = [inst]

    return BoxLocalizationEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))


def test_box_localization_emits_all_zeros_on_line():
    body, nthm = _emit(5, 5)
    assert nthm == 1
    # The capstone concludes every zero is on the critical line.
    assert "re = 1 / 2" in body.replace("  ", " ")
    # Real-geometry: the integral/winding is already discharged upstream.
    assert "2 * π * I" not in body
    assert "∮" not in body
    # It is a genuine counting theorem over a Finset support.
    assert "theorem box_localization_a" in body
    assert "∑ ρ ∈ s, d ρ" in body
    assert "Finset.sum_sdiff" in body


def test_box_localization_refuses_n_line_gt_n_total():
    with pytest.raises(ValueError, match="n_line.*n_total|exceeds"):
        box_localization_certificate(n_line=6, n_total=5)  # impossible; refuse


def test_box_localization_refuses_n_line_ne_n_total():
    with pytest.raises(ValueError, match="n_line.*n_total|exhaust"):
        box_localization_certificate(n_line=4, n_total=5)  # no exhaustion; refuse


def test_box_localization_refuses_vacuous():
    with pytest.raises(ValueError, match="n_line >= 1|non-vacuous"):
        box_localization_certificate(n_line=0, n_total=0)


def test_box_localization_positive_certificate():
    cert = box_localization_certificate(5, 5)
    assert cert.n == 5
    assert str(cert.re_lo) == "2/5" and str(cert.re_hi) == "3/5"
    assert str(cert.im_lo) == "10" and str(cert.im_hi) == "35"


def test_box_localization_registered_everywhere():
    # certify.py _SPECIAL_KINDS + _SPECIAL_DISPATCH, emitter_sensitivity REGISTRY, __init__ export.
    from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS
    assert "box_localization" in _SPECIAL_KINDS
    assert "box_localization" in _SPECIAL_DISPATCH
    from telperion.emitter_sensitivity import REGISTRY
    assert "BoxLocalizationEmitter" in REGISTRY
    import telperion
    assert hasattr(telperion, "BoxLocalizationEmitter")
