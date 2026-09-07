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
    choose_ball,
    emit_per_box_instantiation,
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


# ---------------------------------------------------------------------------
# Task-4 driver refusals: invalid box (sigma-range excludes 1/2, or box contains s = 1).
# ---------------------------------------------------------------------------

def test_box_localization_refuses_sigma_range_excluding_half():
    # A box whose real-range does not straddle 1/2 cannot localize RH -> refused.
    with pytest.raises(ValueError, match="straddle|1/2|invalid box"):
        box_localization_certificate(n_line=5, n_total=5, re_lo="3/5", re_hi="4/5",
                                     im_lo="10", im_hi="35")


def test_box_localization_refuses_box_containing_pole():
    # A box whose real-range contains 1 AND imag-range contains 0 contains the pole s = 1.
    with pytest.raises(ValueError, match="pole|s = 1|invalid box"):
        box_localization_certificate(n_line=1, n_total=1, re_lo="1/2", re_hi="3/2",
                                     im_lo="-1", im_hi="1")


def test_box_localization_certificate_refuses_invalid_box_via_count_and_range():
    # Brief's Step-1 test: n_line != n_total refused (already), AND an invalid sigma-range refused.
    with pytest.raises(ValueError):
        box_localization_certificate(n_line=6, n_total=5, re_lo="2/5", re_hi="3/5",
                                     im_lo="0", im_hi="100")


def test_box_localization_accepts_valid_strip_box():
    # [2/5, 3/5] x [0, 100] straddles 1/2 and excludes s = 1 (im-range [0,100] contains 0 but
    # re-range [2/5,3/5] excludes 1) -> accepted.
    cert = box_localization_certificate(n_line=29, n_total=29, re_lo="2/5", re_hi="3/5",
                                        im_lo="0", im_hi="100")
    assert cert.n == 29


# ---------------------------------------------------------------------------
# Task-4 ball selection + per-box instantiation emitter (pure-Python; no flint/lake).
# ---------------------------------------------------------------------------

def test_choose_ball_strictly_separates_box_from_pole():
    import sympy as sp
    cx, cy, rsq = choose_ball("2/5", "3/5", "10", "35")
    # box center (1/2, 45/2); corner^2 < rsq < pole^2 so box strictly inside, pole outside.
    dc2 = (sp.Rational(1, 10)) ** 2 + (sp.Rational(25, 2)) ** 2
    d12 = (1 - cx) ** 2 + cy ** 2
    assert dc2 < rsq < d12


def test_emit_per_box_instantiation_instantiates_generic_theorem():
    cert = box_localization_certificate(5, 5, "2/5", "3/5", "10", "35")
    txt = emit_per_box_instantiation(cert, "2d5_3d5_10_35", namespace="RHInBox_probe")
    # It INSTANTIATES the generic capstone.
    assert "RHInBox.rh_in_box_of_certificate" in txt
    # It imports the generic theorem module.
    assert "import RHInBox" in txt
    # It takes the two documented Arb inputs.
    assert "hLine" in txt and "hArb" in txt
    # It supplies the on-line Finset T and a count equality N = T.card.
    assert "T.card" in txt
    # N = 5 existential of five strictly-increasing on-line completed-zeta zeros.
    assert "x1 x2 x3 x4 x5" in txt
    # conjecture1_proved discipline.
    assert "conjecture1_proved = False" in txt


def test_emit_per_box_instantiation_general_N():
    # The emitter is generic in N: N=1 (single-element Finset) and N=3 both emit.
    for n in (1, 3):
        cert = box_localization_certificate(n, n, "2/5", "3/5", "10", "35")
        txt = emit_per_box_instantiation(cert, f"n{n}", namespace=f"RHInBox_n{n}")
        assert "RHInBox.rh_in_box_of_certificate" in txt
        # N existential binders x1..xN.
        assert " ".join(f"x{i}" for i in range(1, n + 1)) in txt
