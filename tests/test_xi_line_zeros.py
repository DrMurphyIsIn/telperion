"""xi_line_zeros emitter tests (Stage 1 core -- on-line zero count via sign changes).

`sign_change_count(samples)` counts alternations between consecutive SIGN-DEFINITE
real boxes (a box is positive if lo > 0, negative if hi < 0, straddling otherwise).
`certify_xi_line_zeros_point` builds the samples via the family spec and REFUSES
(ValueError -> CertificationError) when there is no sign change (nothing to prove).
The emitter produces one theorem per instance asserting >= N zeros of the completed
Riemann zeta Lambda on the critical line Re = 1/2 in [a, b], each obtained by the
intermediate value theorem on `g t := (completedRiemannZeta (1/2 + t*I)).re` (real
by the Task-2 prelude `completedZeta_im_eq_zero`).  The enclosure hypotheses
`g t_i in [lo_i, hi_i]` are documented Arb-certified NON-KERNEL inputs.
conjecture1_proved = False.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import certify  # noqa: E402
from telperion.certify import CertificationError  # noqa: E402
from telperion.emit_xi_line_zeros import (  # noqa: E402
    XiLineZerosEmitter,
    sign_change_count,
    xi_line_zeros_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


def _grid_one() -> GridSpec:
    return GridSpec([("i", [0])])


def _profile() -> LeanProfile:
    return LeanProfile(
        namespace=("XiLineZerosDemo",),
        imports=("Mathlib", "LambdaLineReal"),
    )


def test_sign_change_count_counts_alternations():
    # boxes: +, +, -, +  -> 2 sign changes (+ to -, - to +)
    samples = [
        (F(10), (F(1), F(2))),
        (F(11), (F(1), F(2))),
        (F(12), (F(-2), F(-1))),
        (F(13), (F(1), F(2))),
    ]
    assert sign_change_count(samples) == 2


def test_sign_change_count_ignores_straddling():
    # +, straddle, -, straddle, +  -> 2 sign changes (the straddling boxes are
    # skipped for sign purposes: + -> - -> +).
    samples = [
        (F(0), (F(1), F(2))),
        (F(1), (F(-1), F(1))),
        (F(2), (F(-2), F(-1))),
        (F(3), (F(-1), F(1))),
        (F(4), (F(1), F(2))),
    ]
    assert sign_change_count(samples) == 2


def test_sign_change_count_all_positive_is_zero():
    samples = [(F(0), (F(1), F(2))), (F(1), (F(3), F(4)))]
    assert sign_change_count(samples) == 0


def test_refuses_when_no_valid_alternation():
    # all positive -> 0 changes; certify must refuse (nothing to prove)
    fam = xi_line_zeros_family(
        "Z", (), _grid_one(), lambda pt: "z0",
        lambda pt: (F(10), F(13),
                    [(F(10), (F(1), F(2))), (F(11), (F(1), F(2)))]),
    )
    with pytest.raises(CertificationError, match="no sign change"):
        certify(fam)


def test_emit_produces_zero_existence_theorem():
    fam = xi_line_zeros_family(
        "Z", (), _grid_one(), lambda pt: "z_demo",
        lambda pt: (F(10), F(13),
                    [(F(10), (F(1), F(2))),
                     (F(12), (F(-2), F(-1))),
                     (F(13), (F(1), F(2)))]),
    )
    text, n = XiLineZerosEmitter().emit_body(certify(fam), _profile())
    assert n == 1 and "completedRiemannZeta" in text and "= 0" in text


def test_emit_two_zeros_from_two_sign_changes():
    # +, -, +  -> 2 sign changes -> asserts 2 distinct zeros.
    fam = xi_line_zeros_family(
        "Z", (), _grid_one(), lambda pt: "z_two",
        lambda pt: (F(10), F(20),
                    [(F(10), (F(1), F(2))),
                     (F(13), (F(-2), F(-1))),
                     (F(16), (F(1), F(2)))]),
    )
    text, n = XiLineZerosEmitter().emit_body(certify(fam), _profile())
    assert n == 1
    # two existentially quantified roots, both zeros of Lambda, strictly ordered.
    assert text.count("completedRiemannZeta") >= 2
    assert "example :" in text  # single-sourced statement-match gate
    # the body bridges to the real part via the prelude lemma `lambda_eq_gLine`
    # (which is itself proved from the Task-2 `completedZeta_im_eq_zero`).
    assert "lambda_eq_gLine" in text


def test_emit_gate_single_sourced():
    fam = xi_line_zeros_family(
        "Z", (), _grid_one(), lambda pt: "z_gate",
        lambda pt: (F(14), F(15),
                    [(F(14), (F(1), F(2))), (F(15), (F(-2), F(-1)))]),
    )
    text, n = XiLineZerosEmitter().emit_body(certify(fam), _profile())
    assert n == 1 and "example :" in text
