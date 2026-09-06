"""Hyperbolicity emitter tests (#3, d=2).

`certify_hyperbolicity_point` chains a box-robust discriminant-nonnegativity
margin (`box_min_lower_bound`) into a per-degree real-rootedness claim.  The
emitter produces one forall-box `roots.card = 2` theorem per instance, closed by
the prelude lemma `hyperbolic_deg2_of_discrim_nonneg` (a≠0 from the box sign,
discriminant ≥ 0 from the box-robust nlinarith).  A box whose discriminant is
NOT provably nonnegative -- or whose leading-coefficient box straddles 0 -- is
REFUSED (ValueError, the negative control).
"""
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import certify  # noqa: E402
from telperion.certify import CertificationError  # noqa: E402
from telperion.emit_hyperbolicity import (  # noqa: E402
    HyperbolicityEmitter,
    hyperbolicity_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


def _grid_one() -> GridSpec:
    return GridSpec([("i", [0])])


def _profile() -> LeanProfile:
    return LeanProfile(
        namespace=("HyperbolicityDemo",),
        imports=("Mathlib", "HyperbolicityBridge"),
    )


def test_refuses_negative_discriminant():
    # box for a=c2, b=c1, c=c0 with c1^2 - 4 c0 c2 < 0 must refuse.  Precise:
    # certify() wraps the arm's ValueError refusal in a CertificationError; assert
    # on the exact type + reason so an unrelated crash cannot pass this gate.
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h0",
        lambda pt: ([(F(1), F(1)), (F(1), F(1)), (F(1), F(1))], 2))  # disc = 1-4 = -3
    with pytest.raises(CertificationError, match="discriminant lower bound"):
        certify(fam)


def test_refuses_leading_straddles_zero():
    # a2 box straddles 0 -> cannot prove a ≠ 0 -> refuse (even if disc ok).
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h0",
        lambda pt: ([(F(-1), F(-1)), (F(0), F(0)), (F(-1), F(1))], 2))
    with pytest.raises(CertificationError, match="straddles 0"):
        certify(fam)


def test_refuses_non_deg2():
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h0",
        lambda pt: ([(F(-1), F(-1)), (F(0), F(0)), (F(0), F(0)), (F(1), F(1))], 3))
    with pytest.raises(CertificationError, match="only degree d=2 is supported"):
        certify(fam)


def test_emit_real_rooted_quadratic():
    # a real-rooted quadratic box: a0=-1..-1, a1=0..0, a2=1..1 -> x^2 - 1,
    # disc = 0 - 4*(-1)*1 = 4 > 0.
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h_x2m1",
        lambda pt: ([(F(-1), F(-1)), (F(0), F(0)), (F(1), F(1))], 2))
    text, n = HyperbolicityEmitter().emit_body(certify(fam), _profile())
    assert "roots.card = 2" in text and "hyperbolic_deg2_of_discrim_nonneg" in text


def test_emit_second_family():
    # x^2 - 3x + 2: a0=2, a1=-3, a2=1, disc = 9 - 8 = 1 > 0.
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h_x2m3xp2",
        lambda pt: ([(F(2), F(2)), (F(-3), F(-3)), (F(1), F(1))], 2))
    text, n = HyperbolicityEmitter().emit_body(certify(fam), _profile())
    assert n == 1
    assert "roots.card = 2" in text
    # the gate example is single-sourced with the theorem type.
    assert "example :" in text and "hyperbolic_deg2_of_discrim_nonneg" in text


def test_leading_sign_negative_box():
    # a2 all-negative box: a0=1, a1=0, a2=-1 -> -x^2 + 1, disc = 0 - 4*(-1)*1 = 4 > 0.
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h_neg",
        lambda pt: ([(F(1), F(1)), (F(0), F(0)), (F(-1), F(-1))], 2))
    text, n = HyperbolicityEmitter().emit_body(certify(fam), _profile())
    assert "roots.card = 2" in text
