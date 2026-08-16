"""J+I tests: unimodality certificates and Farkas dual witnesses."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    FarkasDual,
    GridSpec,
    InequalityFamily,
    certify,
    cone_decide,
    unimodal_certificate,
)

u, v = sp.symbols("u v", nonnegative=True)


# ---- J: unimodality ---------------------------------------------------------
def test_unimodal_with_exact_tie():
    # r(s) = (s+10)/(2s+2): decreasing (r(s)-r(s+1) = 18/((2s+2)(2s+4)) > 0);
    # crosses 1 at s* = 8 with r(8) = 18/18 = 1 EXACTLY -> the R(5)=1 pattern
    cert = unimodal_certificate(lambda s: (s + 10) / (2 * s + 2), s0=1)
    assert cert.s_star == 8
    assert cert.exact_tie                       # max at BOTH 8 and 9
    assert cert.cross_lo > 1
    assert "EXACT TIE" in cert.render()


def test_unimodal_strict_crossing():
    # r(s) = (s+10)/(2s+3): crossing at s = 7 (17/17=1)? r(7)=17/17=1... use
    # (s+9)/(2s+2): r <= 1 iff s >= 7; r(7) = 16/16 = 1 tie again; take
    # (s+9)/(2s+3): r(6)=15/15=1 tie; (2s+4): r(5)=14/14... shift numerator:
    # r(s) = (s+8)/(2s+3): r<=1 iff s>=5; r(5)=13/13=1. Persistent ties are a
    # feature of integer shifts; use non-integer slope: r(s) = 20/(3s+2):
    # decreasing; r<=1 iff 3s>=18 iff s>=6; r(6)=1 EXACT again?! 20/20. Use
    # r(s) = 19/(3s+2): r(5)=19/17>1, r(6)=19/20<1 -> STRICT crossing at 6.
    cert = unimodal_certificate(lambda s: 19 / (3 * s + 2), s0=1)
    assert cert.s_star == 6
    assert not cert.exact_tie
    assert cert.cross_hi == sp.Rational(19, 20)
    assert cert.cross_lo == sp.Rational(19, 17)


def test_unimodal_refuses_increasing_ratio():
    # r(s) = (2s+2)/(s+10) is INCREASING -> not certifiably decreasing
    with pytest.raises(ValueError, match="not certifiably decreasing"):
        unimodal_certificate(lambda s: (2 * s + 2) / (s + 10), s0=1, search_hi=50)


def test_unimodal_no_crossing_reported():
    # r(s) = (s+2)/(s+1) > 1 always (decreasing toward 1, never <= 1)
    with pytest.raises(ValueError, match="no crossing"):
        unimodal_certificate(lambda s: (s + 2) / (s + 1), s0=1, search_hi=100)


def test_unimodal_origin_shaped_ratio():
    # the near-star shape in miniature: r(s) = c * (1 - 1/(4s^2+11s+7)) with
    # c slightly above 1 -> decreasing factor toward c... this r is INCREASING
    # in s (the bracket grows), so certify its reciprocal family instead:
    # f decreasing-ratio form r(s) = (1 + 1/s)^2 / (11/10):
    # r = 10(s+1)^2/(11 s^2): r(s)-r(s+1) > 0; crossing when 10(s+1)^2<=11s^2
    cert = unimodal_certificate(
        lambda s: 10 * (s + 1) ** 2 / (11 * s**2), s0=2, lift_max=4
    )
    assert cert.s_star == 21  # 10*22^2 = 4840 <= 11*441=4851 at s=21
    assert not cert.exact_tie


# ---- I: Farkas duals --------------------------------------------------------
def test_farkas_dual_for_inconsistent_system():
    # target has a monomial (v^2) no basis element can produce
    dual = cone_decide(u**2 + v**2, [u**2, u * v], (u, v))
    assert isinstance(dual, FarkasDual)
    assert dual.verify()
    assert dual.target_value > 0


def test_farkas_dual_for_negative_weight():
    # unique solution needs lambda = -1 on u*v
    dual = cone_decide(u**2 - u * v, [u**2, u * v], (u, v))
    assert isinstance(dual, FarkasDual)
    assert dual.verify()


def test_cone_decide_still_finds_memberships():
    from telperion import ConeCombination

    cc = cone_decide(2 * u**2 + 3 * u * v, [u**2, u * v], (u, v))
    assert isinstance(cc, ConeCombination)
    assert cc.weights == (2, 3)


# ---- I: complete witness spaces --------------------------------------------
def test_complete_witness_exhaustion_is_proven():
    fam = InequalityFamily(
        name="WC",
        symbols=(u,),
        grid=GridSpec([("a", [9])]),
        lean_name=lambda pt: "wc",
        witnesses=lambda pt: [(f"s{s}", (u + s - 9) / (1 + u)) for s in range(3)],
        witnesses_complete=True,
    )
    with pytest.raises(CertificationError, match="PROVEN IMPOSSIBLE"):
        certify(fam)
