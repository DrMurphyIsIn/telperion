"""exp_enclosure emitter -- kernel-checked rational brackets of Real.exp from Real.exp_bound.

The shape: for a rational `x` with `|x| <= 1`, Mathlib's `Real.exp_bound` gives the order-`n`
Taylor box `[S_n - r_n, S_n + r_n]` around `Real.exp x` with `S_n = sum_{m<n} x^m/m!` and
`r_n = |x|^n * (n+1)/(n! * n)`, both EXACT rationals.  The certificate is a CLAIMED rational
bracket `[lo, hi]`; it is honest exactly when the Taylor box is contained in it, and the
generator refuses every claim the box does not imply (the forge face) instead of widening it.

This reflects into the kernel the Arb `hexp` seam that `BraggDefect.bragg_defect_witness`
carries as a hypothesis, and brackets the recurrence deficit `e^d + e^-d - 2` (QC_RECURRENCE
row a).  The Lean kernel is the arbiter (the zzl_aux island build of
`ExpEnclosureInstances`); these are the pre-CI self-checks.

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    ExpEnclosureEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    exp_enclosure_certificate,
    exp_enclosure_family,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

# BraggDefect.lean:68-69 -- the Arb enclosure of e^(1/10) that `hexp` carries.
_BD = Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean" / "BraggDefect.lean"
_EXP_LO = sp.Rational(442068367230259049924676660787771898883,
                      400000000000000000000000000000000000000)
_EXP_HI = sp.Rational(11051709180756476248117094953514706601127,
                      10000000000000000000000000000000000000000)
# BraggDefect.excess_bracket -- the deficit e^(1/10) + e^(-1/10) - 2 constants.
_D_LO = sp.Rational(
    44243688035498337190547890814412959087189025996450853896963629856431657841141,
    4420683672302590499246837981405882640450800000000000000000000000000000000000000)
_D_HI = sp.Rational(
    44243688035498337190690637870740262328789025996450853896963629856431657841141,
    4420683672302590499246766607877718988830000000000000000000000000000000000000000)


def _taylor_box(x, n):
    x = Fraction(int(sp.Rational(x).p), int(sp.Rational(x).q))
    S = sum(x ** m / factorial(m) for m in range(n))
    r = abs(x) ** n * Fraction(n + 1, factorial(n) * n)
    return S - r, S + r


def _spec(**kw):
    return lambda pt: dict(kw)


# --- registry wiring --------------------------------------------------------

def test_kind_is_exp_enclosure():
    fam = exp_enclosure_family("T", GridSpec([("i", [0])]), lambda pt: "t",
                               spec=_spec(x="1/10", lo=_EXP_LO, hi=_EXP_HI))
    assert fam.kind == "exp_enclosure"


def test_emitter_for_round_trips():
    assert emitter_for("exp_enclosure").kind == "exp_enclosure"


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY
    from telperion.negative_control_harness import ADAPTERS
    assert "ExpEnclosureEmitter" in REGISTRY
    stance = REGISTRY["ExpEnclosureEmitter"]
    assert stance.reason.strip()
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "ExpEnclosureEmitter" in ADAPTERS


# --- the certificate --------------------------------------------------------

def test_positive_cert_tenth_fits_taylor_box():
    cert = exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    assert cert.mode == "exp"
    lo_box, hi_box = _taylor_box("1/10", cert.n)
    # the claimed bracket CONTAINS the Taylor box (that containment IS the proof)
    assert Fraction(int(cert.lo.p), int(cert.lo.q)) <= lo_box
    assert hi_box <= Fraction(int(cert.hi.p), int(cert.hi.q))
    # the certificate's own exact partial sum / remainder reproduce the box
    assert cert.partial_sum - cert.remainder == sp.Rational(lo_box.numerator, lo_box.denominator)
    assert cert.partial_sum + cert.remainder == sp.Rational(hi_box.numerator, hi_box.denominator)


def test_least_order_selection():
    """The generator picks the LEAST order whose box fits, and no smaller order fits."""
    cert = exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    assert cert.n == 14
    for n in range(1, cert.n):
        lo_box, hi_box = _taylor_box("1/10", n)
        fits = (Fraction(int(_EXP_LO.p), int(_EXP_LO.q)) <= lo_box
                and hi_box <= Fraction(int(_EXP_HI.p), int(_EXP_HI.q)))
        assert not fits, f"order {n} already fits -- {cert.n} is not least"


def test_reads_bragg_defect_literals_verbatim():
    """The instance (i) bracket is BraggDefect's expLo/expHi, read from the island source."""
    src = _BD.read_text(encoding="utf-8")
    assert f"noncomputable def expLo : ℝ := ({_EXP_LO.p} / {_EXP_LO.q} : ℝ)" in src
    assert f"noncomputable def expHi : ℝ := ({_EXP_HI.p} / {_EXP_HI.q} : ℝ)" in src
    cert = exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    assert cert.lo == _EXP_LO and cert.hi == _EXP_HI


def test_deficit_mode_matches_bragg_defect_constants():
    """Deficit mode at x = 1/10 accepts BraggDefect.excess_bracket's own constants."""
    cert = exp_enclosure_certificate(x="1/10", lo=_D_LO, hi=_D_HI, mode="deficit")
    assert cert.mode == "deficit"
    plo, phi = _taylor_box("1/10", cert.n)
    mlo, mhi = _taylor_box("-1/10", cert.n)
    assert Fraction(int(_D_LO.p), int(_D_LO.q)) <= plo + mlo - 2
    assert phi + mhi - 2 <= Fraction(int(_D_HI.p), int(_D_HI.q))
    # BOTH brackets are carried
    assert cert.partial_sum_neg is not None
    assert cert.partial_sum_neg == sum(sp.Rational(-1, 10) ** m / factorial(m)
                                       for m in range(cert.n))


def test_deficit_mode_second_channel_fifth():
    """defect_eq_two's second channel d = 1/5 also certifies."""
    cert = exp_enclosure_certificate(
        x="1/5", mode="deficit",
        lo=sp.Rational(40133511238151692591, 10 ** 21),
        hi=sp.Rational(401335112381516925911, 10 ** 22))
    assert 1 <= cert.n <= 64


def test_cosh_mode_matches_zoodh_constants():
    """cosh face: ZooDH's order-6 cosh bracket constants at x = 21487557/1e8 certify."""
    cert = exp_enclosure_certificate(
        x="21487557/100000000", mode="cosh",
        lo=sp.Rational(511587210574920885840517, 500000000000000000000000),
        hi=sp.Rational(511587370066054060481853, 500000000000000000000000))
    assert cert.mode == "cosh"
    assert 1 <= cert.n <= 64


# --- anti-phantom refusals (one test each) ----------------------------------

def test_refuses_abs_gt_one():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="3/2", lo=sp.Rational(4), hi=sp.Rational(5))


def test_refuses_order_below_one():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI, n=0)


def test_refuses_order_above_cap():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI, n=65)


def test_refuses_inverted_bracket():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="1/10", lo=_EXP_HI, hi=_EXP_LO)


def test_refuses_bracket_not_implied():
    """THE FORGE CASE: a claimed hi BELOW the Taylor upper endpoint at every order <= 64."""
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="1/10", lo=sp.Rational(1), hi=sp.Rational(1105, 1000))


def test_refuses_deficit_nonpositive():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="0", lo=sp.Rational(-1), hi=sp.Rational(1), mode="deficit")


def test_refuses_non_rational_input():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x=sp.sqrt(2) / 2, lo=sp.Rational(1), hi=sp.Rational(3))
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x=0.1, lo=_EXP_LO, hi=_EXP_HI)


def test_refuses_unknown_mode():
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(x="1/10", lo=_EXP_LO, hi=_EXP_HI, mode="sinh")


def test_certify_propagates_the_refusal():
    fam = exp_enclosure_family("Bad", GridSpec([("i", [0])]), lambda pt: "bad",
                               spec=_spec(x="1/10", lo=sp.Rational(1),
                                          hi=sp.Rational(1105, 1000)))
    # certify wraps the arm's ValueError in a CertificationError; the refusal text survives.
    with pytest.raises(Exception, match="REFUSED"):
        certify(fam)


# --- emission ---------------------------------------------------------------

def _emit_text(**kw):
    fam = exp_enclosure_family("ExpEnclosureTest", GridSpec([("i", [0])]),
                               lambda pt: kw.pop("name", "t_inst"), spec=_spec(**kw))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ExpEnclosureTest",), imports=("Mathlib",)),
        [ExpEnclosureEmitter()],
        ValidationReport(checks=(("exp_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def test_emit_is_lint_clean_and_deterministic():
    txt = _emit_text(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    again = _emit_text(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    assert txt == again, "emission is not byte-deterministic"
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == [], errs
    assert "sorry" not in txt and "admit" not in txt
    assert "Real.exp_bound" in txt
    assert "conjecture1_proved = False" in txt
    # the claimed literals appear verbatim in the statement
    assert f"{_EXP_LO.p} / {_EXP_LO.q}" in txt
    assert f"{_EXP_HI.p} / {_EXP_HI.q}" in txt


def test_emit_deficit_renders_both_faces():
    txt = _emit_text(x="1/10", lo=_D_LO, hi=_D_HI, mode="deficit")
    assert "theorem t_inst_pos" in txt
    assert "theorem t_inst_neg" in txt
    assert "Real.exp ((1 / 10)) + Real.exp (-((1 / 10))) - 2" in txt
    assert "abs_neg" in txt
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == []


def test_emit_cosh_renders_cosh_eq():
    txt = _emit_text(x="21487557/100000000", mode="cosh",
                     lo=sp.Rational(511587210574920885840517, 500000000000000000000000),
                     hi=sp.Rational(511587370066054060481853, 500000000000000000000000))
    assert "Real.cosh" in txt and "Real.cosh_eq" in txt
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == []


def test_no_emoji_in_emitted_lean():
    txt = _emit_text(x="1/10", lo=_EXP_LO, hi=_EXP_HI)
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"
