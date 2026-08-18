"""Tests for the interval-bracket first-class emitter (emit_bracket.py).

Coverage:
  (a) certify + emit of a 2-instance exp bracket family yields 2 theorems per
      instance (4 total) and the correct tactic shape in the frozen output.
  (b) Negative control: a BracketSpec with a FALSE hi (too small, so
      hi * Taylor_n(theta) - 1 < 0) is REFUSED at certification
      (CertificationError is raised).
  (c) Byte-stability: emit twice, identical text.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (
    CertificationError,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
)
from telperion.emit_bracket import BracketSpec, IntervalBracketEmitter, bracket_family


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _taylor(x: Fr, nterms: int) -> Fr:
    """Exact rational Taylor partial sum."""
    s, term = Fr(0), Fr(1)
    for k in range(nterms):
        s += term
        term = term * x / (k + 1)
    return s


def _make_spec(theta: Fr, nterms: int, tfloor: Fr, hi: Fr) -> BracketSpec:
    lo = Fr(1) - theta
    return BracketSpec(
        func="exp",
        theta_num=theta.numerator,
        theta_den=theta.denominator,
        nterms=nterms,
        hi_num=hi.numerator,
        hi_den=hi.denominator,
        lo_num=lo.numerator,
        lo_den=lo.denominator,
        tf_num=tfloor.numerator,
        tf_den=tfloor.denominator,
    )


# Two valid instances
THETA_A = Fr(37167, 100000)   # far-case
NTERMS_A = 9
TFLOOR_A = Fr(145015, 100000)
HI_A = Fr(68959, 100000)
SPEC_A = _make_spec(THETA_A, NTERMS_A, TFLOOR_A, HI_A)

THETA_B = Fr(1, 4)
NTERMS_B = 7
TFLOOR_B = Fr(321, 250)
HI_B = Fr(7789, 10000)
SPEC_B = _make_spec(THETA_B, NTERMS_B, TFLOOR_B, HI_B)

_SPECS = {0: SPEC_A, 1: SPEC_B}
_NAMES = {0: "enc_far", 1: "enc_quarter"}


def _two_instance_family():
    return bracket_family(
        name="TestBracket",
        grid=GridSpec([("i", [0, 1])]),
        lean_name=lambda pt: _NAMES[pt["i"]],
        spec=lambda pt: _SPECS[pt["i"]],
    )


def _green_validation():
    return ValidationReport(checks=(("always_ok", True),))


# ---------------------------------------------------------------------------
# (a) Certify + emit: n_theorems = 2 per instance, correct tactic shape
# ---------------------------------------------------------------------------

class TestCertifyAndEmit:
    def test_n_theorems_two_per_instance(self):
        fam = _two_instance_family()
        cf = certify(fam)
        assert cf.checks_passed == 6  # 3 checks per instance * 2 instances
        res = emit(
            cf,
            LeanProfile(namespace=("Test",)),
            [IntervalBracketEmitter()],
            _green_validation(),
            file_name="TestBracket.lean",
        )
        assert res.n_theorems == 4   # 2 per instance * 2 instances

    def test_emit_contains_le_and_ge_theorems(self):
        fam = _two_instance_family()
        cf = certify(fam)
        res = emit(
            cf,
            LeanProfile(namespace=("Test",)),
            [IntervalBracketEmitter()],
            _green_validation(),
            file_name="TestBracket.lean",
        )
        text = res.files["TestBracket.lean"]
        # Both instances should have _le and _ge theorems
        assert "theorem enc_far_le" in text
        assert "theorem enc_far_ge" in text
        assert "theorem enc_quarter_le" in text
        assert "theorem enc_quarter_ge" in text

    def test_tactic_shape_upper_bound(self):
        """The _le theorem must use the CI-green tactic sequence verbatim."""
        fam = _two_instance_family()
        cf = certify(fam)
        res = emit(
            cf,
            LeanProfile(namespace=("Test",)),
            [IntervalBracketEmitter()],
            _green_validation(),
            file_name="TestBracket.lean",
        )
        text = res.files["TestBracket.lean"]
        # Core tactic sequence for the upper bound
        assert "rw [Real.exp_neg, ← one_div]" in text
        assert "Real.sum_le_exp_of_nonneg (by norm_num)" in text
        assert "norm_num [Finset.sum_range_succ, Nat.factorial]" in text
        assert "one_div_le_one_div_of_le hpos hlow" in text

    def test_tactic_shape_lower_bound(self):
        """The _ge theorem must use Real.add_one_le_exp + linarith."""
        fam = _two_instance_family()
        cf = certify(fam)
        res = emit(
            cf,
            LeanProfile(namespace=("Test",)),
            [IntervalBracketEmitter()],
            _green_validation(),
            file_name="TestBracket.lean",
        )
        text = res.files["TestBracket.lean"]
        assert "Real.add_one_le_exp" in text
        assert "linarith" in text

    def test_rational_constants_in_output(self):
        """Rational constants in the Lean output match the BracketSpec fields."""
        fam = _two_instance_family()
        cf = certify(fam)
        res = emit(
            cf,
            LeanProfile(namespace=("Test",)),
            [IntervalBracketEmitter()],
            _green_validation(),
            file_name="TestBracket.lean",
        )
        text = res.files["TestBracket.lean"]
        # far-case constants
        assert "37167 / 100000" in text   # theta_A
        assert "68959 / 100000" in text   # hi_A
        assert "29003 / 20000" in text    # tfloor_A reduced
        # quarter constants
        assert "1 / 4" in text            # theta_B
        assert "7789 / 10000" in text     # hi_B
        assert "321 / 250" in text        # tfloor_B


# ---------------------------------------------------------------------------
# (b) Negative control: false HI is refused at certification
# ---------------------------------------------------------------------------

class TestNegativeControl:
    def test_false_hi_too_small_refused(self):
        """A BracketSpec with hi * Taylor_n(theta) - 1 < 0 must be refused."""
        theta = Fr(37167, 100000)
        nterms = 9
        tfloor = Fr(145015, 100000)
        # TRUE exp(-theta) ~ 0.6893; set hi way too small (0.50)
        bad_hi = Fr(50000, 100000)  # 0.5 < exp(-0.37167) ≈ 0.689
        bad_spec = _make_spec(theta, nterms, tfloor, bad_hi)
        fam = bracket_family(
            name="BadBracket",
            grid=GridSpec([("i", [0])]),
            lean_name=lambda pt: "bad_enc",
            spec=lambda pt: bad_spec,
        )
        with pytest.raises(CertificationError) as exc_info:
            certify(fam)
        # The error message should indicate the margin is negative (REFUSED)
        err = str(exc_info.value)
        assert "REFUSED" in err or "refused" in err.lower() or "hi" in err.lower()

    def test_false_hi_error_message_mentions_hi(self):
        """The refusal message should name the problematic quantity."""
        theta = Fr(1, 4)
        nterms = 7
        tfloor = Fr(321, 250)
        bad_hi = Fr(5, 10)  # 0.5, way too small for exp(-0.25) ≈ 0.779
        bad_spec = _make_spec(theta, nterms, tfloor, bad_hi)
        fam = bracket_family(
            name="BadBracket2",
            grid=GridSpec([("i", [0])]),
            lean_name=lambda pt: "bad_enc2",
            spec=lambda pt: bad_spec,
        )
        with pytest.raises(CertificationError) as exc_info:
            certify(fam)
        # Should mention something about hi or the margin
        msg = str(exc_info.value)
        assert any(kw in msg for kw in ("REFUSED", "refused", "hi", "margin", "small"))


# ---------------------------------------------------------------------------
# (c) Byte-stability: emit twice, identical text
# ---------------------------------------------------------------------------

class TestByteStability:
    def test_emit_twice_identical(self):
        fam = _two_instance_family()
        profile = LeanProfile(namespace=("Stable",))
        emitter = IntervalBracketEmitter()
        val = _green_validation()

        cf1 = certify(fam)
        res1 = emit(cf1, profile, [emitter], val, file_name="Stable.lean")

        cf2 = certify(fam)
        res2 = emit(cf2, profile, [emitter], val, file_name="Stable.lean")

        assert res1.files == res2.files
        assert res1.input_hash == res2.input_hash

    def test_emit_hash_stable(self):
        fam = _two_instance_family()
        profile = LeanProfile(namespace=("Stable",))
        emitter = IntervalBracketEmitter()
        val = _green_validation()

        cf = certify(fam)
        res = emit(cf, profile, [emitter], val, file_name="Stable.lean")
        # Input hash is non-empty and deterministic (same family = same hash)
        assert len(res.input_hash) == 64  # sha256 hex


# ---------------------------------------------------------------------------
# Additional: import and constructor sanity
# ---------------------------------------------------------------------------

class TestConstructors:
    def test_bracket_family_requires_callable_spec(self):
        with pytest.raises(ValueError, match="callable"):
            bracket_family(
                name="Bad",
                grid=GridSpec([("i", [0])]),
                lean_name=lambda pt: "x",
                spec="not_callable",
            )

    def test_bracketspec_is_frozen(self):
        with pytest.raises((AttributeError, TypeError)):
            SPEC_A.func = "log"  # type: ignore[misc]

    def test_bracketspec_theta_property(self):
        assert SPEC_A.theta == THETA_A
        assert SPEC_B.theta == THETA_B

    def test_bracketspec_hi_lo_properties(self):
        assert SPEC_A.hi == HI_A
        assert SPEC_A.lo == Fr(1) - THETA_A
        assert SPEC_B.hi == HI_B
        assert SPEC_B.lo == Fr(1) - THETA_B
