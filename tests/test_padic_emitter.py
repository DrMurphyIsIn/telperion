"""Tests for the p-adic valuation first-class emitter (emit_padic.py).

Covers:
  (a) certify + emit of a small valuation family: expected n_theorems and
      the norm_num divisibility shape;
  (b) negative control: a ValuationFact with a wrong k is REFUSED at
      certification (certify raises CertificationError);
  (c) byte-stability: emit twice, assert identical text.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    GridSpec,
    LeanProfile,
    ValuationFact,
    ValidationReport,
    certify,
    emit,
)
from telperion.emit_padic import (  # noqa: E402
    PadicValuationEmitter,
    certify_valuation_point,
    valuation_family,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _small_family(facts_fn, name="TestValuation", grid=None):
    """Build a minimal valuation family for testing."""
    if grid is None:
        grid = GridSpec([("i", [0])])
    return valuation_family(
        name=name,
        grid=grid,
        lean_name=lambda pt: f"node_{pt['i']}" if "i" in pt else "node_0",
        facts=facts_fn,
    )


def _green_validation():
    return ValidationReport(checks=(("always_ok", True),))


def _do_emit(fam):
    cf = certify(fam)
    prof = LeanProfile(namespace=("PadicTest",))
    vr = _green_validation()
    return emit(cf, prof, [PadicValuationEmitter()], vr,
                file_name="Test.lean")


# ---------------------------------------------------------------------------
# (a) certify + emit: expected n_theorems and norm_num shape
# ---------------------------------------------------------------------------

def test_certify_and_emit_basic():
    """A two-fact family certifies and emits exactly 2 norm_num theorems."""
    facts_fn = lambda pt: [
        ValuationFact("v23_621", 621, 23, 1),    # 23^1 | 621, 23^2 does not
        ValuationFact("v23_64",  64,  23, 0),    # 1 | 64, 23 does not
    ]
    fam = _small_family(facts_fn)
    res = _do_emit(fam)
    assert res.n_theorems == 2, f"expected 2, got {res.n_theorems}"

    text = res.files["Test.lean"]
    # Both theorems must use the norm_num divisibility shape
    assert "theorem v23_621 : (23 ∣ 621) ∧ ¬ (529 ∣ 621) := by norm_num" in text
    assert "theorem v23_64 : (1 ∣ 64) ∧ ¬ (23 ∣ 64) := by norm_num" in text


def test_certify_single_fact():
    """A single-fact family emits exactly one theorem."""
    facts_fn = lambda pt: [ValuationFact("v23_hub", 23 ** 11, 23, 11)]
    fam = _small_family(facts_fn)
    res = _do_emit(fam)
    assert res.n_theorems == 1

    text = res.files["Test.lean"]
    # 23^11 | 23^11 and 23^12 does not divide 23^11
    pk = 23 ** 11
    pk1 = 23 ** 12
    expected = f"theorem v23_hub : ({pk} ∣ {pk}) ∧ ¬ ({pk1} ∣ {pk}) := by norm_num"
    assert expected in text, f"norm_num shape missing; got:\n{text}"


def test_certify_n_checks_equals_n_facts():
    """certify reports n_checks equal to the number of ValuationFacts checked."""
    n_facts = 3
    facts_fn = lambda pt: [
        ValuationFact("v23_a", 621,        23, 1),
        ValuationFact("v23_b", 64,         23, 0),
        ValuationFact("v23_c", 23 ** 11,   23, 11),
    ]
    fam = _small_family(facts_fn)
    cf = certify(fam)
    assert cf.checks_passed == n_facts


def test_certify_multi_node_grid():
    """A two-point grid family produces facts for every grid node."""
    def facts_fn(pt):
        if pt["i"] == 0:
            return [ValuationFact("v23_root_den", 621, 23, 1)]
        else:
            return [ValuationFact("v23_child_den", 87946907297998046875, 23, 9)]

    fam = valuation_family(
        name="MultiNodeTest",
        grid=GridSpec([("i", [0, 1])]),
        lean_name=lambda pt: f"node_{pt['i']}",
        facts=facts_fn,
    )
    res = _do_emit(fam)
    assert res.n_theorems == 2

    text = res.files["Test.lean"]
    assert "v23_root_den" in text
    assert "v23_child_den" in text


# ---------------------------------------------------------------------------
# (b) Negative control: wrong k is REFUSED
# ---------------------------------------------------------------------------

def test_wrong_k_refused():
    """A ValuationFact claiming v23(621) = 2 (actual: 1) must be refused.

    certify() should raise CertificationError (not produce any Lean) when a
    fact fails its exact re-derivation check.
    """
    wrong_facts_fn = lambda pt: [
        ValuationFact("v23_621_wrong", 621, 23, 2)  # wrong: 23^2 does not divide 621
    ]
    fam = _small_family(wrong_facts_fn, name="BadValuation")

    with pytest.raises(CertificationError) as exc_info:
        certify(fam)

    # The error message should name the fact and show the correct valuation
    msg = str(exc_info.value)
    assert "v23_621_wrong" in msg, f"fact name missing from error: {msg}"
    assert "REFUSED" in msg, f"REFUSED not in error: {msg}"
    # Should show the discrepancy: claimed 2, engine says 1
    assert "2" in msg and "1" in msg, f"valuation numbers missing from error: {msg}"


def test_wrong_k_refused_direct():
    """certify_valuation_point itself raises ValueError on a wrong fact."""
    from telperion import GridSpec, InequalityFamily

    fam = _small_family(
        lambda pt: [ValuationFact("v23_bad", 621, 23, 2)]
    )
    pt = {"i": 0}
    with pytest.raises(ValueError, match="REFUSED"):
        certify_valuation_point(fam, pt, "test")


def test_correct_k_accepted_then_wrong_refused():
    """Correct facts pass; the same family with one wrong fact is refused."""
    good = lambda pt: [ValuationFact("v23_ok", 621, 23, 1)]
    bad  = lambda pt: [ValuationFact("v23_bad", 621, 23, 0)]  # 23^0=1 divides but not tight

    fam_good = _small_family(good)
    fam_bad = _small_family(bad, name="BadVal")

    # Good should certify without error
    cf = certify(fam_good)
    assert cf.checks_passed == 1

    # Bad should be refused
    with pytest.raises(CertificationError):
        certify(fam_bad)


# ---------------------------------------------------------------------------
# (c) Byte-stability: emit twice, identical text
# ---------------------------------------------------------------------------

def test_byte_stable_emit():
    """Emitting the same family twice produces byte-identical Lean text."""
    facts_fn = lambda pt: [
        ValuationFact("v23_621", 621,      23, 1),
        ValuationFact("v23_64",  64,       23, 0),
        ValuationFact("v23_hub", 23 ** 11, 23, 11),
    ]
    fam = _small_family(facts_fn)
    res1 = _do_emit(fam)
    res2 = _do_emit(fam)
    assert res1.files == res2.files, (
        "emit is not byte-stable: two runs produced different output"
    )


def test_byte_stable_input_hash():
    """The input hash is identical across two certify+emit runs."""
    facts_fn = lambda pt: [ValuationFact("v23_621", 621, 23, 1)]
    fam = _small_family(facts_fn)
    res1 = _do_emit(fam)
    res2 = _do_emit(fam)
    assert res1.input_hash == res2.input_hash


# ---------------------------------------------------------------------------
# Emitter configuration
# ---------------------------------------------------------------------------

def test_emitter_kind():
    """PadicValuationEmitter.kind is 'valuation'."""
    em = PadicValuationEmitter()
    assert em.kind == "valuation"


def test_valuation_family_kind():
    """valuation_family produces an InequalityFamily with kind='valuation'."""
    fam = _small_family(lambda pt: [ValuationFact("v23_621", 621, 23, 1)])
    assert fam.kind == "valuation"


def test_valuation_family_prime_constant():
    """valuation_family records the prime in its constants dict."""
    fam = valuation_family(
        name="PrimeTest",
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "pt",
        facts=lambda pt: [ValuationFact("f", 64, 23, 0)],
        prime=23,
    )
    assert "prime" in fam.constants
    assert fam.constants["prime"] == 23
