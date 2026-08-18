"""Circularity / strength check (#6): a proper reduction has a separating witness;
a lemma that implies the goal on the whole probe is suspected circular."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.circularity import circularity_check  # noqa: E402
from telperion.verdict import FloatAtDecisionPoint, Verdict  # noqa: E402

PTS = [{"n": 1}, {"n": 2}, {"n": 3}]


def test_non_circular_has_separating_witness():
    # lemma holds for n>=2, goal for n>=3 -> at n=2 lemma holds but goal fails
    v = circularity_check(lambda pt: pt["n"] - 2, lambda pt: pt["n"] - 3, PTS)
    assert v.verdict is Verdict.VALIDATED
    assert "separating witness" in v.evidence[0]


def test_identical_lemma_is_restatement():
    v = circularity_check(lambda pt: pt["n"] - 2, lambda pt: pt["n"] - 2, PTS)
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "restated" in v.obstruction or "==" in v.obstruction


def test_lemma_implies_goal_is_suspected_circular():
    # lemma holds only for n>=3, goal for n>=2: wherever lemma holds, goal holds,
    # and they are not identical -> no separating witness -> suspected circular
    v = circularity_check(lambda pt: pt["n"] - 3, lambda pt: pt["n"] - 2, PTS)
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "no separating witness" in v.obstruction


def test_empty_is_null():
    v = circularity_check(lambda pt: 1, lambda pt: 1, [])
    assert v.verdict is Verdict.NULL


def test_float_at_decision_refused():
    with pytest.raises(FloatAtDecisionPoint):
        circularity_check(lambda pt: 0.5, lambda pt: Fraction(1), PTS)
