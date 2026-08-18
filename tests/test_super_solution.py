"""Super-solution tester (#4): exact domination, the branching caveat, no floats."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.super_solution import super_solution_check  # noqa: E402
from telperion.verdict import FloatAtDecisionPoint, Verdict  # noqa: E402

PTS = [{"n": 1}, {"n": 2}, {"n": 3}]


def test_valid_super_solution():
    # P(n) = n, TP(n) = n - 1: P >= TP everywhere, non-branching
    v = super_solution_check(lambda pt: pt["n"], lambda pt: pt["n"] - 1, PTS)
    assert v.verdict is Verdict.VALIDATED


def test_domination_failure_is_located():
    # TP exceeds P at n=3
    def tp(pt):
        return pt["n"] + (1 if pt["n"] == 3 else -1)
    v = super_solution_check(lambda pt: pt["n"], tp, PTS)
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "n': 3" in v.obstruction or "{'n': 3}" in v.obstruction


def test_branching_downgrades_to_caveat():
    # pointwise passes, but branching=True => no silent global VALIDATED
    v = super_solution_check(lambda pt: pt["n"], lambda pt: pt["n"] - 1, PTS,
                             branching=True)
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "branching" in v.obstruction


def test_empty_is_null():
    assert super_solution_check(lambda pt: 1, lambda pt: 0, []).verdict is Verdict.NULL


def test_float_at_decision_refused():
    with pytest.raises(FloatAtDecisionPoint):
        super_solution_check(lambda pt: 1.5, lambda pt: Fraction(1), PTS)
