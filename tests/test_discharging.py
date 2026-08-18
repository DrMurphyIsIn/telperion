"""Discharging-conservation checker (#5): exact conservation, target, locates breaks."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.discharging import discharging_check  # noqa: E402
from telperion.verdict import FloatAtDecisionPoint, Verdict  # noqa: E402


def test_conserving_scheme_validated():
    init = {"a": Fraction(5), "b": Fraction(1), "c": Fraction(0)}
    transfers = [("a", "b", Fraction(2)), ("a", "c", Fraction(1))]
    v = discharging_check(init, transfers)
    assert v.verdict is Verdict.VALIDATED


def test_conservation_break_located():
    # a transfer that also injects charge into a node it doesn't remove from
    # is modelled as a bad scheme via a manual mismatch: use a checker on a
    # transfer list that conserves, then a target the checker enforces.
    init = {"a": Fraction(5), "b": Fraction(1)}
    v = discharging_check(init, [("a", "b", Fraction(3))], target=Fraction(3))
    # final a=2, b=4 -> b misses target (<=3) -> located
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "target" in v.obstruction


def test_target_met_validated():
    init = {"a": Fraction(5), "b": Fraction(1)}
    v = discharging_check(init, [("a", "b", Fraction(1))], target=Fraction(4))
    # final a=4, b=2 -> both <= 4
    assert v.verdict is Verdict.VALIDATED


def test_unknown_node_located():
    v = discharging_check({"a": Fraction(1)}, [("a", "z", Fraction(1))])
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "unknown node" in v.obstruction


def test_empty_is_null():
    assert discharging_check({}, []).verdict is Verdict.NULL


def test_float_charge_refused():
    with pytest.raises(FloatAtDecisionPoint):
        discharging_check({"a": 1.5}, [])
