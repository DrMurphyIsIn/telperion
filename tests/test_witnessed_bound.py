"""Witnessed-bound guard: the flat-arm red herring becomes a located verdict."""
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.verdict import FloatAtDecisionPoint, Verdict  # noqa: E402
from telperion.witnessed_bound import witnessed_bound_check  # noqa: E402


def test_faithful_bound_validated():
    # claimed == witnessed everywhere
    pts = [{"mu": F(3, 23)}, {"mu": F(1, 3)}, {"mu": F(1, 7)}]
    real = {F(3, 23): F(1), F(1, 3): F(486, 529), F(1, 7): F(2, 5)}
    v = witnessed_bound_check(lambda p: real[p["mu"]], lambda p: real[p["mu"]], pts)
    assert v.verdict is Verdict.VALIDATED


def test_flat_arm_phantom_located():
    # the actual red herring: flat env = 0.919 at mu=0.797 where the real F-max
    # (F_ns) is only ~0.17. The guard must locate the phantom.
    pts = [{"mu": F(3, 23)}, {"mu": F(797, 1000)}]
    claimed = {F(3, 23): F(1), F(797, 1000): F(919, 1000)}      # flat-arm bound
    witnessed = {F(3, 23): F(1), F(797, 1000): F(17, 100)}      # real F_ns there
    v = witnessed_bound_check(lambda p: claimed[p["mu"]], lambda p: witnessed[p["mu"]], pts)
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "PHANTOM" in v.obstruction and "797" in v.obstruction


def test_empty_is_null():
    assert witnessed_bound_check(lambda p: 1, lambda p: 1, []).verdict is Verdict.NULL


def test_float_at_decision_refused():
    with pytest.raises(FloatAtDecisionPoint):
        witnessed_bound_check(lambda p: 0.919, lambda p: F(17, 100), [{"mu": F(1, 2)}])
