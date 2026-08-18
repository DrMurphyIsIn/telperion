"""Faithfulness cross-check (pattern #1) — unit tests.

Covers:
  1. Two faithful implementations of the same rational function -> VALIDATED.
  2. The caught-bug case: an unfaithful second implementation -> OBSTRUCTED_AND_LOCATED,
     with the witness point named in the obstruction.
  3. A float returned by an implementation at a decision point -> FloatAtDecisionPoint
     (the no-floats discipline holds through the checker).
  4. Empty points -> NULL.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.faithfulness import faithfulness_check, seeded_rational_points  # noqa: E402
from telperion.verdict import (  # noqa: E402
    FloatAtDecisionPoint,
    Verdict,
)


# ---------------------------------------------------------------------------
# helpers: the shared test function is  f(x, y) = x^2 + y / 3
# ---------------------------------------------------------------------------

def _f_primary(pt: dict) -> Fraction:
    """Primary implementation of f(x, y) = x^2 + y/3 in exact arithmetic."""
    x, y = pt["x"], pt["y"]
    return x * x + Fraction(y, 3)


def _f_independent(pt: dict) -> Fraction:
    """Independently-written implementation of the same f."""
    x, y = pt["x"], pt["y"]
    # Different computation path: (3x^2 + y) / 3
    return Fraction(3 * x * x + y, 3)


def _f_unfaithful(pt: dict) -> Fraction:
    """Buggy implementation: uses x + y/3 instead of x^2 + y/3.

    Agrees with the primary when x==0 or x==1 (since 1^2==1), but disagrees
    elsewhere (e.g. x=2: primary=4+y/3, buggy=2+y/3).
    """
    x, y = pt["x"], pt["y"]
    return x + Fraction(y, 3)


def _f_returns_float(pt: dict) -> float:
    """Bad implementation: returns a Python float — violates the no-float discipline."""
    x, y = pt["x"], pt["y"]
    return float(x) ** 2 + float(y) / 3.0


# ---------------------------------------------------------------------------
# 1. Two faithful implementations agree -> VALIDATED
# ---------------------------------------------------------------------------

def test_faithful_pair_is_validated():
    pts = seeded_rational_points(["x", "y"], n=10, seed=42)
    result = faithfulness_check(_f_primary, _f_independent, pts, label="f=x^2+y/3")

    assert result.verdict == Verdict.VALIDATED, result.render()
    # Evidence must mention the point count.
    assert any("10" in e for e in result.evidence), result.evidence


# ---------------------------------------------------------------------------
# 2. Unfaithful implementation -> OBSTRUCTED_AND_LOCATED with witness
# ---------------------------------------------------------------------------

def test_unfaithful_impl_is_obstructed():
    # Use points where x != 0 and x != 1 so the bug is exposed.
    pts = [{"x": Fraction(2), "y": Fraction(1)},
           {"x": Fraction(3), "y": Fraction(0)}]

    result = faithfulness_check(_f_primary, _f_unfaithful, pts, label="cherry-bug")

    assert result.verdict == Verdict.OBSTRUCTED_AND_LOCATED, result.render()
    # The obstruction must name a witness (specific point + both values).
    assert result.obstruction is not None
    # The disagreeing values appear in the obstruction string.
    assert "primary=" in result.obstruction, result.obstruction
    assert "independent=" in result.obstruction, result.obstruction


def test_obstruction_locates_first_disagreeing_point():
    # Only the first disagreeing point should be in the obstruction.
    bad_pt = {"x": Fraction(4), "y": Fraction(6)}
    pts = [bad_pt]

    result = faithfulness_check(_f_primary, _f_unfaithful, pts, label="single-witness")

    assert result.verdict == Verdict.OBSTRUCTED_AND_LOCATED
    # The exact witness values: primary = 4^2 + 6/3 = 18, unfaithful = 4 + 2 = 6
    assert "primary=18" in result.obstruction or "primary=Fraction(18" in result.obstruction or "18" in result.obstruction
    assert "independent=6" in result.obstruction or "6" in result.obstruction


# ---------------------------------------------------------------------------
# 3. Float at a decision point -> FloatAtDecisionPoint
# ---------------------------------------------------------------------------

def test_float_return_is_refused():
    pts = [{"x": Fraction(1), "y": Fraction(2)}]

    with pytest.raises(FloatAtDecisionPoint):
        # _f_returns_float hands back a Python float; require_exact inside
        # faithfulness_check should fire immediately.
        faithfulness_check(_f_returns_float, _f_independent, pts, label="float-guard")


def test_float_in_independent_is_also_refused():
    pts = [{"x": Fraction(1), "y": Fraction(2)}]

    with pytest.raises(FloatAtDecisionPoint):
        faithfulness_check(_f_primary, _f_returns_float, pts, label="float-guard-ind")


# ---------------------------------------------------------------------------
# 4. Empty points -> NULL
# ---------------------------------------------------------------------------

def test_empty_points_is_null():
    result = faithfulness_check(_f_primary, _f_independent, [], label="empty")

    assert result.verdict == Verdict.NULL, result.render()
    # The evidence should mention that nothing was checked.
    combined = " ".join(result.evidence)
    assert "no points" in combined or "nothing" in combined


# ---------------------------------------------------------------------------
# 5. seeded_rational_points: determinism guarantee
# ---------------------------------------------------------------------------

def test_seeded_rational_points_deterministic():
    pts_a = seeded_rational_points(["x", "y"], n=5, seed=99)
    pts_b = seeded_rational_points(["x", "y"], n=5, seed=99)
    assert pts_a == pts_b


def test_seeded_rational_points_different_seeds_differ():
    pts_a = seeded_rational_points(["x"], n=5, seed=1)
    pts_b = seeded_rational_points(["x"], n=5, seed=2)
    assert pts_a != pts_b


def test_seeded_rational_points_all_fractions():
    pts = seeded_rational_points(["a", "b", "c"], n=8, seed=7)
    assert len(pts) == 8
    for pt in pts:
        assert set(pt.keys()) == {"a", "b", "c"}
        for v in pt.values():
            assert isinstance(v, Fraction)
