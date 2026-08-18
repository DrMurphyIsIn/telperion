"""Tests for src/telperion/limit_probe.py -- anti-size-bounded-trap (pattern #2).

Five scenarios that exercise every branch of limit_probe:

1. Growing margin  -> VALIDATED
2. The trap        -> OBSTRUCTED_AND_LOCATED at the first breaking size
3. Shrinking but   -> OBSTRUCTED_AND_LOCATED (degradation toward limit)
   positive margin
4. Empty sizes     -> NULL
5. Float margin    -> FloatAtDecisionPoint raised immediately
"""
from __future__ import annotations

import sys
import os

# Resolve the repo root relative to this test file so the import works whether
# pytest is invoked from the repo root or the tests/ directory.
_HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = os.path.join(os.path.dirname(_HERE), "src")
if _SRC not in sys.path:
    sys.path.insert(0, _SRC)

from fractions import Fraction

import pytest

from telperion.limit_probe import limit_probe
from telperion.verdict import FloatAtDecisionPoint, Verdict


# ---------------------------------------------------------------------------
# Test 1: growing (non-degrading) margin -> VALIDATED
# ---------------------------------------------------------------------------

def test_validated_growing_margin():
    """claim(n) = (n-1)/n grows monotonically toward 1 -- every size passes,
    margin is strictly increasing, so the probe returns VALIDATED."""

    def claim(n):
        return Fraction(n - 1, n)  # 0, 1/2, 2/3, 3/4, ... -> 1

    sizes = [2, 5, 10, 20, 50, 100]
    result = limit_probe(claim, sizes, label="growing margin")

    assert result.verdict == Verdict.VALIDATED, result.render()
    # Evidence must be present (VALIDATED requires at least one evidence item).
    assert result.evidence


# ---------------------------------------------------------------------------
# Test 2: size-bounded trap -- holds for small n, fails for large n
# ---------------------------------------------------------------------------

def test_obstructed_size_bounded_trap():
    """claim(n) = (19 - n) / 100: positive for n < 19, zero at n=19, negative
    after.  The trap: small sizes look fine, but n=19 breaks it.

    The probe must:
      * return OBSTRUCTED_AND_LOCATED
      * locate the obstruction at n=19 (the SMALLEST breaking size)
    """

    def claim(n):
        return Fraction(19 - n, 100)

    # Sizes that cross the boundary: small ones pass, 19 and 20 fail.
    sizes = [5, 10, 15, 19, 20, 50]
    result = limit_probe(claim, sizes, label="trap: holds until n=19")

    assert result.verdict == Verdict.OBSTRUCTED_AND_LOCATED, result.render()
    assert result.obstruction is not None
    # The located breaking size must be identified in the obstruction string.
    assert "n=19" in result.obstruction, (
        f"Expected obstruction to name n=19, got: {result.obstruction!r}"
    )


# ---------------------------------------------------------------------------
# Test 3: shrinking (but still positive) margin -> OBSTRUCTED_AND_LOCATED
# ---------------------------------------------------------------------------

def test_obstructed_shrinking_margin():
    """claim(n) = 1/n: always positive but strictly decreasing toward 0.

    Design decision: a shrinking-but-positive margin is OBSTRUCTED_AND_LOCATED
    with a 'margin shrinking toward limit' obstruction.  Rationale: silence on
    a shrinking margin is exactly how the size-bounded trap sprang in the
    Brualdi-Goldwasser campaign.  This is the most important of the four
    branches: it catches 'true so far but heading to the boundary'.
    """

    def claim(n):
        return Fraction(1, n)

    sizes = [1, 2, 5, 10, 50, 100]
    result = limit_probe(claim, sizes, label="shrinking margin 1/n")

    assert result.verdict == Verdict.OBSTRUCTED_AND_LOCATED, result.render()
    assert result.obstruction is not None
    # Must mention the shrinking trend.
    assert "shrink" in result.obstruction.lower(), (
        f"Expected 'shrink' in obstruction, got: {result.obstruction!r}"
    )


# ---------------------------------------------------------------------------
# Test 4: empty sizes -> NULL
# ---------------------------------------------------------------------------

def test_null_empty_sizes():
    """No sizes to probe -> NULL (cannot assess the limit)."""

    def claim(n):
        return Fraction(1)  # would always pass, irrelevant

    result = limit_probe(claim, [], label="empty sizes")

    assert result.verdict == Verdict.NULL, result.render()


# ---------------------------------------------------------------------------
# Test 5: float margin at a decision point -> FloatAtDecisionPoint raised
# ---------------------------------------------------------------------------

def test_float_margin_refused():
    """A claim that returns a Python float is refused at the decision point
    with FloatAtDecisionPoint -- the same discipline as require_exact /
    decide in verdict.py."""

    def claim(n):
        return 0.5  # Python float: forbidden at a decision point

    with pytest.raises(FloatAtDecisionPoint):
        limit_probe(claim, [5, 10, 20], label="float claim")


# ---------------------------------------------------------------------------
# Additional: single-size probe with growing margin -> VALIDATED
# ---------------------------------------------------------------------------

def test_single_size_validated():
    """A single probed size that passes -> VALIDATED (no delta, no degradation
    possible).  Verifies the single-point edge case does not crash."""

    def claim(n):
        return Fraction(3, 4)

    result = limit_probe(claim, [10], label="single size")

    assert result.verdict == Verdict.VALIDATED, result.render()


# ---------------------------------------------------------------------------
# Additional: exact zero margin is a failure (boundary is a violation)
# ---------------------------------------------------------------------------

def test_zero_margin_is_violation():
    """claim(n) = 0 for all n: margin is exactly zero (not positive) ->
    OBSTRUCTED_AND_LOCATED at the very first size."""

    def claim(n):
        return Fraction(0)

    sizes = [1, 5, 10]
    result = limit_probe(claim, sizes, label="zero margin")

    assert result.verdict == Verdict.OBSTRUCTED_AND_LOCATED, result.render()
    # First size is n=1.
    assert "n=1" in result.obstruction, result.obstruction
