"""Sampled->proof upgradability (#7): finite complete cover is mechanical;
an unbounded axis is a conceptual seam; a finite gap is a coverage gap."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import sympy as sp  # noqa: E402

from telperion import GridSpec, InequalityFamily  # noqa: E402
from telperion.upgradability import (  # noqa: E402
    UNBOUNDED,
    upgradability_check,
    upgradability_of_family,
)
from telperion.verdict import Verdict  # noqa: E402


def test_complete_finite_cover_is_mechanical():
    claimed = [{"a": 1}, {"a": 2}, {"a": 3}]
    v = upgradability_check(claimed, claimed, label="finite claim")
    assert v.verdict is Verdict.VALIDATED
    assert "COMPLETE finite cover" in v.evidence[0]


def test_finite_gap_is_located():
    claimed = [{"a": 1}, {"a": 2}, {"a": 3}]
    sampled = [{"a": 1}, {"a": 2}]
    v = upgradability_check(sampled, claimed, label="finite claim")
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "coverage GAP" in v.obstruction


def test_unbounded_axis_is_conceptual_seam():
    sampled = [{"n": k} for k in range(1, 6)]
    v = upgradability_check(sampled, UNBOUNDED, unbounded_axes=("n",),
                            label="for all n")
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "CONCEPTUAL SEAM" in v.obstruction


def test_empty_claim_is_null():
    v = upgradability_check([], [], label="nothing")
    assert v.verdict is Verdict.NULL


def _fam():
    u = sp.Symbol("u", nonnegative=True)
    return InequalityFamily(
        name="F", symbols=(u,), grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"f{pt['a']}", target=lambda pt: u + pt["a"],
    )


def test_family_finite_grid_is_mechanical():
    assert upgradability_of_family(_fam()).verdict is Verdict.VALIDATED


def test_family_unbounded_axis_is_seam():
    v = upgradability_of_family(_fam(), unbounded_axes=("a",))
    assert v.verdict is Verdict.OBSTRUCTED_AND_LOCATED
    assert "CONCEPTUAL SEAM" in v.obstruction
