"""disjoint_discs emitter — MIRRORMERE E4b isolation INSTANCES (OfflineDiscs shape).

Explicit strip points + an explicit rational radius, with the per-pair STRICT separation
`(2r)^2 < dist^2` and the strict strip margins as the load-bearing, norm_num-decided facts.
The negative controls are an inflated radius (overlapping discs), a boundary-reaching radius, a
point off the open strip, a duplicate point and a non-positive radius — all REFUSED at certify.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    DisjointDiscsEmitter, ValidationReport, certify, emit,
)
from telperion.emit_disjoint_discs import (  # noqa: E402
    disjoint_discs_certificate, disjoint_discs_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_PTS = [("1/2", "7067/500"), ("1/2", "10511/500"), ("2/5", "12505/500"), ("3/5", "12505/500")]


def _spec(points, r):
    return lambda pt: {"points": points, "r": r}


def _refused(points, r):
    fam = disjoint_discs_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                spec=_spec(points, r))
    with pytest.raises(Exception):
        certify(fam)


def test_positive_cert_records_the_exact_separation_and_margin():
    cert = disjoint_discs_certificate(_PTS, "1/50")
    # the off-line pair (2/5, 3/5) at a common height is the tight one: dist = 1/5
    assert cert.min_sep_sq == sp.Rational(1, 25)
    assert cert.min_margin == sp.Rational(2, 5)
    assert (2 * cert.r) ** 2 < cert.min_sep_sq


def test_refuses_overlapping_discs():
    # NEGATIVE CONTROL: r = 1/10 on points 1/5 apart gives (2r)^2 = 1/25 = dist^2 — NOT strict.
    _refused(_PTS, "1/10")


def test_refuses_radius_reaching_the_strip_boundary():
    # NEGATIVE CONTROL: margin at re = 2/5 is 2/5; r = 1/2 pushes the disc out of the open strip.
    _refused([("2/5", "1"), ("2/5", "100")], "1/2")


def test_refuses_point_on_the_strip_boundary():
    # NEGATIVE CONTROL: re = 1 is ON the boundary — no disc about it lies in the OPEN strip.
    _refused([("1", "5"), ("1/2", "9")], "1/100")


def test_refuses_duplicate_points_and_nonpositive_radius():
    _refused([("1/2", "3"), ("1/2", "3")], "1/100")
    _refused([("1/2", "3"), ("1/2", "9")], "0")


def test_emit_is_lint_clean_and_deterministic():
    fam = disjoint_discs_family("DD", GridSpec([("_", [0])]), lambda pt: "isolation_bank",
                                spec=_spec(_PTS, "1/50"))
    report = emit(certify(fam),
                  LeanProfile(namespace=("DD",), imports=("Mathlib", "OfflineDiscs")),
                  [DisjointDiscsEmitter()],
                  ValidationReport(checks=(("disjoint_discs", True),)))
    text = next(iter(report.files.values()))
    # the two load-bearing routes, plus the statement gate against the registry-node shape
    assert "Metric.closedBall_disjoint_closedBall" in text
    assert "Real.lt_sqrt" in text
    assert "Quasicrystal.abs_re_sub_le_dist" in text
    assert "example : ∃ r : ℝ, 0 < r ∧" in text
    # 6 pairs + 4 strip lemmas + 1 assembly
    assert text.count("theorem isolation_bank") >= 11
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry_with_an_adapter():
    from telperion.emitter_sensitivity import REGISTRY
    import telperion.negctrl_adapters  # noqa: F401  (registers the adapters)
    from telperion.negative_control_harness import registered_adapters
    assert "DisjointDiscsEmitter" in REGISTRY
    assert "DisjointDiscsEmitter" in registered_adapters()


def test_kind_is_wired_into_the_dispatch_tables():
    from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS, emitter_for
    assert "disjoint_discs" in _SPECIAL_KINDS
    assert len(_SPECIAL_DISPATCH["disjoint_discs"]) == 3
    assert emitter_for("disjoint_discs").kind == "disjoint_discs"
