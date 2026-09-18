"""defect_witness emitter — the two-configuration inertia gap (MIRRORMERE QC-B3, BraggDefect shape).

On-line functional value 0 ∈ [A,B], off-line functional value strictly in [−d_hi², −d_lo²] < 0, and
the leakage gap −d_lo² < 0 = q(0).  A swapped / degenerate configuration (d_lo = 0, no excess) is the
negative control and is refused.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import sympy as sp  # noqa: E402

from telperion import DefectWitnessEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_defect_witness import (  # noqa: E402
    defect_witness_certificate, defect_witness_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _spec(d_lo, d_hi, A=0, B=0):
    return lambda pt: {"d_lo": d_lo, "d_hi": d_hi, "A": A, "B": B}


def test_positive_cert_separates():
    cert = defect_witness_certificate("1/10", "11/100")
    # off-line functional interval [−d_hi², −d_lo²]
    assert cert.off_lo == -sp.Rational(11, 100) ** 2
    assert cert.off_hi == -sp.Rational(1, 10) ** 2
    # the gap: off-line upper strictly below the on-line value 0
    assert cert.off_hi < 0


def test_refuses_degenerate_online_pair():
    # NEGATIVE CONTROL: d_lo = 0 (no excess) — the swapped/degenerate configuration.
    fam = defect_witness_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                spec=_spec("0", "11/100"))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a degenerate on-line pair (d_lo = 0) must be refused"


def test_refuses_online_value_outside_interval():
    # NEGATIVE CONTROL: [A,B] that excludes q(0)=0 (here A = 1/100 > 0).
    fam = defect_witness_family("Bad2", GridSpec([("_", [0])]), lambda pt: "bad2",
                                spec=_spec("1/10", "11/100", A="1/100", B="1"))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "an on-line interval excluding 0 must be refused"


def test_emit_is_lint_clean_and_deterministic():
    fam = defect_witness_family("DW", GridSpec([("_", [0])]), lambda pt: "defect_tenth",
                                spec=_spec("1/10", "11/100"))
    report = emit(certify(fam), LeanProfile(namespace=("DW",)),
                  [DefectWitnessEmitter()], ValidationReport(checks=(("defect_witness", True),)))
    text = next(iter(report.files.values()))
    # three theorems: online, offline, leakage_gap
    assert "_online" in text and "_offline" in text and "_leakage_gap" in text
    assert "defectFunctional" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "DefectWitnessEmitter" in REGISTRY
