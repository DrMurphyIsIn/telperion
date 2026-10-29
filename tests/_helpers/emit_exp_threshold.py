"""Helpers shared by test_emit_exp_threshold.py (engine) and test_emit_exp_threshold_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_exp_threshold import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import (  # noqa: E402
    ExpThresholdEmitter, GridSpec, LeanProfile, ValidationReport, certify, emit,
    exp_threshold_family,
)


def _fam(spec, name="t_inst", fam_name="ExpThresholdTest"):
    return exp_threshold_family(fam_name, GridSpec([("i", [0])]), lambda pt: name,
                                spec=lambda pt: dict(spec))


def _emit_text(spec, name="t_inst"):
    report = emit(
        certify(_fam(spec, name)),
        LeanProfile(namespace=("ExpThresholdTest",), imports=("Mathlib",)),
        [ExpThresholdEmitter()],
        ValidationReport(checks=(("exp_threshold", True),)),
    )
    return next(iter(report.files.values()))
