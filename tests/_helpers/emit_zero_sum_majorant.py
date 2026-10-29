"""Helpers shared by test_emit_zero_sum_majorant.py (engine) and test_emit_zero_sum_majorant_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_zero_sum_majorant import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, ZeroSumMajorantEmitter, certify, emit,
    zero_sum_majorant_family,
)


def _fam(spec, name="t_inst", fam_name="ZeroSumMajorantTest"):
    return zero_sum_majorant_family(fam_name, GridSpec([("i", [0])]), lambda pt: name,
                                    spec=lambda pt: dict(spec))


def _emit_text(spec, name="t_inst"):
    report = emit(
        certify(_fam(spec, name)),
        LeanProfile(namespace=("ZeroSumMajorantTest",), imports=("RvMBridgeXi",)),
        [ZeroSumMajorantEmitter()],
        ValidationReport(checks=(("zero_sum_majorant", True),)),
    )
    return next(iter(report.files.values()))
