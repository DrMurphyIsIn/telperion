"""Helpers shared by test_emit_nat_root_bracket_table.py (engine) and test_emit_nat_root_bracket_table_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_nat_root_bracket_table import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_nat_root_bracket_table import (  # noqa: E402
    NatRootBracketTableEmitter, nat_root_bracket_table_family,
)


def _emit_text(specs, names, imports=("NatRootBracket",)):
    fam = nat_root_bracket_table_family(
        "NatRootBracketTableTest", GridSpec([("case", list(range(len(specs))))]),
        lambda pt: names[pt["case"]], spec=lambda pt: dict(specs[pt["case"]]))
    report = emit(certify(fam), LeanProfile(namespace=("NatRootBracketTableTest",), imports=imports),
                  [NatRootBracketTableEmitter()], ValidationReport(checks=(("ok", True),)))
    return next(iter(report.files.values()))
