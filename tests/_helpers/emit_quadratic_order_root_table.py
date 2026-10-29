"""Helpers shared by test_emit_quadratic_order_root_table.py (engine) and test_emit_quadratic_order_root_table_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_quadratic_order_root_table import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_quadratic_order_root_table import (  # noqa: E402
    QuadraticOrderRootTableEmitter, quadratic_order_root_table_family,
)


def _emit_text(specs, names=None):
    names = names or [f"q{i}" for i in range(len(specs))]
    fam = quadratic_order_root_table_family(
        "QuadraticOrderRootTableTest", GridSpec([("i", list(range(len(specs))))]),
        lambda pt: names[pt["i"]], spec=lambda pt: dict(specs[pt["i"]]))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("QuadraticOrderRootTableTest",),
                    imports=("Mathlib", "QuadraticOrderRoot")),
        [QuadraticOrderRootTableEmitter()],
        ValidationReport(checks=(("quadratic_order_root_table", True),)),
    )
    return next(iter(report.files.values()))
