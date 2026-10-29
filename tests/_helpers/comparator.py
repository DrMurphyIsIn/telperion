"""Helpers shared by test_comparator.py (engine) and test_comparator_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.comparator import ...` resolves, as `from missions_fixtures import ...` does.
"""
from __future__ import annotations


from telperion.provenance import EmitResult


def _result(files):
    return EmitResult(
        family_name="Bernoulli", input_hash="deadbeef" * 8,
        files=files, n_theorems=sum(f.count("theorem ") for f in files.values()),
        n_checks=2,
    )
