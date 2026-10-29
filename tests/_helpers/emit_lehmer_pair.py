"""Helpers shared by test_emit_lehmer_pair.py (engine) and test_emit_lehmer_pair_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_lehmer_pair import ...` resolves, as `from missions_fixtures import ...` does.
"""
import pytest


def _need_platt():
    """Skip (not error) where libflint lacks the Platt machinery: `flint` can
    import while `acb_dirichlet_platt_*` is absent from the bundled library."""
    from telperion.arb_platt import PLATT_AVAILABLE
    if not PLATT_AVAILABLE:
        pytest.skip("libflint with Platt machinery not found")
