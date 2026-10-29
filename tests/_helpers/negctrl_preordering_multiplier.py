"""Helpers shared by test_negctrl_preordering_multiplier.py (engine) and test_negctrl_preordering_multiplier_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.negctrl_preordering_multiplier import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("PreorderingMultiplierEmitter")
    assert ad is not None, "no adapter registered for PreorderingMultiplierEmitter"
    return ad
