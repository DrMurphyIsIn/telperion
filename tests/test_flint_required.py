"""Make missing python-flint / libflint a hard failure where CI says it must be present.

The rigorous winding tests (test_arb_winding.py) import python-flint with importorskip, and the DH ctypes
comparison is skipped when arb_dh cannot find libflint. On a CI runner, either condition would silently
disable the soundness regression tests added after the 2026-10-14 winding audit (#740). With
TELPERION_REQUIRE_FLINT=1 in the environment, this test fails instead of letting them skip. Locally,
without the variable, it is skipped.
conjecture1_proved = False.
"""
import os

import pytest

REQUIRED = os.environ.get("TELPERION_REQUIRE_FLINT") == "1"


@pytest.mark.skipif(not REQUIRED, reason="TELPERION_REQUIRE_FLINT not set")
def test_python_flint_importable():
    import flint  # noqa: F401  (ImportError here is the failure we want)


@pytest.mark.skipif(not REQUIRED, reason="TELPERION_REQUIRE_FLINT not set")
def test_dh_ctypes_shim_found():
    from telperion import arb_dh

    assert arb_dh.DH_AVAILABLE, (
        "arb_dh could not locate libflint, so test_dh_series_matches_ctypes_dh_eval and the "
        "ctypes big-rational tests would be skipped; see arb_dh._find_libflint")
