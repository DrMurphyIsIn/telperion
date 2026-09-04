from __future__ import annotations

import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # for the shared lean_env guard

from telperion import InequalityFamily, GridSpec  # noqa: E402
from telperion.evolve.config import EvolveConfig  # noqa: E402
from telperion.evolve.kernel import kernel_check_family  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

u = sp.Symbol("u", nonnegative=True)
_LEAN = EvolveConfig.default().lean_project
pytestmark = pytest.mark.skipif(
    not lean_env_ready(_LEAN),
    reason="no lake / no prebuilt Mathlib (guard skips instead of triggering a rebuild)",
)


def test_lifted_toy_is_kernel_green():
    fam = InequalityFamily(
        name="ToyLift", symbols=(u,), grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: f"toy_lift_a{pt['a']}",
        target=lambda pt: (u**2 - u + pt["a"]) / (u + 1), auto_lift=1,
    )
    green, art = kernel_check_family(fam, _LEAN)
    assert green is True
    assert "theorem" in art["lean"]
