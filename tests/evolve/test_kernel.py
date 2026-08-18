from __future__ import annotations

import os
import shutil
import pytest
import sympy as sp

from telperion import InequalityFamily, GridSpec
from telperion.evolve.config import EvolveConfig
from telperion.evolve.kernel import kernel_check_family

u = sp.Symbol("u", nonnegative=True)
_LEAN = EvolveConfig.default().lean_project
pytestmark = pytest.mark.skipif(
    not shutil.which("lake") or not os.path.isdir(os.path.join(_LEAN, ".lake")),
    reason="no lake / no prebuilt Mathlib",
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
