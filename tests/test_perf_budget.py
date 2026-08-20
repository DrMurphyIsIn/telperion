"""Performance-regression gate: certify+emit must stay sub-quadratic in the grid
size.  A robust ratio check (dimensionless), not an absolute-time budget."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import sympy as sp  # noqa: E402

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
)
from telperion.bench import scaling_probe  # noqa: E402

_u = sp.Symbol("u", nonnegative=True)
_PROFILE = LeanProfile(namespace=("Perf",))
_VAL = ValidationReport(checks=(("s", True),))


def _pipeline(n: int) -> None:
    fam = InequalityFamily(
        name="Perf", symbols=(_u,), grid=GridSpec([("a", list(range(1, n + 1)))]),
        lean_name=lambda pt: f"perf_{pt['a']}",
        target=lambda pt: (pt["a"] * _u + pt["a"]) / (_u + 1),
    )
    emit(certify(fam), _PROFILE, [DirectPolyaEmitter()], _VAL)


def test_certify_emit_scales_subquadratically():
    # 4x size step widens the linear/quadratic gap for CI robustness: linear
    # work scores growth ~1.0, quadratic ~4.0.  The 3.0 ceiling catches a genuine
    # O(n^2) render regression by a wide margin (a true quadratic scores ~4.0)
    # while tolerating loaded-runner wall-clock noise: this empirical probe was
    # observed flaking at growth ~2.5-2.62 on contended CI at the old 2.5 ceiling
    # (a measurement artifact, not a regression), so the bound is set above that
    # band. `repeat=3` medians out more of the per-run jitter.
    res = scaling_probe(_pipeline, 80, 320, repeat=3, max_growth=3.0)
    assert res.ok, f"super-linear certify+emit scaling regression: {res.detail}"
