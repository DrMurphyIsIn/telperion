"""Performance-regression gate — keep certify/emit sub-quadratic.

The campaign's two worst stalls (srepr default ordering evalf-ing every Add
node; DirectPolyaEmitter re-expanding at render) were O(n^2)/O(n*cost) traps
found only by py-spy on a hung run.  This module institutionalizes catching them:
a scaling probe times an operation at size n and 2n and checks the growth is
sub-quadratic, so the next such trap fails a test instead of hanging a freeze.

DELIBERATELY NOT a ProbeVerdict.  Wall-clock time is an EMPIRICAL measurement,
not an exact-rational decision — routing it through `verdict.decide` (which
refuses floats) would be a category error.  The honest-verdict discipline is for
mathematical claims; this is a runtime tripwire.  A scaling check is compared as
a RATIO (dimensionless), which is robust to machine speed in a way an absolute
time budget is not.
"""
from __future__ import annotations

import time
from dataclasses import dataclass


@dataclass(frozen=True)
class ScalingResult:
    n1: int
    n2: int
    t1: float
    t2: float
    ratio: float          # t2 / t1
    size_ratio: float     # n2 / n1
    growth: float         # ratio / size_ratio: ~1 linear, ~size_ratio quadratic
    ok: bool
    detail: str


def time_op(op, *, repeat: int = 3) -> float:
    """Minimum wall-clock over `repeat` runs (min rejects scheduling noise)."""
    best = float("inf")
    for _ in range(repeat):
        t0 = time.perf_counter()
        op()
        best = min(best, time.perf_counter() - t0)
    return best


def scaling_probe(run_at, n1: int, n2: int, *, repeat: int = 3,
                  max_growth: float = 1.8, min_time: float = 5e-3) -> ScalingResult:
    """Time `run_at(n)` at n1 and n2 (n2 > n1) and check sub-quadratic growth.

    run_at(n): a callable that performs the sized operation for size n.
    growth = (t2/t1) / (n2/n1).  Linear work has growth ~1; quadratic has
    growth ~ n2/n1.  `max_growth` (default 1.8) is the linear-plus-slack ceiling:
    for a 2x size step, quadratic would score ~2.0, so 1.8 catches it while
    tolerating constant-factor and measurement noise.

    If t1 < min_time the sizes are too small to measure reliably; ok=True with a
    note (do not fail on unmeasurable timings — that is the flake source)."""
    t1 = time_op(lambda: run_at(n1), repeat=repeat)
    t2 = time_op(lambda: run_at(n2), repeat=repeat)
    size_ratio = n2 / n1
    if t1 < min_time:
        return ScalingResult(n1, n2, t1, t2, t2 / t1 if t1 else float("inf"),
                             size_ratio, 0.0, True,
                             f"t1={t1*1e3:.1f}ms < {min_time*1e3:.0f}ms floor — "
                             f"too fast to measure; not asserting")
    ratio = t2 / t1
    growth = ratio / size_ratio
    ok = growth <= max_growth
    detail = (f"n {n1}->{n2}: {t1*1e3:.1f}ms->{t2*1e3:.1f}ms, growth {growth:.2f} "
              f"(1.0=linear, {size_ratio:.1f}=quadratic; ceiling {max_growth})")
    return ScalingResult(n1, n2, t1, t2, ratio, size_ratio, growth, ok, detail)
