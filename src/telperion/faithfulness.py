"""Faithfulness cross-check — pattern #1 from the methodology campaign.

HONEST SCOPE: a first-class checker that cross-checks a primary implementation
against an INDEPENDENT one at seeded EXACT rational points and REFUSES on any
disagreement.  Generalises the scattered `_dual_engine_check` in certify.py into
a standalone, composable primitive.

Background: `_dual_engine_check` (certify.py ~line 210) caught a real bug where a
recursion model was UNFAITHFUL to the object it claimed to represent (wrong for
cherry-trees), which would have invalidated half a session's findings.  That
pattern is now promoted here so any probe can invoke it explicitly, in the correct
verdict taxonomy, before trusting its own numerics.

Load-bearing discipline: every comparison that decides a verdict runs through
`require_exact` / `decide` — NO floats at decision points.  A float returned by
either implementation at a decision point is refused loudly
(`FloatAtDecisionPoint`), exactly as `emit()` refuses an unvalidated claim.

conjecture1_proved=False.
"""
from __future__ import annotations

import random
from fractions import Fraction
from typing import Any, Callable

from .verdict import (
    FloatAtDecisionPoint,  # noqa: F401 — re-exported for callers
    ProbeVerdict,
    decide,
    null,
    obstructed,
    require_exact,
    validated,
)


def seeded_rational_points(
    symbols: list[str],
    n: int,
    seed: int,
    lo: int = 0,
    hi: int = 60,
    denom_hi: int = 6,
) -> list[dict[str, Fraction]]:
    """Generate *n* deterministic exact-rational sample points.

    Each coordinate is an independent `Fraction(randint(lo, hi),
    randint(1, denom_hi))` — the same seeding style used in
    `_dual_engine_check`.  Determinism is guaranteed by the explicit `seed`; do
    NOT call `random.seed()` globally (that would corrupt other callers).

    Parameters
    ----------
    symbols:
        Variable names (strings) — keys in the returned dicts.
    n:
        Number of distinct points to generate.
    seed:
        Explicit RNG seed; the same seed + symbols + n always produces the same
        grid, so cross-check results are reproducible across runs.
    lo, hi:
        Integer range for numerators (inclusive).
    denom_hi:
        Upper bound for denominators (randint(1, denom_hi) — always >= 1).
    """
    rng = random.Random(seed)
    pts: list[dict[str, Fraction]] = []
    for _ in range(n):
        pt = {
            sym: Fraction(rng.randint(lo, hi), rng.randint(1, denom_hi))
            for sym in symbols
        }
        pts.append(pt)
    return pts


def faithfulness_check(
    primary: Callable[[Any], Any],
    independent: Callable[[Any], Any],
    points: list[Any],
    *,
    label: str = "target",
) -> ProbeVerdict:
    """Cross-check *primary* against *independent* at every point in *points*.

    Both callables must accept a single argument (a point — a dict of
    `str -> Fraction` from `seeded_rational_points`, or any hashable seed the
    caller chooses) and return an exact rational (int / Fraction / sympy
    Rational).  The return values are coerced via `require_exact`; a Python
    float or sympy Float raises `FloatAtDecisionPoint` immediately — the
    no-floats-at-decision-points discipline is enforced through this checker.

    Verdicts
    --------
    VALIDATED
        All points agree exactly and `points` is non-empty.
    OBSTRUCTED_AND_LOCATED
        The two implementations disagree at some point; the obstruction names
        the witness (the point and both exact values).  This is the caught-bug
        case: one implementation is wrong, and the witness locates it.
    NULL
        `points` is empty — nothing was cross-checked.  A clean negative, not a
        pass.

    Parameters
    ----------
    primary:
        The main implementation being validated.
    independent:
        A separate, independently-written implementation of the same function.
    points:
        Evaluation points.  A list of dicts `{symbol: Fraction}` from
        `seeded_rational_points` is the canonical choice; any list of arguments
        accepted by both callables is fine.
    label:
        Short description of what is being checked (appears in evidence strings).
    """
    if not points:
        return null(
            f"faithfulness cross-check: {label}",
            "no points supplied — nothing cross-checked (clean negative, not a pass)",
        )

    n_checked = 0
    for pt in points:
        primary_raw = primary(pt)
        independent_raw = independent(pt)

        # Coerce both through require_exact — floats at decision points are refused.
        p_exact = require_exact(primary_raw, f"{label}.primary at {pt!r}")
        i_exact = require_exact(independent_raw, f"{label}.independent at {pt!r}")

        if not decide(p_exact, "==", i_exact, label=f"{label} agreement at {pt!r}"):
            return obstructed(
                f"faithfulness cross-check: {label}",
                obstruction=(
                    f"disagreement at point {pt!r}: "
                    f"primary={p_exact}, independent={i_exact}"
                ),
                detail=(
                    f"checked {n_checked} point(s) before locating witness; "
                    f"one implementation is wrong"
                ),
            )
        n_checked += 1

    return validated(
        f"faithfulness cross-check: {label}",
        f"{n_checked} point(s) cross-checked; primary and independent agreed exactly at every point",
        f"label={label!r}",
    )
