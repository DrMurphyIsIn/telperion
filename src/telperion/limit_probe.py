"""Large-tree-limit probe -- anti-size-bounded-trap (pattern #2).

SCOPE
-----
A first-class probe that evaluates a size-parameterised claim at a sequence of
increasing sizes and classifies the *trend* of the margin as the limit is
approached.

THE TRAP
--------
In the Brualdi-Goldwasser crux campaign the size-bounded-trap sprang at least
four times: arm-dominance held only for k >= 19, the disposal argument held only
for bounded subtrees, and frontier / spectral-truncation results held only for
low-degree cases.  In every instance the trap looked like a PASS on small probed
sizes followed by a failure that only emerged when size grew.

This module makes the anti-trap discipline structural:

  * All margin decisions are EXACT (int / Fraction / sympy Rational).
  * Float margins at decision points raise FloatAtDecisionPoint immediately.
  * A claim that holds for small n but fails at larger n → OBSTRUCTED_AND_LOCATED
    at the SMALLEST breaking size.
  * A claim whose margin DEGRADES toward zero as size grows — "true so far but
    heading to the boundary" — also returns OBSTRUCTED_AND_LOCATED with the
    located degradation trend.  Silence on a shrinking margin is how the trap
    sprang; this probe refuses that silence.
  * A claim whose margin is non-decreasing (or at least bounded away from zero
    without degradation) across all probed sizes → VALIDATED with the exact
    margin sequence as evidence.
  * Empty sizes → NULL.

MARGIN CONTRACT
---------------
`claim(n)` must return one of:
  - An exact-rational margin: int, Fraction, or sympy Rational / Integer.
    Positive means the claim holds at that size; zero or negative means it
    fails (or is exactly at the boundary).
  - A bool: treated as Fraction(1) for True and Fraction(0) for False.
    (A bool False is treated as a failing margin of 0, which is caught as a
    violation at the boundary.)

A Python float anywhere that would reach a decision is refused via
FloatAtDecisionPoint — the same discipline as `require_exact` / `decide` in
verdict.py.

DEGRADATION CRITERION
---------------------
After a fully-passing probe (no size failed outright) we compute the sequence
of consecutive margin differences (delta_i = m_{i+1} - m_i) in exact arithmetic.
If the margin is STRICTLY DECREASING overall (first delta < 0 AND last delta < 0
AND the sequence ends lower than it started) we declare OBSTRUCTED_AND_LOCATED
with a "margin shrinking toward limit" obstruction.  A flat or growing margin
(or one that fluctuates but does not end lower than it started) is VALIDATED.

This is intentionally tight: a probe with a minor dip mid-sequence but ending
higher is VALIDATED (noise is possible); one that ends lower than it started
is flagged (the trend is downward at the limit).

conjecture1_proved = False
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, Union

import sympy as sp

from .verdict import (
    FloatAtDecisionPoint,
    ProbeVerdict,
    decide,
    null,
    obstructed,
    require_exact,
    validated,
)

# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _coerce_margin(value, n: int) -> Fraction:
    """Coerce a claim(n) return value to an exact Fraction, or refuse.

    Accepts bool (True -> 1, False -> 0), int, Fraction, sympy Rational /
    Integer.  Refuses Python float and sympy Float."""
    if isinstance(value, bool):
        return Fraction(int(value))
    return require_exact(value, label=f"margin at size {n}")


def _margin_summary(sizes: list[int], margins: list[Fraction]) -> str:
    """Exact one-line summary: size -> margin for each probed point."""
    parts = [f"n={n}: {m}" for n, m in zip(sizes, margins)]
    return ", ".join(parts)


def _delta_summary(sizes: list[int], margins: list[Fraction]) -> str:
    """Consecutive differences in exact arithmetic, for evidence."""
    if len(margins) < 2:
        return "(single point, no differences)"
    deltas = [margins[i + 1] - margins[i] for i in range(len(margins) - 1)]
    def _signed(x: Fraction) -> str:
        return ("+" if x >= 0 else "") + str(x)

    pairs = [
        f"n={sizes[i]}->{sizes[i+1]}: {_signed(deltas[i])}"
        for i in range(len(deltas))
    ]
    return "deltas: " + ", ".join(pairs)


def _is_degrading(margins: list[Fraction]) -> bool:
    """True iff the margin sequence ends strictly lower than it started.

    Both the first difference and the last difference must be negative AND
    the final margin is strictly less than the first.  This catches a clean
    downward trend while tolerating mid-sequence fluctuations."""
    if len(margins) < 2:
        return False
    first_delta = margins[1] - margins[0]
    last_delta = margins[-1] - margins[-2]
    net = margins[-1] - margins[0]
    # Exact comparisons only (all Fraction arithmetic above).
    return (
        decide(first_delta, "<", Fraction(0), "first_delta")
        and decide(last_delta, "<", Fraction(0), "last_delta")
        and decide(net, "<", Fraction(0), "net_trend")
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def limit_probe(
    claim: Callable[[int], Union[int, Fraction, sp.Basic, bool]],
    sizes: Iterable[int],
    *,
    label: str = "claim",
) -> ProbeVerdict:
    """Evaluate a size-parameterised claim at increasing sizes; classify the limit trend.

    Parameters
    ----------
    claim:
        A callable ``claim(n) -> margin`` where ``n`` is a positive integer and
        the return value is an exact-rational margin (int / Fraction / sympy
        Rational / Integer) or a bool.  Positive margin = holds; zero or
        negative = fails or is exactly at boundary.
    sizes:
        An increasing iterable of integer sizes at which to probe.
    label:
        Human-readable name of the claim, used in verdict strings.

    Returns
    -------
    ProbeVerdict with one of:
      VALIDATED              -- holds at every probed size, margin non-degrading.
      OBSTRUCTED_AND_LOCATED -- either (a) fails outright at some size (located
                                at the smallest breaking size) or (b) holds at
                                every size but margin is shrinking toward the
                                limit (located degradation trend).
      NULL                   -- ``sizes`` was empty.
    """
    size_list = list(sizes)
    if not size_list:
        return null(
            label,
            detail="no sizes to probe — cannot assess large-size limit",
        )

    margins: list[Fraction] = []
    probed_sizes: list[int] = []

    for n in size_list:
        raw = claim(n)
        # _coerce_margin refuses floats via require_exact (FloatAtDecisionPoint)
        m = _coerce_margin(raw, n)
        probed_sizes.append(n)
        margins.append(m)

        # Exact decision: does the claim hold at this size?
        if not decide(m, ">", Fraction(0), f"margin_positive(n={n})"):
            # Size-bounded trap: found the smallest breaking size.
            summary = _margin_summary(probed_sizes, margins)
            return obstructed(
                label,
                f"size n={n}: margin={m} (non-positive) — size-bounded trap located here",
                summary,
                detail=(
                    f"claim held for smaller sizes but failed at n={n}; "
                    f"this is the anti-size-bounded-trap catch"
                ),
            )

    # All sizes passed.  Assess the limit trend via exact margin arithmetic.
    summary = _margin_summary(probed_sizes, margins)
    delta_str = _delta_summary(probed_sizes, margins)

    if _is_degrading(margins):
        # Margin is heading toward zero as size grows: the trap's warning sign.
        return obstructed(
            label,
            (
                f"margin shrinking toward limit: "
                f"started at {margins[0]}, ended at {margins[-1]} — "
                f"trend toward violation as n -> infinity"
            ),
            summary,
            delta_str,
            detail=(
                "holds at all probed sizes but margin is degrading; "
                "extend the probe or seek a closed-form bound; "
                "silence on a shrinking margin is how the trap sprang"
            ),
        )

    # Non-degrading across all probed sizes: validated.
    return validated(
        label,
        summary,
        delta_str,
        f"largest probed size: n={probed_sizes[-1]}, final margin={margins[-1]}",
        detail=(
            f"holds at {len(probed_sizes)} probed sizes with non-degrading margin"
        ),
    )
