"""Circularity / strength check (pattern #6) — refuse a lemma that assumes the goal.

Distilled from the crux campaign, where it caught the spectral-gap mis-framing:
a proposed intermediate bound that, on inspection, IMPLIED the conjecture — so
"reducing to it" reduced nothing, and proving it would have been circular.

The test is a strength comparison over an EXACT probe set.  Given a proposed
`lemma` and the `goal` it is meant to reduce toward — both as `pt -> exact
margin` (margin >= 0 means the claim holds at pt), or as booleans — a lemma is a
PROPER reduction only if there is a point where the lemma holds but the goal
does not (a separating witness: the lemma is genuinely weaker / independent).

  * A separating witness (lemma holds, goal fails) PROVES non-circularity there
    -> VALIDATED.
  * No separating witness across the whole probe -> the lemma implies the goal
    on everything tested; proving it is not a proper reduction -> the
    circularity is OBSTRUCTED_AND_LOCATED (suspected, with the probe as the
    located evidence).  Honest scope: absence of a witness over a finite exact
    probe SUGGESTS circularity; it does not prove implication on a continuous
    domain — so the located verdict says "suspected", and finding one witness
    later flips it to VALIDATED.

Exact arithmetic at every decision point (`decide`/`require_exact`).  No floats
decide circularity.  conjecture1_proved=False.
"""
from __future__ import annotations

from .verdict import ProbeVerdict, decide, null, obstructed, require_exact, validated


def _margin(fn, pt):
    """Evaluate a lemma/goal at pt to an exact margin (>=0 means it holds).
    A bool True/False maps to margin 0 / -1 (holds / fails), exactly."""
    val = fn(pt)
    if isinstance(val, bool):
        return require_exact(0 if val else -1, "margin")
    return require_exact(val, "margin")


def circularity_check(lemma, goal, points, *, label: str = "lemma vs goal") -> ProbeVerdict:
    """Is proving `lemma` a proper reduction toward `goal`, or does it assume it?

    lemma(pt), goal(pt) -> exact margin (>=0 holds) or bool.  points: an iterable
    of grid points (dicts) to probe, ideally including declared tie points.

    Returns VALIDATED (non-circular: a separating witness exists), or
    OBSTRUCTED_AND_LOCATED (circularity suspected / lemma == goal on the probe),
    or NULL (nothing probed)."""
    pts = list(points)
    if not pts:
        return null(f"circularity of {label}", "no probe points supplied")

    identical = True
    for pt in pts:
        lm = _margin(lemma, pt)
        gm = _margin(goal, pt)
        lemma_holds = decide(lm, ">=", 0, f"{label}.lemma@{pt}")
        goal_holds = decide(gm, ">=", 0, f"{label}.goal@{pt}")
        if lm != gm:
            identical = False
        # separating witness: lemma holds but goal does not -> lemma is strictly
        # weaker here, so it does NOT imply the goal -> non-circular, proven.
        if lemma_holds and not goal_holds:
            return validated(
                f"{label} is a proper (non-circular) reduction",
                f"separating witness at {pt}: lemma margin {lm} >= 0 while goal "
                f"margin {gm} < 0 — the lemma holds where the goal does not, so "
                f"it does not assume the goal",
            )

    if identical:
        return obstructed(
            f"circularity of {label}",
            obstruction=(
                f"lemma margin == goal margin at all {len(pts)} probe points — "
                f"the 'lemma' is the goal restated; proving it is circular"
            ),
        )
    return obstructed(
        f"circularity of {label}",
        obstruction=(
            f"no separating witness over {len(pts)} probe points: the lemma holds "
            f"only where the goal already does (lemma => goal on the probe). "
            f"Proving it is not a proper reduction toward the goal — suspected "
            f"circular. Exhibit a point where the lemma holds and the goal fails "
            f"to clear this."
        ),
        detail="suspected on a finite exact probe; one separating witness flips it to VALIDATED",
    )
