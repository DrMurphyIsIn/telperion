"""Sampled -> proof upgradability test (pattern #7).

Distilled from the crux campaign's distinction between a MECHANICAL result
(HypDepth3Generic: a finite, complete case cover that Lean's `interval_cases`
upgrades to a theorem by exhaustion) and a CONCEPTUAL seam (a claim over an
unbounded parameter, where a finite sample is only a probe and the general case
is the real work — sampling can never cross it).

Conflating the two is how a finite check masquerades as a proof.  This test
takes what was actually SAMPLED and what is CLAIMED and returns:

  * VALIDATED               — the sample is a COMPLETE finite cover of the claim
                              (mechanical; upgradable by exhaustion).
  * OBSTRUCTED_AND_LOCATED  — either a finite coverage GAP (the uncovered cases,
                              mechanically closable by sampling them), or a
                              genuine CONCEPTUAL SEAM at an unbounded axis (the
                              sample is finite, the claim is not — needs a
                              general argument: induction, a limit, a transfer
                              operator; located at that axis).
  * NULL                    — nothing claimed to upgrade.

Domain membership is exact (finite sets); no floats decide coverage.
conjecture1_proved=False.
"""
from __future__ import annotations

from .verdict import ProbeVerdict, null, obstructed, validated

# Sentinel: the claim ranges over an unbounded / infinite domain on some axis.
UNBOUNDED = "UNBOUNDED"


def _canon(pt) -> tuple:
    """Canonicalize a grid point (dict) to a hashable, order-stable key."""
    if isinstance(pt, dict):
        return tuple(sorted((str(k), str(v)) for k, v in pt.items()))
    return (str(pt),)


def upgradability_check(sampled, claimed, *, unbounded_axes=(),
                        label: str = "claim") -> ProbeVerdict:
    """Is a sample-verified claim upgradable to a proof by exhaustion, or is
    there a conceptual seam?

    sampled: finite iterable of the points actually verified.
    claimed: either a finite iterable of the full claimed points, or the
             sentinel UNBOUNDED when the claim ranges over an unbounded domain.
    unbounded_axes: names of axes the claim is unbounded on (locates the seam)."""
    sampled_set = {_canon(p) for p in sampled}

    # Conceptual seam: an unbounded claim can never be a finite complete cover.
    if claimed is UNBOUNDED or unbounded_axes:
        axes = ", ".join(unbounded_axes) if unbounded_axes else "the claimed range"
        return obstructed(
            f"upgradability of {label}",
            obstruction=(
                f"CONCEPTUAL SEAM: the sample verifies {len(sampled_set)} finite "
                f"case(s), but the claim is unbounded on [{axes}]. Exhaustion "
                f"cannot cross this — the general case needs a genuine argument "
                f"(induction / limit / transfer operator), not more samples."
            ),
            detail="mechanical-vs-conceptual: this is the conceptual side",
        )

    claimed_set = {_canon(p) for p in claimed}
    if not claimed_set:
        return null(f"upgradability of {label}", "no claimed domain supplied")

    uncovered = claimed_set - sampled_set
    if not uncovered:
        return validated(
            f"{label} is mechanically upgradable",
            f"the sample is a COMPLETE finite cover of the {len(claimed_set)} "
            f"claimed case(s) — upgradable to a theorem by exhaustion "
            f"(interval_cases / finite dispatch)",
        )
    shown = ", ".join(str(dict(u)) for u in sorted(uncovered)[:5])
    more = "" if len(uncovered) <= 5 else f" (+{len(uncovered) - 5} more)"
    return obstructed(
        f"upgradability of {label}",
        obstruction=(
            f"finite coverage GAP: {len(uncovered)} of {len(claimed_set)} claimed "
            f"case(s) unsampled — {shown}{more}. Mechanically closable: sample "
            f"the missing cases (no conceptual seam, just incomplete exhaustion)."
        ),
    )


def upgradability_of_family(family, *, unbounded_axes=()) -> ProbeVerdict:
    """Convenience: read the sample (the family's grid) against the claim.

    With no `unbounded_axes`, the grid IS the claimed finite domain -> mechanical
    (VALIDATED).  Declare the axes on which the family's claim is really meant to
    hold for ALL values (e.g. a size parameter) to surface the conceptual seam."""
    grid_pts = list(family.grid.points())
    if unbounded_axes:
        return upgradability_check(grid_pts, UNBOUNDED,
                                   unbounded_axes=tuple(unbounded_axes),
                                   label=family.name)
    return upgradability_check(grid_pts, grid_pts, label=family.name)
