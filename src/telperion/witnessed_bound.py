"""Witnessed-bound guard — a faithfulness discipline for optimizers.

An upper-bound function used to GATE an optimizer must be WITNESSED: at every
point where the bound is consulted, some real object must actually attain it.  A
bound value that no real object achieves is a PHANTOM bound — and an optimizer
handed a phantom bound will "cheat" into a false violation at exactly the phantom
point, because it can place a variable there for free.

This is the Brualdi–Goldwasser flat-arm red herring, generalized: the loose
envelope used a flat `arm = 0.919` at `μ = 0.797` where the real F-max is only
`F_ns(0.797) = 0.17`, so the constrained optimizer manufactured a "violation"
there that no real tree can realize.  It sprang three times in one session.

`witnessed_bound_check` cross-checks a claimed bound against the real (witnessed)
bound at seeded EXACT-rational points and refuses the first phantom, turning
"the optimizer cheated" from a silent false OBSTRUCTED into a located verdict.
It is `faithfulness_check` specialized to bound functions: the phantom point IS
the disagreement witness.  Exact rationals at the decision (no floats) —
consistent with [[verdict]] and [[faithfulness]].  conjecture1_proved=False.
"""
from __future__ import annotations

from .verdict import ProbeVerdict, decide, null, obstructed, require_exact, validated


def witnessed_bound_check(claimed_bound, witnessed_bound, points, *,
                          tol=0, label="bound") -> ProbeVerdict:
    """Is `claimed_bound` witnessed (never exceeds what a real object attains)?

    claimed_bound(pt), witnessed_bound(pt) -> exact value.  `witnessed_bound(pt)`
    is the max over REAL objects at pt (the tightest a real witness gives); the
    claimed bound is faithful iff `claimed ≤ witnessed + tol` everywhere.  A point
    with `claimed > witnessed` is a PHANTOM — the located spot an optimizer would
    cheat.  Returns OBSTRUCTED_AND_LOCATED at the first phantom, else VALIDATED,
    or NULL if nothing was probed."""
    pts = list(points)
    if not pts:
        return null(f"witnessed bound {label}", "no points supplied")
    t = require_exact(tol, f"{label}.tol")
    for pt in pts:
        c = require_exact(claimed_bound(pt), f"{label}.claimed@{pt}")
        w = require_exact(witnessed_bound(pt), f"{label}.witnessed@{pt}")
        if decide(c, ">", w + t, f"{label}@{pt}"):
            return obstructed(
                f"witnessed bound {label}",
                obstruction=(
                    f"PHANTOM bound at {pt}: claimed {c} > witnessed {w} — no real "
                    f"object attains {c} here, so an optimizer gated by this bound "
                    f"will cheat into a false violation at this point. Tighten the "
                    f"bound to the witnessed value before optimizing against it."
                ),
                detail="the flat-arm red-herring guard; every gate value must have a real witness",
            )
    return validated(
        f"{label} is witnessed",
        f"claimed ≤ witnessed at all {len(pts)} probe points — no phantom gate value",
    )
