"""Super-solution tester (pattern #4) — exact, with the divergence caveat.

A candidate `P` is a SUPER-SOLUTION of a Bellman-style operator `T` if it
dominates its own update everywhere: `P(pt) >= (T P)(pt)` at every point.  A
valid super-solution is an upper bound on the value function (value iteration
from it only descends), which is how the concave-hull / value-function machinery
in `bellman.py` is used to bound `Phi`.

This is the exact-arithmetic counterpart of that test.  `bellman.py` works in
floats (fine for hull geometry and search); a super-solution VERDICT must not
hang on a float, so this decides `P >= T P` in exact rationals and returns a
ProbeVerdict.

THE CAVEAT (load-bearing, from the crux campaign): a per-node / LOCAL
super-solution can pass pointwise here and still FAIL globally, because value
iteration on a BRANCHING recursion has non-local coupling — the per-node
telescoping potential verified <= 0.93 locally but its per-node super-solution
failed on the relaxed domain.  So a VALIDATED verdict from this test is scoped to
"dominates T on the probe set"; it does NOT certify a global super-solution on a
branching domain.  When `branching=True` is declared, a pass is downgraded to an
explicit OBSTRUCTED_AND_LOCATED note locating the coupling caveat, so the test
can never silently overclaim a global bound.  conjecture1_proved=False.
"""
from __future__ import annotations

from .verdict import ProbeVerdict, decide, null, obstructed, require_exact, validated


def super_solution_check(candidate, operator, points, *, branching: bool = False,
                         label: str = "candidate") -> ProbeVerdict:
    """Does `candidate` dominate its Bellman update `operator` on `points`?

    candidate(pt), operator(pt) -> exact value (int / Fraction / sympy Rational),
    where operator(pt) is (T candidate)(pt), the one-step update at pt.
    branching=True declares the recursion is branching (non-local coupling), so
    even a clean pointwise pass is returned as OBSTRUCTED-with-caveat rather than
    a global VALIDATED — the campaign's per-node-super-solution-fails lesson."""
    pts = list(points)
    if not pts:
        return null(f"super-solution {label}", "no points supplied")

    worst = None  # (deficit, pt, P, TP) with the most negative slack P - TP
    for pt in pts:
        P = require_exact(candidate(pt), f"{label}.P@{pt}")
        TP = require_exact(operator(pt), f"{label}.TP@{pt}")
        slack = P - TP
        if not decide(P, ">=", TP, f"{label}@{pt}"):
            # located violation: value iteration would push P up here (and, on a
            # branching domain, is exactly where divergence can start).
            return obstructed(
                f"super-solution {label}",
                obstruction=(
                    f"domination fails at {pt}: P={P} < (T P)={TP} (deficit "
                    f"{slack}). Value iteration lifts P here; not a super-solution."
                ),
            )
        if worst is None or slack < worst[0]:
            worst = (slack, pt, P, TP)

    if branching:
        return obstructed(
            f"super-solution {label} (global, branching domain)",
            obstruction=(
                f"pointwise domination holds on all {len(pts)} probe points "
                f"(tightest slack {worst[0]} at {worst[1]}), BUT the recursion is "
                f"branching — a per-node super-solution need not hold globally "
                f"(non-local coupling; the per-node telescoping potential passed "
                f"locally yet failed on the relaxed domain). Not a global bound."
            ),
            detail="the value-iteration branching-divergence caveat; scope is local only",
        )
    return validated(
        f"{label} dominates T on the probe",
        f"P >= (T P) at all {len(pts)} probe point(s); tightest slack {worst[0]} "
        f"at {worst[1]} — a valid super-solution on this (non-branching) probe",
    )
