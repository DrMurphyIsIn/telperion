"""Discharging-conservation checker (pattern #5).

A discharging argument assigns an initial charge to each node, redistributes
charge along local rules, and concludes a per-node bound from the redistributed
charges — the whole thing sound ONLY IF redistribution conserves total charge
exactly.  The campaign's Lean-portable discharging (G1Discharge / G1ConsTree) is
machine-checked in the origin (proof) repo; that formalization is not this
module's to reach into.

What Telperion owns is the exact-arithmetic INVARIANT such a proof rests on: a
checker that (1) applies the transfers, (2) verifies total charge is conserved
to the last unit in exact rationals, and (3) checks the post-discharge per-node
target — returning a ProbeVerdict.  A float can never decide conservation here;
an off-by-anything transfer is located, not absorbed.

  * VALIDATED               — charge conserved exactly AND every node meets the
                              target (if one is given).
  * OBSTRUCTED_AND_LOCATED  — conservation broken (a non-conservative rule, with
                              the exact discrepancy), or a node that misses the
                              target after discharging (located).
  * NULL                    — nothing to discharge.

conjecture1_proved=False.
"""
from __future__ import annotations

from .verdict import ProbeVerdict, decide, null, obstructed, require_exact, validated


def discharging_check(initial_charges, transfers, *, target=None,
                      target_op: str = "<=", label: str = "discharging") -> ProbeVerdict:
    """Verify a discharging scheme conserves charge and meets its per-node target.

    initial_charges: dict node -> exact initial charge.
    transfers: iterable of (src, dst, amount) — amount moves from src to dst
               (exact).  src/dst must be keys in initial_charges.
    target: optional exact bound; each final charge is checked `final <target_op>
            target` (default final <= target).  None skips the per-node check.
    target_op: one of the comparison operators understood by `decide`."""
    if not initial_charges:
        return null(f"{label}", "no charges supplied")

    transfers = list(transfers)
    total_before = sum((require_exact(c, f"init[{k}]") for k, c in initial_charges.items()),
                       start=require_exact(0))
    final = {k: require_exact(c, f"init[{k}]") for k, c in initial_charges.items()}

    for i, (src, dst, amount) in enumerate(transfers):
        amt = require_exact(amount, f"transfer[{i}].amount")
        if src not in final or dst not in final:
            return obstructed(
                f"{label}",
                obstruction=f"transfer {i} references unknown node "
                            f"({src!r}->{dst!r}); nodes are {sorted(final)}",
            )
        final[src] = final[src] - amt
        final[dst] = final[dst] + amt

    total_after = sum(final.values(), start=require_exact(0))
    if not decide(total_after, "==", total_before, f"{label}.conservation"):
        return obstructed(
            f"{label} conservation",
            obstruction=(
                f"charge NOT conserved: total before {total_before}, after "
                f"{total_after} (discrepancy {total_after - total_before}) — a "
                f"non-conservative redistribution rule invalidates the argument"
            ),
        )

    if target is not None:
        tgt = require_exact(target, f"{label}.target")
        misses = [(k, v) for k, v in sorted(final.items())
                  if not decide(v, target_op, tgt, f"{label}.target[{k}]")]
        if misses:
            shown = ", ".join(f"{k}:{v}" for k, v in misses[:5])
            more = "" if len(misses) <= 5 else f" (+{len(misses) - 5} more)"
            return obstructed(
                f"{label} target",
                obstruction=(
                    f"charge conserved, but {len(misses)} node(s) miss the target "
                    f"(final {target_op} {tgt}): {shown}{more}"
                ),
            )

    tgt_note = "" if target is None else f"; every node satisfies final {target_op} {target}"
    return validated(
        f"{label} is charge-conserving",
        f"total charge {total_before} conserved exactly across "
        f"{len(transfers)} transfer(s){tgt_note}",
    )
