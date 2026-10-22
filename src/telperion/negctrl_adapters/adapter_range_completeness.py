"""Negative-control adapter for RangeCompletenessEmitter (kernel-decided list coverage).

The coverage theorem `∀ m ∈ Finset.range N, SqfBelow K m → m ∉ excl → m ∈ L` is decided by
`decide +kernel`; the list `L` IS the statement, and the kernel re-runs every membership.
The load-bearing content is therefore the list itself.

FALSE forgery: the honest certificate for N = 60, K = 8 (64 > 60), with the seven Heegner
radicands below 60 excluded, and the LARGEST element of L (59, a prime, squarefree, not
excluded) DROPPED.  m = 59 then satisfies every guard and is not in the list, so the
`Finset.range 60` fold reaches `59 ∈ L` and the kernel's `Decidable` evaluation is `false`:
`decide +kernel` fails and the theorem is rejected.  Layer 1 would never mint it
(`range_completeness_certificate` refuses the false coverage and names m = 59); the adapter
edits the frozen dataclass BY HAND, bypassing that, exactly as `adapter_scaled_interval_eval`
does, so the kernel is the arbiter.

TRUE twin: the same certificate unmodified -- compiles clean and axiom-clean.  The two emitted
texts differ in exactly one line (the list literal).

Only the coverage theorem is emitted for the control (no length / nodup / soundness
companions), so the rejection is pinned to the coverage `decide`, not to a companion that
would ALSO be false (`length = 31` against a 30-element list).

Both twins elaborate over Mathlib alone.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

from telperion.emit_range_completeness import (
    RangeCompletenessEmitter,
    SquarefreeSurrogate,
    range_completeness_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_N, _K = 60, 8
_EXCL = (1, 2, 3, 7, 11, 19, 43)          # the Heegner radicands below 60


def _squarefree_below(n: int, k: int) -> list[int]:
    return [m for m in range(n) if all(m % (j * j) != 0 for j in range(2, k + 1))]


def make_true_cert():
    """The honest certificate: the 30 squarefree m < 60 outside the seven, with K = 8."""
    members = [m for m in _squarefree_below(_N, _K) if m not in _EXCL]
    cert, _n = range_completeness_certificate(
        _N, members, exclude=_EXCL, surrogate=SquarefreeSurrogate(_K))
    return cert


def make_false_cert():
    """The honest certificate with its largest element (59) dropped: m = 59 is uncovered."""
    cert = make_true_cert()
    assert cert.members[-1] == 59
    return replace(cert, members=cert.members[:-1])


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        RangeCompletenessEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="RangeCompletenessEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "squarefree m < 60 outside the seven Heegner radicands, with 59 dropped from the "
            "list: the kernel's `decide +kernel` over Finset.range 60 reaches 59 ∉ L and is "
            "false; the unmodified twin compiles"
        ),
        imports_line="import Mathlib",
    )
)
