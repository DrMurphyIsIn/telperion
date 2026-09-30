"""Negative-control adapter for SingleCrossingLadderEmitter (single crossing + ladder).

The instance is one pair of the arm ladder, A_3 against A_4:

    F_j(x) = ((j-1)/(2j+1)) log(1 + x/2) + (1/(2j+1)) log(1 + (2j+1)/(2j+2) x),

whose difference D = F_3 - F_4 has its unique zero on (0, oo) at lambda_3 = 0.4305018...
The emitted crossing theorem is

    theorem nm_p3_cross : ∃ c ∈ Set.Ioo lo hi, F 3 c = F 4 c ∧ ∀ x ∈ S, 0 < x → ...

and it consumes the bracket values `0 < F 3 lo - F 4 lo` and `F 3 hi - F 4 hi < 0`.

FALSE forgery: the bracket shifted two grid steps right, (0.43052, 0.43053).  It misses
lambda_3, so `D(0.43052) > 0` is FALSE (D < 0 past lambda_3), not merely unproved.  Layer 1
(`single_crossing_ladder_certificate`) refuses it: the enclosure fold does not imply the
sign.  The adapter mints it with ``check=False``: the sign cells, the factorisation and the
log atoms are the honest ones (claim-free atom enclosures at a fixed Taylor order), and ONLY
the bracket is wrong.  The kernel is the arbiter: the value theorem's `linarith` from the
log-atom brackets cannot reach a false sign.

TRUE twin: the honest bracket (0.43050, 0.43051), byte-for-byte the dogfood pair.

The double-crossing control (the synthetic family on [0, oo), claimed single) is exercised
by tests/test_negctrl_single_crossing_ladder.py with the same harness.

conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_single_crossing_ladder import (
    ARM_PAIR3_SPEC,
    ARM_PAIR3_WRONG_BRACKET_SPEC,
    DOUBLE_DIP_BOUNDED_SPEC,
    DOUBLE_DIP_UNBOUNDED_SPEC,
    SingleCrossingCert,
    SingleCrossingLadderEmitter,
    single_crossing_ladder_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_true_cert() -> SingleCrossingCert:
    """The honest pair certificate (bracket (0.43050, 0.43051))."""
    return single_crossing_ladder_certificate(**ARM_PAIR3_SPEC)


def make_false_cert() -> SingleCrossingCert:
    """Hand-forged FALSE cert: the bracket (0.43052, 0.43053), which misses lambda_3,
    built with every Layer-1 sign check skipped."""
    return single_crossing_ladder_certificate(**ARM_PAIR3_WRONG_BRACKET_SPEC, check=False)


def make_true_double_dip_cert() -> SingleCrossingCert:
    """The synthetic double-dip family on S = [0, 2], where the crossing IS single."""
    return single_crossing_ladder_certificate(**DOUBLE_DIP_BOUNDED_SPEC)


def make_false_double_dip_cert() -> SingleCrossingCert:
    """Hand-forged FALSE cert: the same family on [0, oo), where D crosses TWICE, claimed
    single (the tail cell asserts N < 0 on [b, oo), false past N's second root)."""
    return single_crossing_ladder_certificate(**DOUBLE_DIP_UNBOUNDED_SPEC, check=False)


def _emit(cert: SingleCrossingCert, name: str) -> str:
    return emit_via_single_instance_family(
        SingleCrossingLadderEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


ADAPTER = NegativeControlAdapter(
    emitter_name="SingleCrossingLadderEmitter",
    make_false_cert=make_false_cert,
    make_true_cert=make_true_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "forged breakpoint bracket (0.43052, 0.43053) for the A_3/A_4 arm crossing "
        "(false: lambda_3 = 0.4305018... lies left of it, so D(lo) < 0): the value "
        "theorem's linarith from the log-atom brackets cannot reach the false sign and the "
        "kernel rejects it; the true twin (0.43050, 0.43051) compiles"
    ),
    imports_line="import Mathlib",
)

#: The double-crossing control, run by the tests with the same harness (not registered:
#: the registry holds one adapter per emitter).
DOUBLE_DIP_ADAPTER = NegativeControlAdapter(
    emitter_name="SingleCrossingLadderEmitter",
    make_false_cert=make_false_double_dip_cert,
    make_true_cert=make_true_double_dip_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "forged single crossing on [0, oo) for a family that crosses twice (near 0.971 and "
        "4.315): the tail sign cell's linarith cannot prove N < 0 past N's second root and "
        "the kernel rejects it; the true twin on [0, 2] compiles"
    ),
    imports_line="import Mathlib",
)

register(ADAPTER)
