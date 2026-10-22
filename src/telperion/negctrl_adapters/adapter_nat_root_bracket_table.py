"""Negative-control adapter for NatRootBracketTableEmitter (kernel-decided root brackets).

Every table entry is a literal natural ``lo`` with the kernel-decided fact
``lo^q * m^p <= S^q`` (``∀ n < K`` over the block); the load-bearing content is the literal
list itself.

FALSE forgery: the honest table for ``∑_{i<40} (i+1)^(-3/4)`` at scale ``10^10`` in two blocks
of 20, with ONE entry of the second block's ``lo`` list raised by 1 (and the block sum and total
recomputed so that the forgery is internally consistent).  The tightest valid ``lo`` satisfies
``lo^4 * m^3 <= 10^40 < (lo+1)^4 * m^3``, so the raised entry makes the block's ``_fact`` a FALSE
``∀``-statement and ``decide +kernel`` fails on it (the final theorem then has no proof of its
hypothesis either).  Layer 1 would never mint it (``nat_root_bracket_table_certificate`` computes
the tightest brackets and re-checks them); the adapter edits the frozen dataclass BY HAND,
bypassing that, exactly as ``adapter_scaled_interval_eval`` does, so the kernel is the arbiter.

TRUE twin: the same table unmodified -- compiles clean and axiom-clean.  The two emitted texts
differ in exactly three lines (the forged list, its block sum, and the total in the final
statements).

The single face's ``U := L`` control (``2^(-1/2)`` at scale ``10^6`` with the upper endpoint
forged down to the lower one) is exercised Lean-gated in ``tests/test_emit_nat_root_bracket_table.py``.

Both twins elaborate over Mathlib alone: the ``NatRootBracket`` prelude is spliced in as the
adapter ``prelude`` (its body without the import line), so no island module is needed.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

from telperion.emit_nat_root_bracket_table import (
    NatRootBracketTableEmitter,
    nat_root_bracket_prelude_body,
    nat_root_bracket_table_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_P, _Q, _TERMS, _SCALE, _BLOCK = 3, 4, 40, 10 ** 10, 20
#: The forged position: block 1, entry 7 (m = 20 * 1 + 7 + 1 = 28).
_FORGED_BLOCK, _FORGED_INDEX = 1, 7


def make_true_cert():
    """The honest certificate (the tightest brackets, re-checked exactly)."""
    return nat_root_bracket_table_certificate(_P, _Q, _TERMS, scale=_SCALE, block=_BLOCK)


def make_false_cert():
    """The honest certificate with one ``lo`` entry raised by 1 (block sum and total updated)."""
    cert = make_true_cert()
    lo_blocks = [list(b) for b in cert.lo_blocks]
    lo_blocks[_FORGED_BLOCK][_FORGED_INDEX] += 1
    lo_sums = list(cert.lo_sums)
    lo_sums[_FORGED_BLOCK] += 1
    return replace(cert, lo_blocks=tuple(tuple(b) for b in lo_blocks), lo_sums=tuple(lo_sums),
                   lo_total=cert.lo_total + 1)


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        NatRootBracketTableEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="NatRootBracketTableEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=nat_root_bracket_prelude_body(),
        allow_axioms=(),
        label=(
            "one lo entry of the ∑_(i<40) (i+1)^(-3/4) table (two blocks of 20, scale 10^10) "
            "raised by 1: the block's ∀-fact lo^4 * m^3 <= 10^40 is false at m = 28 and "
            "decide +kernel rejects it; the unmodified twin compiles"
        ),
        imports_line="import Mathlib",
    )
)
