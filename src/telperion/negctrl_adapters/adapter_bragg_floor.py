"""Negative-control adapter for BraggFloorEmitter (Route P Brick D3 diffraction rungs).

The rung theorem is a concrete rational inequality `floorHi ≤ braggLo − tailHi` discharged by
`norm_num`.  Its load-bearing content is exactly those three Arb-enclosed rational literals: if the
inequality is FALSE, `norm_num` fails and the TRUSTED Lean kernel rejects the proof.

FALSE forgery: a cert whose floor exceeds the net amplitude — `floorHi = 9/10`, `braggLo = 1/2`,
`tailHi = 1/100`, so `braggLo − tailHi = 49/100 < 9/10`.  Layer 1 (`bragg_floor_certificate`) refuses
a non-positive margin; the adapter mints the frozen dataclass BY HAND, bypassing that guard, so the
kernel is the arbiter: `norm_num : (9/10 : ℝ) ≤ 1/2 − 1/100` fails and the theorem is rejected.

TRUE twin: the n = 0 rung's genuine numbers (`floorHi ≈ 0.5541`, `braggLo ≈ 0.5689`, `tailHi ≈ 0.0079`
at cutoff 1000, margin ≈ +0.0069) — a real cleared rung, compiles clean.  Both twins are pure
`(· : ℝ)` rational inequalities, so the control elaborates against plain Mathlib with no upstream defs
(it tests the EMITTER's certificate arithmetic; the conditional companion seam is not in scope here
and is CI-compiled in the li_positivity example itself).

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_bragg_floor import BraggFloorCert, BraggFloorEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_false_cert():
    """Hand-forged FALSE cert: floorHi 9/10 exceeds braggLo−tailHi = 49/100 (margin −41/100 < 0;
    bragg_floor_certificate would refuse it)."""
    return BraggFloorCert(
        n=0, s0=sp.Rational(2, 1), cutoff=1000,
        bragg_lo=sp.Rational(1, 2), tail_hi=sp.Rational(1, 100),
        floor_hi=sp.Rational(9, 10),
    )


def make_true_cert():
    """Paired TRUE twin: the real n = 0 rung numbers (margin ≈ +0.0069 > 0), a genuine cleared rung."""
    return BraggFloorCert(
        n=0, s0=sp.Rational(2, 1), cutoff=1000,
        bragg_lo=sp.Rational("0.568958"), tail_hi=sp.Rational("0.007908"),
        floor_hi=sp.Rational("0.554120"),
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        BraggFloorEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="BraggFloorEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged Bragg rung with floorHi 9/10 ABOVE braggLo-tailHi 49/100: the norm_num "
            "inequality floorHi <= braggLo - tailHi is false, kernel rejects; true twin "
            "(floorHi 0.554120, braggLo 0.568958, tailHi 0.007908, margin ~+0.0069) compiles"
        ),
        imports_line="import Mathlib",
    )
)
