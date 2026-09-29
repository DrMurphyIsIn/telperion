"""Negative-control adapter for MobiusTangentCellEmitter (tangent-line cells, Mobius term).

The TRUE twin is the logarithmic-mean bound `log x <= 2 (x - 1)/(x + 1)` on [1/4, 1/2] in
template form

    F(x) = -2 + 0 x + log(0 + 1 x) + 4 / (1 + 1 x) <= 0,

one cell, tangent point t = 7/16 (so the `log u <= H` split runs through `Real.log_two_gt_d9`,
u < 2/3), Mobius coefficient 4 > 0 (the convex endpoint lemma).  It compiles over Mathlib
alone.

FALSE forgery: the same certificate with the problem's constant moved from -2 to -19/10.
F(1/2) = log(1/2) - 2/3 + 1/10 = 0.0735... > 0, so the cell theorem, the union theorem and
the statement at x = 1/2 are FALSE, not merely unproved.  Layer 1
(`mobius_tangent_cell_certificate` / `check_cell`) refuses it: the recorded majorant constant
`m` no longer matches the recomputation, and no cell subdivision makes the majorant
nonpositive.  The adapter mints it BY HAND (`dataclasses.replace` on the honest problem, the
honest cells kept), so the kernel is the arbiter: the cell's closing `linarith` needs
`F <= m + k x + 4/(1 + x)`, which is off by exactly 1/10, and the proof does not elaborate.

Both twins share every tactic line; only the constant `(-2)` -> `(-19 / 10)` in the stated
`F` moves.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction

from telperion.emit_mobius_tangent_cell import (
    MobiusTangentCellCert,
    MobiusTangentCellEmitter,
    mobius_tangent_cell_certificate,
    mobius_tangent_problem,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

#: the forged constant (the honest one is -2)
FORGED_A = Fraction(-19, 10)


def _problem():
    return mobius_tangent_problem(a=-2, b=0, logs=[(1, 0, 1)], sigma=4, B=1, A=1,
                                  p="1/4", q="1/2")


def make_true_cert() -> MobiusTangentCellCert:
    """The honest certificate: one cell [1/4, 1/2], t = 7/16, convex Mobius mode."""
    return mobius_tangent_cell_certificate(_problem())


def make_false_cert() -> MobiusTangentCellCert:
    """Hand-forged FALSE cert: constant -2 -> -19/10 (F(1/2) = 0.0735... > 0), honest cells
    kept.  `check_cell` would refuse it; the kernel must too."""
    honest = make_true_cert()
    return MobiusTangentCellCert(replace(honest.problem, a=FORGED_A), honest.cells)


def _emit(cert: MobiusTangentCellCert, name: str) -> str:
    return emit_via_single_instance_family(
        MobiusTangentCellEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="MobiusTangentCellEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged log-mean cell with the constant raised -2 -> -19/10 (F(1/2) = 0.0735 > 0): "
            "the cell's closing linarith is off by 1/10 and the kernel rejects it; the true "
            "twin (log x <= 2 (x - 1)/(x + 1) on [1/4, 1/2], one convex cell) compiles"
        ),
        imports_line="import Mathlib",
    )
)
