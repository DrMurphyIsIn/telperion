"""Negative-control adapter for GapBudgetMultiplicityEmitter (tangent-price gap budgets).

The instance is the dogfood's ``maxprod_mod2``: parts with sum ``3t + 2`` and
``sum log k >= log 2 + t log 3`` (the classical optimum ``{2} + 3^t``).  The budget is
``theta = gamma(2) = 2/3 log 3 - log 2 = 0.03926...``, so the honest certificate proves
``count 1 = 0``, ``count 2 <= 1``, ``count 4 = 0`` and ``k < 5`` for every part.

FALSE forgery: the same certificate with the gap lower bound at ``k = 2`` raised to ``1/20``
(above the truth ``0.03926...`` and above ``theta_hi``), so the derived cap at 2 becomes 0 and
the main theorem claims ``count 2 = 0``.  That is FALSE, not merely unproved: the benchmark
``{2} + 3^t`` itself satisfies every hypothesis and has one 2.  The forged enclosure
``1/20 < 2/3 log 3 - log 2`` is false as well.  Layer 1 refuses it (the enclosure fold does not
imply the claimed bound: ``gap_lo={2: 1/20}`` raises); the adapter mints it BY HAND
(``dataclasses.replace``), so the kernel is the arbiter: the enclosure ``linarith`` cannot
reach ``1/20`` and the proof does not elaborate.

TRUE twin: the honest certificate (bound ``39261/1000000``, cap 1) -- compiles clean over
Mathlib alone.  Both twins share every tactic line except those quoting the forged literal
and the cap it moves.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

import sympy as sp

from telperion.emit_enclosure_tree import _emission_order
from telperion.emit_gap_budget_multiplicity import (
    GapBudgetCert,
    GapBudgetMultiplicityEmitter,
    K,
    _consequences,
    gap_budget_multiplicity_certificate,
    gb_log,
    gb_logk,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

T = sp.Symbol("t")
#: the forged lower bound on gamma(2) = 0.03926...
FORGED_G2 = sp.Rational(1, 20)


def spec() -> dict:
    return dict(atoms=(1, None), tail_start=5, w=gb_logk(), ell=K, tau=gb_log(3) / 3,
                params=(T,), M=3 * T + 2, bench=((2, 1), (3, T)))


def make_true_cert() -> GapBudgetCert:
    """The honest dogfood certificate `maxprod_mod2`."""
    return gap_budget_multiplicity_certificate(**spec())


def make_false_cert() -> GapBudgetCert:
    """Hand-forged FALSE cert: gamma(2) >= 1/20, hence `count 2 = 0` (the benchmark has one 2)."""
    honest = make_true_cert()
    atoms = []
    for a in honest.atoms:
        if a.k == 2:
            root = replace(a.enc.root, lo=FORGED_G2)
            enc = replace(a.enc, root=root, order=_emission_order(root))
            a = replace(a, g=FORGED_G2, enc=enc)
        atoms.append(a)
    atoms = tuple(atoms)
    caps, tail_cap, ks = _consequences(atoms, honest.theta_hi, honest.tail,
                                       honest.tail.anchor.g, True)
    return replace(honest, atoms=atoms, caps=caps, tail_cap=tail_cap, knapsack=ks)


def make_false_cert_cap() -> GapBudgetCert:
    """SECOND forgery, aimed at the cap step itself: every gap bound and theta_hi honest, only
    the derived cap at 2 miscomputed as 0 (the truth is floor(theta_hi / g_2) = 1).  The main
    theorem again claims the FALSE `count 2 = 0`; the kernel fails at `gapBudget_nat_cap 0`'s
    `norm_num` side condition `theta_hi < 1 * g_2`.  Exercised by a lean-gated test (the harness
    keys one adapter per emitter)."""
    honest = make_true_cert()
    caps = tuple((k, 0 if k == 2 else c) for k, c in honest.caps)
    return replace(honest, caps=caps)


def _emit(cert: GapBudgetCert, name: str) -> str:
    return emit_via_single_instance_family(
        GapBudgetMultiplicityEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="GapBudgetMultiplicityEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged gap bound gamma(2) >= 1/20 in the max-product N = 3t + 2 budget (truth "
            "0.03926...): the main theorem would claim count 2 = 0, refuted by the benchmark "
            "{2} + 3^t itself; the enclosure linarith cannot reach 1/20 and the kernel rejects "
            "it; the true twin (bound 39261/1000000, cap 1) compiles"
        ),
        imports_line="import Mathlib",
    )
)
