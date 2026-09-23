"""Negative-control adapter for EnclosureTreeEmitter (rational enclosures of expression trees).

The emitted theorems for the dogfood `pi`-face instance (`LiLadderHeight`'s
`n <= 18848 -> (n + 1 : R) <= 3 * pi * 4000 / 2`) are

    theorem nm_n0 : (6283 / 2000 : R) < Real.pi /\\ Real.pi < (3927 / 1250 : R)   -- pi_gt_d4
    theorem nm    : (18849 : R) < 3 * Real.pi * 4000 / 2 /\\ ...                 -- linarith
    theorem nm_rate (n : N) (hn : n <= 18848) : (n + 1 : R) <= 3 * Real.pi * 4000 / 2

The load-bearing content is the ROOT's stated lower bound (and the cap it licenses): the root
proof is a `linarith` from `Real.pi_gt_d4` alone, so a lower bound the rung does not reach
cannot be proved.

FALSE forgery: the same certificate with the root lower bound moved to 18850 and the cap to
18849 -- one past the truth.  `6000 pi = 18849.5559...`, so `18850 < 3 * pi * 4000 / 2` is FALSE,
not merely unproved, and so is the rate statement at `n = 18849` (`18850 <= 18849.55...`).
Layer 1 (`enclosure_tree_certificate`) refuses it at every rung up to d20 ("rate cap ... is NOT
reached"); the adapter mints it BY HAND (`dataclasses.replace` on the honest root, emission order
recomputed), bypassing that guard exactly as `adapter_exp_enclosure` does, so the kernel is the
arbiter: the root `linarith` cannot get `18850 < 3 * Real.pi * 4000 / 2` out of
`6283 / 2000 < Real.pi`, and the proof does not elaborate.

TRUE twin: the honest certificate (root lower bound 18849, cap 18848, rung d4) -- compiles clean
and axiom-clean over Mathlib alone (imports_line `import Mathlib`, empty prelude).  It is
byte-for-byte the dogfood instance's emitted block.

Both twins share every tactic line; only the literals 18849 -> 18850, 18848 -> 18849 (and the
header comments that quote them) move.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

import sympy as sp

from telperion.emit_enclosure_tree import (
    EnclosureTreeCert,
    EnclosureTreeEmitter,
    _emission_order,
    enclosure_tree_certificate,
    node_div,
    node_mul,
    node_pi,
    node_rat,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

#: the LiLadderHeight side condition `3 * pi * 4000 / 2` (= 6000 pi), and its honest cap
_CAP = 18848


def _tree():
    return node_div(node_mul(node_mul(node_rat(3), node_pi()), node_rat(4000)), node_rat(2))


def make_true_cert() -> EnclosureTreeCert:
    """The honest dogfood certificate: rung d4, root lower bound 18849, cap 18848."""
    return enclosure_tree_certificate(_tree(), rate_cap=_CAP)


def make_false_cert() -> EnclosureTreeCert:
    """Hand-forged FALSE cert: the honest root with its lower bound moved to 18850 and the cap
    to 18849.  6000 pi = 18849.5559..., so the root enclosure and the rate statement at
    n = 18849 are both false; the emitted linarith cannot reach them."""
    honest = make_true_cert()
    root = replace(honest.root, lo=sp.Integer(_CAP + 2))
    return EnclosureTreeCert(root=root, order=_emission_order(root), rate_cap=_CAP + 1,
                             pi_digits=honest.pi_digits, order_level=honest.order_level)


def _emit(cert: EnclosureTreeCert, name: str) -> str:
    return emit_via_single_instance_family(
        EnclosureTreeEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="EnclosureTreeEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged pi-face enclosure 18850 < 3 * pi * 4000 / 2 with rate cap 18849 (one past "
            "the truth: 6000 pi = 18849.55...): the root linarith from Real.pi_gt_d4 cannot "
            "reach it and the kernel rejects it; the true twin (lower bound 18849, cap 18848, "
            "the LiLadderHeight instance) compiles"
        ),
        imports_line="import Mathlib",
    )
)
