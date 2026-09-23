"""Negative-control adapter for PreorderingMultiplierEmitter (preordering with multiplier).

The emitted theorem for a constant-multiplier (`M = 1`) certificate on the Li disk is

    theorem nm (x y : R) (hz : x ^ 2 + y ^ 2 <= x) : 0 <= p := by
      obtain <d, hd0, hde> : exists d : R, 0 <= d /\\ d = x - x ^ 2 - y ^ 2 := <_, by linarith, rfl>
      obtain <B, hB0, hBe> : exists B : R, 0 <= B /\\ B = y ^ 2 := <_, by positivity, rfl>
      have key : p = <cone in d, B> := by
        rw [hde, hBe]
        ring
      rw [key]
      positivity

`ring` checks the identity and `positivity` folds the cone: it closes `0 <= cone` ONLY because
every certificate coefficient is nonnegative.  That sign is the load-bearing numeric content, and
the audit's headline refusal ("any `c_alpha < 0`", SHAPES_AUDIT_D_LI_FACE section 3.1).

FALSE forgery: `p = x - x^2 - 2 y^2 = d - B` on the disk `x^2 + y^2 <= x`, with the certificate
`{d: 1, B: -1}` -- the identity is EXACT (`ring` succeeds), but the coefficient on `B` is
negative.  The statement is FALSE, not merely unproved: at `(x, y) = (1/2, 1/2)` the hypothesis
reads `1/2 <= 1/2` (true, a point of the disk) and `p = 1/2 - 1/4 - 1/2 = -1/4 < 0`.  Layer 1
(`preordering_multiplier_certificate`) refuses the negative coefficient outright; the adapter
mints the frozen dataclass BY HAND, bypassing that guard exactly as `adapter_exp_threshold` does,
so the kernel is the arbiter: `positivity` cannot prove `0 <= d - B` and the proof does not
elaborate.

TRUE twin: `p = x - x^2 = d + B`, certificate `{d: 1, B: 1}` -- `0 <= x - x^2` on the disk
(`x - x^2 >= y^2 >= 0`), proved by the same frozen script; compiles clean and axiom-clean over
Mathlib alone (imports_line `import Mathlib`, empty prelude).

The twins share every tactic line; only the target's `y ^ 2` coefficient and the cone's sign on
`B` move.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_preordering_multiplier import (
    HYP,
    STRUCTURAL,
    Generator,
    PreorderingMultiplierCert,
    PreorderingMultiplierEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_X, _Y = sp.symbols("x y")
_GENERATORS = (
    Generator("d", sp.expand(_X - _X ** 2 - _Y ** 2), HYP, "hz",
              (sp.expand(_X ** 2 + _Y ** 2), _X)),
    Generator("B", _Y ** 2, STRUCTURAL, "", None),
)


def _cert(b_coeff) -> PreorderingMultiplierCert:
    b = sp.Integer(b_coeff)
    target = sp.expand((_X - _X ** 2 - _Y ** 2) + b * _Y ** 2)   # d + b B
    return PreorderingMultiplierCert(
        symbols=(_X, _Y), target=target, generators=_GENERATORS,
        mult_coeff=sp.Integer(1), mult_index=None, mult_power=0,
        terms=((sp.Integer(1), (1, 0)), (b, (0, 1))),
        locus=None, face=None,
        # the rendered header states this provenance verbatim: never "re-checked"
        found_by="hand-minted for the negative control (Layer 1 bypassed)",
    )


def make_false_cert() -> PreorderingMultiplierCert:
    """Hand-forged FALSE cert: `0 <= x - x^2 - 2 y^2` on the disk, 'certified' by the exact
    identity `p = d - B` with the NEGATIVE coefficient -1 on B (false at (1/2, 1/2))."""
    return _cert(-1)


def make_true_cert() -> PreorderingMultiplierCert:
    """Paired TRUE twin: `0 <= x - x^2` on the disk, by `p = d + B` (the honest instance)."""
    return _cert(1)


def _emit(cert: PreorderingMultiplierCert, name: str) -> str:
    return emit_via_single_instance_family(
        PreorderingMultiplierEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="PreorderingMultiplierEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged preordering certificate p = x - x^2 - 2 y^2 = d - B on the disk "
            "x^2 + y^2 <= x: the identity is exact but the coefficient on B is -1, the claim is "
            "FALSE at (1/2, 1/2) (p = -1/4), and the emitted positivity fold cannot prove "
            "0 <= d - B, so the kernel rejects it; the true twin p = d + B compiles"
        ),
        imports_line="import Mathlib",
    )
)
