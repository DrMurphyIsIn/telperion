"""Negative-control adapter for ComplexReImSplitEmitter (real/imaginary-part splits).

The emitted theorem is `(p : C).re = P` (or the `im` / `norm_sq` / `norm_exp` / cast faces),
proved by the frozen skeleton `simp only [Complex.add_re, Complex.mul_re, ..., Complex.I_re,
Complex.I_im, pow_succ, pow_zero, one_mul]` then `all_goals ring`: `simp only` rewrites the
left-hand side into a real polynomial in the parameters and `ring` must close the identity
against the CLAIMED polynomial `P`.  The load-bearing content is therefore exactly the claim:
a `P` that is not ring-equal to the true split leaves `ring` a false identity, the proof does
not close, and the TRUSTED Lean kernel rejects the file.  (The cast face's `push_cast` then
`all_goals ring` fails the same way on a corrupted claim: `make_false_cast_cert` below is its
hand-minted forgery, pinned offline by `tests/test_negctrl_complex_re_im_split.py`; the
registered control is the `re` forgery, the B N3 forge case the audit names.)

FALSE forgery: `Re ((a + b i)^2) = a^2 + b^2`.  The true real part is `a^2 - b^2`
(`E6Bridge28.re_pow_two`), so the forged claim is not merely unproved, it is FALSE (at
`a = 0, b = 1` it reads `-1 = 1`).  Layer 1 (`complex_re_im_split_certificate`) refuses it
(claim - target = 2 b^2 != 0); the adapter mints the frozen dataclass BY HAND, bypassing that
guard exactly as `adapter_exp_enclosure` does, so the kernel is the arbiter.

TRUE twin: the same expression, mode and binders with the honest claim `a^2 - b^2` -- the
`re_pow_two` statement of the Li face verbatim -- compiles clean and axiom-clean.

Both twins are plain statements over Mathlib alone (imports_line `import Mathlib`, empty
prelude), so the control needs no island definitions.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_complex_re_im_split import (
    IM_SYM,
    RE_SYM,
    ComplexReImSplitCert,
    ComplexReImSplitEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_A, _B = sp.symbols("a b", real=True)
_P = (_A + _B * sp.I) ** 2
_P_RE = sp.expand(_A ** 2 - _B ** 2)
_P_IM = sp.expand(2 * _A * _B)


def make_false_cert():
    """Hand-forged FALSE cert: the claim `a^2 + b^2` differs from the true real part
    `a^2 - b^2` by `2 b^2`, so `ring` cannot close the emitted identity."""
    return ComplexReImSplitCert(
        p=_P, z=None, params=(_A, _B), re_sym=RE_SYM, im_sym=IM_SYM, mode="re",
        claim=sp.expand(_A ** 2 + _B ** 2), p_re=_P_RE, p_im=_P_IM,
    )


def make_true_cert():
    """Paired TRUE twin: the honest claim `a^2 - b^2` (E6Bridge28.re_pow_two verbatim)."""
    return ComplexReImSplitCert(
        p=_P, z=None, params=(_A, _B), re_sym=RE_SYM, im_sym=IM_SYM, mode="re",
        claim=_P_RE, p_re=_P_RE, p_im=_P_IM,
    )


_M = sp.Symbol("m", integer=True, nonnegative=True)
_U = sp.Symbol("u", real=True)


def make_false_cast_cert():
    """The cast face's FALSE forgery (B D7 shape, E6Bridge5's `hcast`): `(m : C) * (u : C)^2 =
    (((m : R) * u^2 + 1 : R) : C)`, off by 1 everywhere; `push_cast; ring` cannot close it."""
    return ComplexReImSplitCert(
        p=_M * _U ** 2, z=None, params=(_M, _U), re_sym=RE_SYM, im_sym=IM_SYM, mode="cast",
        claim=_M * _U ** 2 + 1, p_re=_M * _U ** 2, p_im=sp.Integer(0), nat_params=(_M,),
    )


def make_true_cast_cert():
    """Paired TRUE twin of the cast forgery: E6Bridge5's `hcast` over the atoms `m`, `u`."""
    return ComplexReImSplitCert(
        p=_M * _U ** 2, z=None, params=(_M, _U), re_sym=RE_SYM, im_sym=IM_SYM, mode="cast",
        claim=_M * _U ** 2, p_re=_M * _U ** 2, p_im=sp.Integer(0), nat_params=(_M,),
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        ComplexReImSplitEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ComplexReImSplitEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged real-part split Re ((a + b i)^2) = a^2 + b^2 (the true value is a^2 - b^2, "
            "E6Bridge28.re_pow_two): simp only reduces the left-hand side to a real polynomial "
            "and ring cannot close the false identity, so the kernel rejects it; the true twin "
            "with claim a^2 - b^2 compiles"
        ),
        imports_line="import Mathlib",
    )
)
