"""Negative-control adapter for CurvatureBoundaryEmitter -- the kink-minimum route.

The instance is the example's headline kink: `f(x) = |x - 1/3| + x^2` on `[0, 1]`, with
pieces `L = 1/3 - x + x^2` on `[0, 1/3]` and `R = x - 1/3 + x^2` on `[1/3, 1]`.  `L' <= 0`
and `R' >= 0` are certified by Bernstein cells, so the minimum over `[0, 1]` is
`f(1/3) = 1/9` (stated as `IsLeast (f '' Icc 0 1) (1/9)`, the pointwise bound, and the
same for the closed form).

FALSE forgery: the claimed minimum is raised by 1/1000, to `1/9 + 1/1000 = 1009/9000`.
The statement `1009/9000 <= f x` is FALSE (at `x = 1/3`, `f = 1/9`).  Layer 1
(`kink_minimum_certificate`) refuses it ("claimed minimum ... but f(1/3) = 1/9"); the
adapter mints it with ``check=False``, so the forged file differs from the true twin only
in the claimed value.  The kernel is the arbiter: `<name>_value : f (1/3) = 1009/9000`
leaves `norm_num` with `False`, and every theorem built on it fails.

TRUE twin: the honest certificate (value 1/9), byte-for-byte the example's block.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_curvature_boundary import (
    CurvatureBoundaryEmitter,
    KinkMinimumCertificate,
    kink_minimum_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

#: the example's headline kink instance
KINK_SPEC = dict(left="1/3 - x + x**2", right="x - 1/3 + x**2", kappa=sp.Rational(1, 3),
                 a=0, b=1, f_expr="Abs(x - 1/3) + x**2")

#: the forged minimum: the true value 1/9 raised by 1/1000
FORGED_VALUE = sp.Rational(1, 9) + sp.Rational(1, 1000)


def make_true_cert() -> KinkMinimumCertificate:
    """The honest kink certificate (minimum 1/9 at 1/3)."""
    return kink_minimum_certificate(**KINK_SPEC, value=sp.Rational(1, 9))


def make_false_cert() -> KinkMinimumCertificate:
    """Hand-forged FALSE cert: the claimed minimum is 1/9 + 1/1000, built with every Layer-1
    check skipped."""
    return kink_minimum_certificate(**KINK_SPEC, value=FORGED_VALUE, check=False)


def _emit(cert: KinkMinimumCertificate, name: str) -> str:
    return emit_via_single_instance_family(
        CurvatureBoundaryEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="CurvatureBoundaryEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged kink minimum min_[0,1] (|x - 1/3| + x^2) = 1/9 + 1/1000 (false: the "
            "minimum is 1/9 at x = 1/3): the kink-value norm_num reduces to False and the "
            "kernel rejects it; the true twin with value 1/9 compiles"
        ),
        imports_line="import Mathlib",
    )
)
