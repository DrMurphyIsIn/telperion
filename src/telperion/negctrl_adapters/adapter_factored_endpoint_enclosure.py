"""Negative-control adapter for FactoredEndpointEnclosureEmitter (factorization + box sign
through a singular endpoint).

The instance is the sharp companion of the classical bound ``(1/l) log(1 + l) <= 1``:

    F(l) = l - log(1 + l) - c l^2 >= 0     on the closed box [0, 1/10] (endpoint l = 0),

certified with ``k = 2`` and the order-5 upper bound ``log(1 + u) <= u - u^2/2 + ... + u^5/5``:
``Q = l^2 (1/2 - c - l/3 + l^2/4 - l^3/5)``, so ``H = 1/2 - c - l/3 + l^2/4 - l^3/5``.  The
true minimum of ``(l - log(1 + l))/l^2`` on ``[0, 1/10]`` is ``0.468982...`` at ``l = 1/10``.

FALSE forgery: ``c = 47/100``, above the minimum by ``~1/1000``: ``F(1/10) < 0``, so the claim
is FALSE, not merely unproved.  Layer 1 (``factored_endpoint_certificate``) refuses it with a
located violation at ``l = 1/10``.  The adapter mints it with ``check=False`` and one box: the
factorization, the Taylor atom and the box are the honest ones, and ONLY the constant is
wrong, so ``H(1/10) < 0`` and the box lemma's ``linarith`` over the Bernstein products cannot
close ``0 <= H``.

TRUE twin: ``c = 117/250`` (below the minimum by ``~1/1000``), byte-for-byte the dogfood
instance ``log_sharp``.

A two-variable pair (``l (x - l)^2 + l^2 x - m l`` with ``m = 3/64 -+ 1/1000``) is exercised by
tests/test_negctrl_factored_endpoint_enclosure.py with the same harness.

conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_factored_endpoint_enclosure import (
    LOG_SHARP_FALSE_SPEC,
    LOG_SHARP_SPEC,
    SYNTH2_MARGIN_FALSE_SPEC,
    SYNTH2_MARGIN_SPEC,
    FactoredEndpointCert,
    FactoredEndpointEnclosureEmitter,
    factored_endpoint_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_true_cert() -> FactoredEndpointCert:
    """The honest certificate (c = 117/250)."""
    return factored_endpoint_certificate(**LOG_SHARP_SPEC)


def make_false_cert() -> FactoredEndpointCert:
    """Hand-forged FALSE cert: c = 47/100, one box, every Layer-1 sign check skipped."""
    return factored_endpoint_certificate(**LOG_SHARP_FALSE_SPEC, max_depth=0, check=False)


def make_true_2d_cert() -> FactoredEndpointCert:
    """The honest two-variable certificate (m = 3/64 - 1/1000)."""
    return factored_endpoint_certificate(**SYNTH2_MARGIN_SPEC)


def make_false_2d_cert() -> FactoredEndpointCert:
    """Hand-forged FALSE two-variable cert: m = 3/64 + 1/1000 (F < 0 at l = 1/8, x = 1/4)."""
    return factored_endpoint_certificate(**SYNTH2_MARGIN_FALSE_SPEC, max_depth=2, check=False)


def _emit(cert: FactoredEndpointCert, name: str) -> str:
    return emit_via_single_instance_family(
        FactoredEndpointEnclosureEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


ADAPTER = NegativeControlAdapter(
    emitter_name="FactoredEndpointEnclosureEmitter",
    make_false_cert=make_false_cert,
    make_true_cert=make_true_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "forged box claim l - log(1+l) >= (47/100) l^2 on [0, 1/10] (false by ~1/1000 at "
        "l = 1/10): the cofactor H = 1/2 - 47/100 - l/3 + l^2/4 - l^3/5 is negative at 1/10, "
        "so the box lemma's linarith over the Bernstein products cannot close 0 <= H and the "
        "kernel rejects it; the true twin with 117/250 compiles"
    ),
    imports_line="import Mathlib",
)

#: The two-variable control, run by the tests with the same harness (not registered: the
#: registry holds one adapter per emitter).
TWO_VAR_ADAPTER = NegativeControlAdapter(
    emitter_name="FactoredEndpointEnclosureEmitter",
    make_false_cert=make_false_2d_cert,
    make_true_cert=make_true_2d_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "forged two-variable box claim l (x - l)^2 + l^2 x >= (3/64 + 1/1000) l on "
        "[0, 1/2] x [1/4, 1] (false by 1/1000 at l = 1/8, x = 1/4): a box lemma 0 <= H "
        "cannot close; the true twin with 3/64 - 1/1000 compiles"
    ),
    imports_line="import Mathlib",
)

register(ADAPTER)
