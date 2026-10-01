"""Negative-control adapter for AnchoredMonotoneExtensionEmitter (anchored monotone extension).

The instance is the hard-core (independent-set) recursion on rooted trees, product mode:

    Z_b = (prod_c Z_c) (1 + lam P),   q_b = 1 / (1 + lam P),   P = prod_c q_c,

with the auxiliary row mu = 1, kappa = -c (the root-deleted forest).

FALSE forgery: the TOO-SMALL normalizer psi = 1 + 3 lam/4 (rho = 1, budget
c = 3 lam/(4 + 3 lam)).  The claim Z_b(lam) <= (1 + 3 lam/4)^{n_b} is genuinely false: a single
vertex has Z = 1 + lam.  In the certificate it is the row-0 residual of the inductive step
that fails -- at the leaf point (A = 1, k = 0) it equals
-lam (3 lam + 4)(lam + 1)/4 < 0 -- so Layer 1 refuses (a located exact violation).
The adapter mints the certificate with ``check=False``: every other obligation is the honest
one, ONLY the residual cell carries a negative product-basis coefficient, and its ``linarith``
cannot close.  The kernel is the arbiter.

TRUE twin: the same recursion with the true normalizer psi = 1 + lam, byte-for-byte the
dogfood instance minus the sanity lemmas.

conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_anchored_monotone_extension import (
    HARDCORE_SPEC,
    HARDCORE_TOO_SMALL_SPEC,
    AnchoredMonotoneCert,
    AnchoredMonotoneExtensionEmitter,
    anchored_monotone_extension_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def _spec(spec: dict) -> dict:
    s = dict(spec)
    s.pop("sanity", None)
    return s


def make_true_cert() -> AnchoredMonotoneCert:
    """The honest certificate: hard-core recursion, normalizer (1 + lam)^n on [0, oo)."""
    return anchored_monotone_extension_certificate(**_spec(HARDCORE_SPEC))


def make_false_cert() -> AnchoredMonotoneCert:
    """Hand-forged FALSE cert: normalizer (1 + 3 lam/4)^n, every Layer-1 check skipped."""
    return anchored_monotone_extension_certificate(**_spec(HARDCORE_TOO_SMALL_SPEC), check=False)


def _emit(cert: AnchoredMonotoneCert, name: str) -> str:
    return emit_via_single_instance_family(
        AnchoredMonotoneExtensionEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


ADAPTER = NegativeControlAdapter(
    emitter_name="AnchoredMonotoneExtensionEmitter",
    make_false_cert=make_false_cert,
    make_true_cert=make_true_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "too-small normalizer (1 + 3 lam/4)^n for the hard-core recursion (false: one vertex "
        "has Z = 1 + lam): the row-0 residual of the inductive step is negative at the leaf "
        "point, its linarith over the product facts cannot close and the kernel rejects it; "
        "the true twin (1 + lam)^n compiles"
    ),
    imports_line="import Mathlib",
)

register(ADAPTER)
