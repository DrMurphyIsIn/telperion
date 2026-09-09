"""Negative-control adapter for TwoMomentCountEmitter — the Davenport–Heilbronn
over-claim control (HermitianMomentInertia family, zeta-23-lean §6).

The emitted theorem is an arithmetic implication in which the SAME κ feeds both
the moment hypothesis (``hfr : frGh ≤ κ·N + R2``) and the concluded proportion
constant (``2 − κ``).  Because ``emit_body`` renders both occurrences from one
payload field, NO payload forgery can make the statement false — the implication
holds for every κ (that is exactly the emitter's STRUCTURALLY_NONVACUOUS
stance).  The meaningful falsification lives one level up, and it is precisely
the Davenport–Heilbronn lesson: DH's function satisfies the same two-moment
structure as ζ yet has off-line zeros, so *claiming a better on-line proportion
than the moments support* is false.

FALSE forgery (statement-level, like adapter_c_g_round): take the emitter's own
rendering of the honest λ = 1, c = 2 certificate (κ = 4/3, constant 2 − κ = 2/3)
and inflate ONLY the concluded constant to ``1`` ("all zeros counted") — the
hypotheses stay byte-identical.  The forged implication is genuinely false
(N = 3, trGh = 3, frGh = 4, errors = 0 satisfy the hypotheses with count = 2,
while ``1·3 ≤ 2`` fails), so ``nlinarith`` cannot close it and the kernel
rejects.  The surgical replacement is asserted to hit exactly once, so template
drift in ``emit_body`` breaks this adapter loudly instead of silently testing a
stale string.

TRUE twin: the identical untouched rendering (one substring different), which
compiles clean.

``RankTraceScalarEmitter`` (the family's other member) stays not_applicable:
``2c·x − c² ≤ x²`` is identity-plus-square for every c — there is no payload or
constant whose corruption yields a false statement in the emitter's shape.

conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_hermitian_moment import (
    TwoMomentCountEmitter,
    two_moment_count_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# The honest headline certificate: λ = 1, c = 2 → κ = 4/3, H = 2 − κ = 2/3.
_HONEST = "honest"
_DH_OVERCLAIM = "dh_overclaim"

# The emitter renders the concluded proportion term as "(2 - {rat_lean(κ)}) * N";
# at κ = 4/3 rat_lean gives "(4 / 3)", so the substring is below.  The DH
# forgery inflates it to 1·N.
_HONEST_CONSTANT = "(2 - (4 / 3)) * N"
_FORGED_CONSTANT = "1 * N"


def make_false_cert():
    """The DH over-claim marker: same certificate, inflated concluded constant."""
    return (_DH_OVERCLAIM, two_moment_count_certificate(1, c=2))


def make_true_cert():
    """The untouched honest twin (λ = 1, c = 2)."""
    return (_HONEST, two_moment_count_certificate(1, c=2))


def _emit(cert, name: str) -> str:
    mode, payload = cert
    txt = emit_via_single_instance_family(
        TwoMomentCountEmitter(),
        lean_name=name,
        instance_kwargs={"payload": payload},
    )
    if mode == _HONEST:
        return txt
    assert mode == _DH_OVERCLAIM, mode
    # Statement-level forgery: inflate ONLY the concluded proportion constant.
    # Exactly-once assertion: the hypothesis side never contains this substring
    # (h0 has no proportion term; the sqrt argument is "(4/3 * N + R2)").
    n_hits = txt.count(_HONEST_CONSTANT)
    assert n_hits == 1, (
        f"template drift: expected exactly one {_HONEST_CONSTANT!r} in the "
        f"rendered theorem, found {n_hits} — update the adapter alongside "
        f"TwoMomentCountEmitter.emit_body"
    )
    return txt.replace(_HONEST_CONSTANT, _FORGED_CONSTANT)


register(
    NegativeControlAdapter(
        emitter_name="TwoMomentCountEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Davenport-Heilbronn over-claim: concluded on-line proportion "
            "inflated from 2 - kappa = 2/3 to 1 with hypotheses untouched "
            "(counterexample N=3, trGh=3, frGh=4, errors=0, count=2)"
        ),
        imports_line="import Mathlib",
    )
)
