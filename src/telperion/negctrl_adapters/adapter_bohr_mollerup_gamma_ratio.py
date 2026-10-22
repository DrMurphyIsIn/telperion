"""Negative-control adapter for BohrMollerupGammaRatioEmitter (kernel-decided Gamma-ratio enclosure).

Every instance states ``LO <= Real.Gamma x1 / Real.Gamma x2 <= HI`` and proves it from six ``Nat``
facts the kernel decides: four root brackets (``l1^q a^p <= b^p S^q`` behind ``_hA``, and so on) and
two comparisons against the kernel-computed products ``gA gB`` (``LOn u2 gB <= LOd n l1 gA`` is
``key_lo``).  The load-bearing content is the four bracket integers and the two comparisons: the
WITNESS.  The stance is CERTIFICATE_SENSITIVE, so the registered control forges the witness with
the statement unchanged.

REGISTERED CONTROL, a WITNESS forgery: the honest ``Gamma(3/8) / Gamma(7/8)`` certificate at
``n = 200`` with ``l1`` raised by one (``36420658219 -> 36420658220``), both claims unchanged.
``l1`` is the LARGEST ``L`` with ``L^8 (8n+3)^5 <= 8^5 S^8``, so ``l1 + 1`` violates it:
``decide +kernel`` in ``_hA`` reports the proposition false, ``lean`` exits 1, and the final theorem
(added anyway by Lean's error recovery) carries ``sorryAx``.  ``key_lo`` stays TRUE (a larger ``l1``
only makes its right-hand side larger), so the rejection is the bracket's and nothing else's.
Layer 1 never mints this certificate (``l1`` is computed, not supplied; its exactness is asserted);
the adapter edits the frozen dataclass BY HAND, bypassing that, exactly as
``adapter_scaled_interval_eval`` does, so the kernel is the arbiter.

SECOND CONTROL, a CLAIM forgery (exported for the tests, not registered: the harness keys adapters
by emitter): ``LO`` replaced by the certified upper decimal ``HI``.  ``HI`` is at or above the
certified upper bound, hence strictly above the true value ``2.17540591...``, so the forged
statement is a FALSE theorem; ``LO <= lo`` fails exactly, so ``key_lo`` is a false ``Nat``
inequality.  Layer 1 refuses this one (``bohr_mollerup_gamma_ratio_certificate`` raises).

TRUE twin: the same certificate unmodified -- compiles clean and axiom-clean.  The witness twins
differ only in the lines that carry ``l1`` (``key_lo``; ``_hA`` and its transport call; ``_aux``'s
``key_lo`` hypothesis, its ``hkey1`` and the calc step that uses ``l1``); the claim twins only in
the lines that carry the lower claim.

Both renderings set ``decide_rec_depth`` (``set_option maxRecDepth 10000 in`` on the six decide
lemmas): the proofs do not need it, but a FAILING ``key_lo`` formats its message under the default
depth and runs out while doing so (the claim forgery's message then reads "maximum recursion depth
has been reached" instead of "Tactic `decide` proved that the proposition ... is false"; the
witness forgery's root-bracket message is readable either way); the option makes the recorded
rejection readable.  Both twins elaborate over Mathlib alone: the
``BohrMollerupPrelude`` is spliced in as the adapter ``prelude`` (its body without the import
line), so no island module is needed.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

from telperion.emit_bohr_mollerup_gamma_ratio import (
    BohrMollerupGammaRatioEmitter,
    bohr_mollerup_gamma_ratio_certificate,
    bohr_mollerup_prelude_body,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_X1, _X2, _N = "3/8", "7/8", 200
#: maxRecDepth for the six decide lemmas of both twins (see the module docstring).
REC_DEPTH = 10000


def make_true_cert():
    """The honest certificate (claims = the certified bounds rounded outward)."""
    return bohr_mollerup_gamma_ratio_certificate(_X1, _X2, _N)


def make_false_cert():
    """The honest certificate with the witness integer ``l1`` raised by one (claims unchanged)."""
    cert = make_true_cert()
    return replace(cert, l1=cert.l1 + 1)


def make_false_claim_cert():
    """The honest certificate with LO forged to HI (above the true value); the second control."""
    cert = make_true_cert()
    return replace(cert, claim_lo=cert.claim_hi)


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        BohrMollerupGammaRatioEmitter(decide_rec_depth=REC_DEPTH),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="BohrMollerupGammaRatioEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=bohr_mollerup_prelude_body(),
        allow_axioms=(),
        label=(
            "witness forgery: l1 of the Gamma(3/8)/Gamma(7/8) certificate at n = 200 raised by one "
            "(36420658219 -> 36420658220) with the claims unchanged; the root inequality behind _hA "
            "is a false Nat fact, decide +kernel reports it and lean exits 1; the unmodified twin "
            "compiles"
        ),
        imports_line="import Mathlib",
    )
)
