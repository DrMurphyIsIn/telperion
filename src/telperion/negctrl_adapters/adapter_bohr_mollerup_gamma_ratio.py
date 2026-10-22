"""Negative-control adapter for BohrMollerupGammaRatioEmitter (kernel-decided Gamma-ratio enclosure).

Every instance states ``LO <= Real.Gamma x1 / Real.Gamma x2 <= HI`` and proves it from two ``Nat``
comparisons the kernel decides against the kernel-computed products ``gA gB``:
``LOn u2 gB <= LOd n l1 gA`` (``key_lo``) and ``HId u3 gA <= HIn n l4 gB`` (``key_hi``).  The
load-bearing content is therefore the claim and the four bracket integers.

FALSE forgery: the honest certificate of ``Gamma(3/8) / Gamma(7/8)`` at ``n = 200`` with ``LO``
replaced by the certified upper decimal ``HI``.  ``HI`` is at or above the certified upper
bound, hence strictly above the true value ``2.17540591...``, so the forged statement is a FALSE
theorem; and ``LO <= lo`` fails exactly, so ``key_lo`` is a false ``Nat`` inequality and
``decide +kernel`` fails.  Layer 1 refuses this certificate (``bohr_mollerup_gamma_ratio_certificate``
raises); the adapter edits the frozen dataclass BY HAND, bypassing that, exactly as
``adapter_scaled_interval_eval`` does, so the kernel is the arbiter.

TRUE twin: the same certificate unmodified -- compiles clean and axiom-clean.  The two emitted
texts differ only in the lines that carry the lower claim (the statement, ``key_lo``, ``_aux``
and its ``hkey1``/calc head, the docstrings).

Both twins elaborate over Mathlib alone: the ``BohrMollerupPrelude`` is spliced in as the
adapter ``prelude`` (its body without the import line), so no island module is needed.

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


def make_true_cert():
    """The honest certificate (claims = the certified bounds rounded outward)."""
    return bohr_mollerup_gamma_ratio_certificate(_X1, _X2, _N)


def make_false_cert():
    """The honest certificate with LO forged to HI (above the true value)."""
    cert = make_true_cert()
    return replace(cert, claim_lo=cert.claim_hi)


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        BohrMollerupGammaRatioEmitter(),
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
            "LO of the Gamma(3/8)/Gamma(7/8) enclosure at n = 200 forged to the certified upper "
            "decimal HI (above the true value 2.1754...): key_lo is a false Nat inequality and "
            "decide +kernel fails; the unmodified twin compiles"
        ),
        imports_line="import Mathlib",
    )
)
