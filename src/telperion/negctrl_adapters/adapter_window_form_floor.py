"""Negative-control adapter for WindowFormFloorEmitter (Zhu's window-floor certificate).

An emitted instance concludes `WindowFloor L published` from `WindowFloor L raw` through
`windowFloor_of_le`, whose side goal is the rational inequality `published <= raw` with
`raw = min(lam0, beta* - epsD) - epsB`.  That goal is the load-bearing content: if it is FALSE,
`norm_num` fails and the TRUSTED Lean kernel rejects the proof.

FALSE forgery: a cert whose PUBLISHED constant is rounded UP rather than down -- `lam0 = 9e-18`,
`epsD = epsB = 1e-100`, so `raw` is just under `9e-18`, but the cert publishes `1e-17`.  Layer 1
(`window_form_floor_certificate`) refuses that with the "EXCEEDS the certified floor" guard; the
adapter mints the frozen dataclass BY HAND, bypassing it, so the kernel is the arbiter.  Rounding
UP is the forgery worth controlling for, because it silently overstates a published constant while
every other number in the certificate stays honest.

TRUE twin: Zhu's real `L = 0.8` certificate (Theorem 1.2) -- `T# = 200`, `A_L = 2.9419735`,
`beta* = 0.5134667`, `lam0 = 9e-18`, `epsD = epsB = 1e-100`, `N = 200`, published `8.9e-18`, which
is Zhu's own rounding.  Compiles clean.

THE SECOND, SHARPER CONTROL (certificate layer, not the kernel)
----------------------------------------------------------------
The kernel control above catches a corrupted LITERAL.  It cannot catch a corrupted CONSTANT, because
a wrong `A_L` still yields a true rational inequality downstream -- which is precisely how Zhu's own
earlier draft produced a support-2.38 claim it has since retracted (Remark 3.3, Section 15 item 4).
`make_retracted_cert` below is that forgery, reconstructed: at `L = 1.19` it declares the per-prime
constant `A_eff = 4.6948` in place of `A_L = 7.0750`.  With `A_eff` the apparent barrier threshold is
`2 pi e^{A_eff} = 687.2` rather than the true `T_1 = 7427`, so `T# = 1000` looks ample and
`beta* = 0.374078... > 0` looks healthy.  Every number is internally consistent and the emitted
`norm_num` goal is TRUE.  Only the emitter's re-derivation of `A_L` from `L` refuses it, and
`test_refuses_mismatched_comb_mass_the_retraction_guard` is the assertion that it does.

That is the honest division of labour: the kernel guards the arithmetic, the certificate layer
guards the constants, and the constants are where the published error actually happened.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_window_form_floor import (
    WindowFormFloorCert,
    WindowFormFloorData,
    WindowFormFloorEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_L08 = sp.Rational(4, 5)
_A_L08 = sp.Rational("2.9419735")
_BETA_08 = sp.Rational("0.5134667")


#: Stand-in vocabulary, so the control elaborates against PLAIN Mathlib with no island imports.
#: The island's real ``WindowFloor`` is an integral inequality over the Weil pairing (see
#: ``window_form_floor_prelude_lean``), but the ONLY load-bearing content of an emitted instance is
#: the ``norm_num`` side goal of ``windowFloor_of_le`` -- the claim that the PUBLISHED floor really
#: is below the certified one.  The stub keeps that lemma's shape exactly (a floor multiplying a
#: non-negative quantity) and is PROVED, not axiomatised, so both twins stay on mathlib's three
#: axioms and ``allow_axioms`` stays empty.  This tests the EMITTER's certificate arithmetic; the
#: real vocabulary is CI-compiled in the weil_form_enclosure island itself.
_STANDIN_PRELUDE = """
def WindowFloor (L lam : \u211d) : Prop := \u2200 m : \u211d, 0 \u2264 m \u2192 lam * m \u2264 L

theorem windowFloor_of_le {L lam mu : \u211d} (h : WindowFloor L lam) (hmu : mu \u2264 lam) :
    WindowFloor L mu :=
  fun m hm => le_trans (mul_le_mul_of_nonneg_right hmu hm) (h m hm)
"""


def make_false_cert():
    """Hand-forged FALSE cert: the PUBLISHED floor is rounded UP, not down.

    `lam0 = 9e-18` with `eps_b = 1e-100` certifies a raw floor just under `9e-18`, but this cert
    publishes `1e-17`, which is larger.  The emitted `norm_num` goal
    `1e-17 <= min(9e-18, beta* - 1e-100) - 1e-100` is FALSE.  `window_form_floor_certificate`
    refuses this (the "EXCEEDS the certified floor" guard); the adapter mints the frozen dataclass
    BY HAND, bypassing that guard, so the kernel is the arbiter.

    Rounding UP is the forgery worth controlling for, because it is the one that silently
    overstates a published constant while every other number in the certificate stays honest."""
    return WindowFormFloorCert(
        L=_L08, t_sharp=sp.Integer(200), comb_mass=_A_L08, beta_star=_BETA_08,
        lam0=sp.Rational("9e-18"), eps_d=sp.Rational("1e-100"), eps_b=sp.Rational("1e-100"),
        n_modes=200, published_floor=sp.Rational("1e-17"),
        label="forged_published_floor_rounded_up",
    )


def make_true_cert():
    """Paired TRUE twin: Zhu Theorem 1.2's actual certified run at L = 0.8, support 1.6."""
    return WindowFormFloorCert(
        L=_L08, t_sharp=sp.Integer(200), comb_mass=_A_L08, beta_star=_BETA_08,
        lam0=sp.Rational("9e-18"), eps_d=sp.Rational("1e-100"), eps_b=sp.Rational("1e-100"),
        n_modes=200, published_floor=sp.Rational("8.9e-18"), label="zhu_thm12_L08_T200",
    )


def make_retracted_data():
    """Zhu's OWN retracted support-2.38 forgery, reconstructed as emitter INPUT.

    Internally consistent, positive floor, true downstream inequality -- and refused, because
    `A_eff = 4.6948` is not the comb mass at `L = 1.19` (`A_L = 7.0750`).  This is the
    certificate-layer control; see the module docstring.
    """
    return WindowFormFloorData(
        L=sp.Rational("1.19"), t_sharp=sp.Integer(1000),
        comb_mass=sp.Rational("4.6948"),          # A_eff -- the retracted substitution
        beta_star=sp.Rational("0.374078212"),     # log(1000/2pi) - 1/1000 - A_eff: consistent
        lam0=sp.Rational("1e-46"), eps_d=sp.Rational("1e-100"), eps_b=sp.Rational("1e-100"),
        n_modes=2000, label="retracted_support_238_A_eff",
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        WindowFormFloorEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="WindowFormFloorEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=_STANDIN_PRELUDE,
        allow_axioms=(),
        label=(
            "forged Zhu window floor whose PUBLISHED constant 1e-17 is rounded UP past the "
            "certified floor min(9e-18, beta* - 1e-100) - 1e-100: the norm_num side goal of "
            "windowFloor_of_le is false, kernel rejects; true twin (Zhu Thm 1.2 at L = 0.8, "
            "T# = 200, lam0 = 9e-18, published 8.9e-18) compiles.  The sharper "
            "certificate-layer control is make_retracted_data: the paper's own withdrawn "
            "support-2.38 instance with A_eff = 4.6948 for A_L = 7.0750, internally consistent and "
            "refused only by the emitter's re-derivation of the comb mass"
        ),
        imports_line="import Mathlib",
    )
)
