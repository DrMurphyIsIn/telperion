"""Tests for the `window_form_floor` emitter -- Zhu's one-stroke window reduction as a certificate.

The emitter carries the certificate shape of Xuefeng Zhu, arXiv:2608.24827, Theorem 1.1: a finite,
Arb-certified least-eigenvalue floor `lam0` for the leading Legendre block of the reduced form `R`,
lifted to a floor on the Weil form over the WHOLE window `supp f subset [-L, L]` by the two-block
bound (eq. 13) with explicitly bounded tail constants `epsD`, `epsB`.

Three layers, in the order the emitter is meant to be trusted:

1. REFUSALS -- the anti-phantom face.  In particular the RETRACTION GUARD: the emitter re-derives
   `A_L` from `L` by exact von Mangoldt summation and `beta*` from `(T#, A_L)`, and refuses any
   instance whose declared constants disagree.  That is the check that catches the paper's own
   retracted support-2.38 claim, which substituted the per-prime constant `A_eff = 4.6948` for
   `A_L = 7.0750` at `L = 1.19` (Zhu Remark 3.3, Section 15 item 4).
2. RE-DERIVATION -- the finite constants reproduce the paper's printed values exactly.
3. EMISSION -- the emitted Lean proves only the finite rational inequality
   `0 < min(lam0, beta* - epsD) - epsB`; the passage to a window floor runs through NAMED,
   UNDISCHARGED analytic hypotheses (Zhu eq. 2, Lemma 3.1, eqs. 6 and 12).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion.emit_window_form_floor import (  # noqa: E402
    WindowFormFloorCert,
    WindowFormFloorData,
    WindowFormFloorEmitter,
    certify_window_form_floor_point,
    comb_mass,
    window_form_floor_certificate,
    window_form_floor_family,
    window_form_floor_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402

# ---------------------------------------------------------------------------------------
# Zhu's certified run at L = 0.8 (Section 5.1, 5.3, 5.4).  Rationals, since the certificate
# layer is exact; the values are the paper's printed ones, truncated DOWNWARD for lower
# bounds and UPWARD for upper bounds so the instance stays sound.
# ---------------------------------------------------------------------------------------
_L08 = sp.Rational(4, 5)
_T_SHARP = sp.Integer(200)
_A_L08 = sp.Rational("2.9419735")          # Zhu Section 5.1
_BETA_08 = sp.Rational("0.5134667")        # log(200/2pi) - 1/200 - A_L
_LAM0_08 = sp.Rational("9e-18")            # certified block floor, Section 5.4
_EPS_D = sp.Rational("1e-100")             # Section 5.3
_EPS_B = sp.Rational("1e-100")             # Section 5.3
_N_08 = 200                                # even Legendre modes 0, 2, ..., 398


def _data(**kw):
    base = dict(
        L=_L08,
        t_sharp=_T_SHARP,
        comb_mass=_A_L08,
        beta_star=_BETA_08,
        lam0=_LAM0_08,
        eps_d=_EPS_D,
        eps_b=_EPS_B,
        n_modes=_N_08,
        label="zhu_L08_T200",
    )
    base.update(kw)
    return WindowFormFloorData(**base)


# =======================================================================================
# 1. Re-derivation of the finite constants (Zhu Sections 3, 5.1 and Remark 3.3)
# =======================================================================================


def test_comb_mass_at_L08_is_three_terms():
    """A_L at L = 0.8 sums log n < 1.6, i.e. n = 2, 3, 4 -- exactly three von Mangoldt terms."""
    terms = comb_mass(sp.Rational(4, 5), terms=True)
    assert [n for n, _ in terms] == [2, 3, 4]


def test_comb_mass_reproduces_paper_value_at_L08():
    """Zhu Section 5.1 prints A_L = 2.9419735... at L = 0.8."""
    val = float(comb_mass(sp.Rational(4, 5)))
    assert abs(val - 2.9419735) < 5e-8


@pytest.mark.parametrize(
    "L, expected",
    [
        ("0.8", 2.9420), ("1.0", 5.8525), ("1.19", 7.0750),
        ("1.2", 8.5210), ("1.4", 10.290), ("1.6", 14.323), ("2.0", 24.383),
    ],
)
def test_comb_mass_reproduces_the_whole_threshold_table(L, expected):
    """Every row of Zhu's Remark 3.3 threshold table, recomputed from the definition."""
    assert abs(float(comb_mass(sp.Rational(L))) - expected) < 1e-3


def test_comb_mass_uses_strict_inequality_log_n_lt_2L():
    """The definition is `log n < 2L`, strict.  At 2L = log 4 exactly, n = 4 must be EXCLUDED."""
    import math
    L_edge = sp.Rational(math.log(4) / 2).limit_denominator(10 ** 12)
    terms = comb_mass(L_edge, terms=True)
    assert 4 not in [n for n, _ in terms]


# =======================================================================================
# 2. Refusals -- the anti-phantom face
# =======================================================================================


def test_accepts_the_real_zhu_certificate():
    """The genuine L = 0.8 instance certifies, with the paper's floor."""
    cert = window_form_floor_certificate(_data())
    assert cert.floor > 0
    # min(lam0, beta - epsD) - epsB = lam0 - epsB, since lam0 = 9e-18 << beta ~ 0.513
    assert cert.floor == _LAM0_08 - _EPS_B
    assert float(cert.floor) == pytest.approx(9e-18, rel=1e-6)


def test_refuses_mismatched_comb_mass_the_retraction_guard():
    """THE RETRACTION GUARD.  Zhu's own withdrawn support-2.38 claim substituted the per-prime
    constant A_eff = 4.6948 for A_L = 7.0750 at L = 1.19 (Remark 3.3).  A_eff bounds the comb from
    BELOW, hence the symbol from ABOVE, and the envelope needs an upper bound for the comb.

    The forged instance below is INTERNALLY CONSISTENT and passes every other guard: with
    A_eff = 4.6948 the apparent threshold is 2 pi e^{A_eff} = 687.2, so T# = 1000 clears it and
    beta* = 0.374078... > 0.  The true constant A_L = 7.0750 gives beta* = -2.006 < 0, so the
    certificate is worthless.  Only re-derivation of A_L from L catches this."""
    with pytest.raises(ValueError, match="comb mass"):
        window_form_floor_certificate(
            _data(
                L=sp.Rational("1.19"),
                t_sharp=sp.Integer(1000),
                comb_mass=sp.Rational("4.6948"),        # A_eff -- the retracted substitution
                beta_star=sp.Rational("0.374078212"),   # log(1000/2pi) - 1/1000 - A_eff: consistent
                n_modes=2000,                           # 2N = 4000 >= e*1.19*1000/2 = 1617.4
            )
        )


def test_refuses_mismatched_beta_star():
    """beta* is re-derived from (T#, A_L), never trusted."""
    with pytest.raises(ValueError, match="beta"):
        window_form_floor_certificate(_data(beta_star=sp.Rational("0.9")))


def test_refuses_nonpositive_beta_star():
    """beta* > 0 is Theorem 1.1's hypothesis; it is exactly what forces T# > T_1 = 2 pi e^{A_L}.
    At L = 0.8, T_1 = 119.09, so T# = 50 gives beta* = -0.8878275862 < 0."""
    with pytest.raises(ValueError, match="beta"):
        window_form_floor_certificate(
            _data(t_sharp=sp.Integer(50), beta_star=sp.Rational("-0.8878275862"))
        )


def test_refuses_t_sharp_below_the_barrier_threshold():
    """T# must exceed T_1 = 2 pi e^{A_L} (Zhu Thm 1.4).  At L = 0.8, T_1 = 119.086, so T# = 100
    is below it and beta* = -0.1846804056 <= 0.  The refusal names T_1 so the barrier is visible
    in the failure text, not just the arithmetic."""
    with pytest.raises(ValueError, match="T_1"):
        window_form_floor_certificate(
            _data(t_sharp=sp.Integer(100), beta_star=sp.Rational("-0.1846804056"))
        )


def test_refuses_nonpositive_floor():
    """If min(lam0, beta - epsD) - epsB <= 0 nothing is implied, so nothing is emitted."""
    with pytest.raises(ValueError, match="floor"):
        window_form_floor_certificate(_data(lam0=sp.Rational("1e-101")))


def test_refuses_nonpositive_lam0():
    with pytest.raises(ValueError, match="lam0"):
        window_form_floor_certificate(_data(lam0=sp.Integer(0)))


def test_refuses_negative_tail_constants():
    with pytest.raises(ValueError, match="eps"):
        window_form_floor_certificate(_data(eps_d=sp.Rational(-1, 10)))
    with pytest.raises(ValueError, match="eps"):
        window_form_floor_certificate(_data(eps_b=sp.Rational(-1, 10)))


def test_refuses_cut_order_below_the_localization_bound():
    """Theorem 1.1 needs the first discarded order 2N >~ e L T# / 2, else the Legendre
    localization does not apply and the tail constants are not the ones bounded in the proof."""
    with pytest.raises(ValueError, match="cut order|n_modes"):
        window_form_floor_certificate(_data(n_modes=10))


def test_refuses_nonpositive_L():
    with pytest.raises(ValueError, match="L"):
        window_form_floor_certificate(_data(L=sp.Integer(0)))


# =======================================================================================
# 3. Emission -- named hypotheses, finite conclusion
# =======================================================================================


def _emit_one():
    fam = window_form_floor_family(
        "WindowFormFloorInstances",
        GridSpec([("case", [0])]),
        lambda pt: "zhu_window_floor_L08",
        spec=lambda pt: _data(),
    )
    from telperion import ValidationReport, certify, emit

    report = emit(
        certify(fam),
        LeanProfile(namespace=("WindowFormFloorInstances",),
                    imports=("Mathlib", "WindowFormFloorDefs")),
        [WindowFormFloorEmitter()],
        ValidationReport(checks=(("window_form_floor", True),)),
    )
    return next(iter(report.files.values()))


def test_emitted_lean_proves_only_the_finite_inequality():
    text = _emit_one()
    assert "theorem zhu_window_floor_L08" in text
    assert "norm_num" in text


def test_emitted_lean_carries_the_reduction_as_a_named_hypothesis():
    """The instance must ASSUME the reduction's output and prove only the rounding.

    The emitted theorem is sorry-free, so it bundles the whole undischarged chain into one
    hypothesis `hred` rather than pretending to derive it.  The four-way itemization of what
    `hred` contains lives in the registry node (status draft, statement only) and in the
    instance's comment, which must name all four."""
    text = _emit_one()
    assert "hred" in text
    assert "windowFloor_of_le" in text
    assert "sorry" not in text
    for inp in ("eq. (2)", "Lemma 3.1", "eqs. (6) and (12)", "block floor"):
        assert inp in text, f"instance comment does not name the undischarged input {inp}"


def test_emitted_lean_refuses_to_round_the_floor_upward():
    """The published floor may only round DOWN from the certified one."""
    with pytest.raises(ValueError, match="EXCEEDS"):
        window_form_floor_certificate(_data(published_floor=sp.Rational("1e-17")))


def test_published_floor_defaults_to_the_raw_certified_floor():
    cert = window_form_floor_certificate(_data())
    assert cert.published_floor == cert.floor


def test_zhu_published_floor_is_the_rounded_down_8_9e_minus_18():
    """Zhu Thm 1.2 publishes 8.9e-18 for a raw 9e-18 - (r+s) - epsB; the rounding must certify."""
    cert = window_form_floor_certificate(_data(published_floor=sp.Rational("8.9e-18")))
    assert cert.published_floor < cert.floor
    assert float(cert.published_floor) == pytest.approx(8.9e-18, rel=1e-9)


def test_emitted_lean_states_the_trust_seam_and_no_rh_claim():
    text = _emit_one()
    assert "conjecture1_proved = False" in text
    assert "Arb" in text or "mpmath" in text
    assert "2608.24827" in text


def test_emitted_lean_has_no_emoji():
    """House rule: no emoji in emitted Lean or Python.  Lean's own notation (forall, int, R, C,
    norm bars) is required and allowed; what is banned is pictographic codepoints."""
    import unicodedata

    text = _emit_one() + window_form_floor_prelude_lean()
    bad = [c for c in text
           if unicodedata.category(c) == "So" or 0x1F000 <= ord(c) <= 0x1FAFF
           or 0x2600 <= ord(c) <= 0x27BF]
    assert bad == [], f"emitted text contains pictographic codepoints: {bad}"


def test_certify_point_roundtrips():
    fam = window_form_floor_family(
        "F", GridSpec([("case", [0])]), lambda pt: "t", spec=lambda pt: _data()
    )
    inst, n = certify_window_form_floor_point(fam, {"case": 0}, "t")
    assert n == 1
    assert isinstance(inst.payload, WindowFormFloorCert)


# =======================================================================================
# 4. Registry wiring
# =======================================================================================


def test_emitter_is_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY

    assert "WindowFormFloorEmitter" in REGISTRY


def test_negative_control_adapter_is_registered():
    assert "WindowFormFloorEmitter" in registered_adapters()
