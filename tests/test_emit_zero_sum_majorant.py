"""zero_sum_majorant emitter -- a zero-supported family is summable through a finite ordinate
window plus the local-count tail `m(rho) C/(1 + |gamma_rho|^2)`.

The shape (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 2; audit C 3.1 merged with B N5): the
per-instance certificate is ONE strip inequality `N/D <= C/(1 + |gamma_rho|^2)` on
`|Im rho - a| >= h`, cleared to an EXACT nonnegative Bernstein / Polya combination that the
emitted Lean states as `key` and closes by `ring`; the majorant and `Summable` faces compose it
with the island atom `RvMBridgeXi.zeroBoundAt`; the `tail_envelope` mode carries the B N5
consumer face and the rate-splitting companion.

Acceptance is pinned on the dogfood sites (E6Bridge19 `zbound`, E6Bridge18 `polBound`,
E6Bridge15 `liBound`, E6Bridge12 `tail_bound_window`) with their exact certificates, every refusal
has its own test, and the emitted Lean is pinned by substring.  The Lean kernel is the arbiter
(`examples/rvm_bridge/lean/Probes/Dogfood_zero_sum_majorant.lean` compiles on the island); these
are the pre-CI self-checks.

conjecture1_proved = False.
"""
import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    ZeroSumMajorantEmitter,
    certify,
    emit,
    zero_sum_majorant_certificate,
    zero_sum_majorant_family,
    zsm_symbols,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_zero_sum_majorant import with_terms  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402
from telperion.workflow import WorkflowError  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_LEAN_DIR = _ROOT / "examples" / "rvm_bridge" / "lean"
_PRELUDE_XI = _LEAN_DIR / "RvMBridgeXi.lean"
_DOGFOOD_GEN = _ROOT / "examples" / "rvm_bridge" / "dogfood_zero_sum_majorant.py"
_DOGFOOD_LEAN = _LEAN_DIR / "Probes" / "Dogfood_zero_sum_majorant.lean"

# the dogfood sites, as the audit cites them
_ZBOUND = dict(centre=0, h=1, c_far="9/4", num=1, den_kind="normSq", prefactor=True)
_POLBOUND = dict(params=[("a", "s.im")], binders=[("s", "ℂ")], centre="a", h=1,
                 c_far="13/4 + 2*a^2", num=1, den_kind="ordinate_sq")
_LIBOUND = dict(_ZBOUND)
# E6Bridge22 lcTerm: m/(1 + (Im rho - a)^2), far constant 13/4 + 2 a^2, h = 0 (empty window)
_LCTERM = dict(params=[("a", "a")], binders=[("a", "ℝ")], centre="a", h=0,
               c_far="13/4 + 2*a^2", num=1, den_kind="one_plus_ordinate_sq")
_TAIL = dict(mode="tail_envelope", envelope_E="symbolic", rate_P="-1/4")

X, W, _ = zsm_symbols()


def _fam(spec, name="t_inst", fam_name="ZeroSumMajorantTest"):
    return zero_sum_majorant_family(fam_name, GridSpec([("i", [0])]), lambda pt: name,
                                    spec=lambda pt: dict(spec))


def _emit_text(spec, name="t_inst"):
    report = emit(
        certify(_fam(spec, name)),
        LeanProfile(namespace=("ZeroSumMajorantTest",), imports=("RvMBridgeXi",)),
        [ZeroSumMajorantEmitter()],
        ValidationReport(checks=(("zero_sum_majorant", True),)),
    )
    return next(iter(report.files.values()))


def _refused(match=None, **spec):
    with pytest.raises(ValueError, match="zero_sum_majorant REFUSED") as ei:
        zero_sum_majorant_certificate(**spec)
    if match is not None:
        assert match in str(ei.value), str(ei.value)
    return str(ei.value)


# --- registry wiring --------------------------------------------------------

def test_kind_is_zero_sum_majorant():
    assert _fam(_ZBOUND).kind == "zero_sum_majorant"


def test_emitter_for_round_trips():
    assert emitter_for("zero_sum_majorant").kind == "zero_sum_majorant"


def test_emitter_is_classified_certificate_sensitive_wired_and_adapted():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY, wired_sensitive_emitters,
    )
    from telperion.negative_control_harness import ADAPTERS
    stance = REGISTRY["ZeroSumMajorantEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE and stance.reason.strip()
    assert stance.checked_in == "emit_zero_sum_majorant"
    assert "ZeroSumMajorantEmitter" in wired_sensitive_emitters()
    assert stance.neg_control is not None and stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "ZeroSumMajorantEmitter" in ADAPTERS


# --- acceptance: the dogfood instances, exact certificates ------------------------------

def test_zbound_certificate_is_the_audit_identity():
    """E6Bridge19 / E6Bridge15: `1/|rho|^2 <= (9/4)/(1 + |gamma|^2)` on `|Im rho| >= 1`, cleared
    and shifted by `w^2 = 1 + t`: `(5/4) t + x (1 - x) + (9/4) x^2` (audit C 2.1)."""
    c = zero_sum_majorant_certificate(**_ZBOUND)
    assert c.mode == "zero_window" and c.faces == ("strip", "majorant", "summable")
    assert c.terms == (((0, 0, 1), sp.Rational(5, 4)), ((1, 1, 0), sp.Integer(1)),
                       ((2, 0, 0), sp.Rational(9, 4)))
    t = W ** 2 - 1
    expected = sp.Rational(5, 4) * t + X * (1 - X) + sp.Rational(9, 4) * X ** 2
    assert sp.expand(c.residual - expected) == 0
    assert sp.expand(c.reconstruct() - c.residual) == 0
    assert c.residual == sp.expand(sp.Rational(9, 4) * (X ** 2 + W ** 2)
                                   - (1 + W ** 2 + (sp.Rational(1, 2) - X) ** 2))
    assert c.prefactor and c.squares == ()


def test_polbound_certificate_uses_the_hand_hint_square():
    """E6Bridge18: `1/(Im rho - Im s)^2 <= (13/4 + 2 (Im s)^2)/(1 + |gamma|^2)`; the odd ordinate
    part is removed by `(Im rho - 2 Im s)^2`, the island's own `sq_nonneg (rho.im - 2 * s.im)`."""
    c = zero_sum_majorant_certificate(**_POLBOUND)
    a = sp.Symbol("s.im", real=True)
    assert c.centre == a and c.params == (("a", "s.im"),) and c.binders == (("s", "ℂ"),)
    assert c.squares == (sp.expand(W - 2 * a),)
    assert c.terms == (((0, 0, 0, 0, 1), sp.Integer(1)), ((0, 0, 1, 0, 0), sp.Rational(5, 4)),
                       ((0, 0, 1, 1, 0), sp.Integer(2)), ((1, 1, 0, 0, 0), sp.Integer(1)))
    t = (W - a) ** 2 - 1
    expected = (W - 2 * a) ** 2 + sp.Rational(5, 4) * t + 2 * a ** 2 * t + X * (1 - X)
    assert sp.expand(c.residual - expected) == 0


def test_libound_shares_the_zbound_certificate():
    assert zero_sum_majorant_certificate(**_LIBOUND).terms == \
        zero_sum_majorant_certificate(**_ZBOUND).terms


def test_lcterm_h0_one_plus_ordinate_certificate():
    """E6Bridge22 lcTerm: the empty-window `h = 0` face with `D = 1 + (Im rho - a)^2`."""
    c = zero_sum_majorant_certificate(**_LCTERM)
    assert c.h == 0 and c.den_kind == "one_plus_ordinate_sq"
    assert all(coef > 0 for _e, coef in c.terms)
    assert sp.expand(c.reconstruct() - c.residual) == 0


def test_tail_envelope_certificate():
    c = zero_sum_majorant_certificate(**_TAIL)
    assert c.mode == "tail_envelope" and c.faces == ("envelope", "rate")
    assert c.envelope_symbolic and c.envelope_E is None
    assert c.rate_P == sp.Rational(-1, 4)
    r = zero_sum_majorant_certificate(mode="tail_envelope", envelope_E=Fraction(3, 2))
    assert r.faces == ("envelope",) and r.envelope_E == sp.Rational(3, 2)


def test_explicit_terms_round_trip():
    found = zero_sum_majorant_certificate(**_ZBOUND)
    again = zero_sum_majorant_certificate(**_ZBOUND, terms=[(e, str(c)) for e, c in found.terms])
    assert again.terms == found.terms


def test_certificate_is_sensitive_to_every_coefficient():
    """The emitted `key` identity is load-bearing: bumping any coefficient (or dropping a term)
    breaks the exact expansion `ring` has to close."""
    c = zero_sum_majorant_certificate(**_POLBOUND)
    for i in range(len(c.terms)):
        bumped = tuple((e, v + 1) if j == i else (e, v) for j, (e, v) in enumerate(c.terms))
        assert sp.expand(with_terms(c, bumped).reconstruct() - c.residual) != 0
    assert sp.expand(with_terms(c, c.terms[1:]).reconstruct() - c.residual) != 0


def test_certify_counts_checks():
    fam = certify(_fam(_ZBOUND))
    assert fam.checks_passed == 1 + 3


# --- refusals: the phantoms of the audit, one test each ---------------------------------

def test_refuses_the_named_phantom_h0_inverse_normsq_with_a_located_witness():
    """`h = 0` with a `1/|rho|^2` shape: `|rho|` is not bounded below on the strip.  FALSE, with
    an exact located point (small `Re rho`, `Im rho = 0`)."""
    msg = _refused(centre=0, h=0, c_far="9/4", num=1, den_kind="normSq")
    assert "FALSE" in msg and "'ρ.im': 0" in msg and "'ρ.re': 1/1000" in msg


def test_refuses_a_far_constant_below_the_sharp_one():
    """9/4 is sharp (at `Re rho -> 0`, `|Im rho| = 1`); 2 is located FALSE."""
    msg = _refused(centre=0, h=1, c_far=2, num=1, den_kind="normSq")
    assert "FALSE" in msg and "'ρ.im': 1" in msg


def test_obstructed_is_not_false_when_the_hand_square_is_withheld():
    """The TRUE polBound claim with no declared square keeps an odd ordinate part: no certificate
    in this basis and no counterexample -- OBSTRUCTED (unproved), never reported FALSE."""
    msg = _refused(**dict(_POLBOUND, squares=[]))
    assert "OBSTRUCTED" in msg and "FALSE" not in msg


def test_refuses_negative_far_constant_and_non_positivity_forms():
    _refused(match="< 0", centre=0, h=1, c_far="-9/4", den_kind="normSq")
    _refused(match="NEGATIVE coefficient", **dict(_POLBOUND, c_far="13/4 - 2*a^2"))
    _refused(match="ODD parameter power", **dict(_POLBOUND, c_far="13/4 + a"))


def test_refuses_nonpositive_or_zero_numerator():
    _refused(match="< 0", **dict(_ZBOUND, num=-1))
    _refused(match="identically zero", **dict(_ZBOUND, num=0))


def test_refuses_near_radius_outside_the_bounded_window_list():
    for h in (3, -1, True, 1.0, "1"):
        _refused(match="near radius", **dict(_ZBOUND, h=h))


def test_refuses_a_non_ordinate_window():
    _refused(match="ORDINATE window", **dict(_ZBOUND, window="disc"))


def test_refuses_a_conditional_support_fact():
    _refused(match="hypothesis-free", **dict(_ZBOUND, support="conditional"))


def test_refuses_unknown_denominator_and_the_vanishing_one():
    _refused(match="unknown den_kind", **dict(_ZBOUND, den_kind="abs"))
    _refused(match="ordinate_sq' with h = 0", **dict(_POLBOUND, h=0))


def test_refuses_forged_term_lists():
    good = zero_sum_majorant_certificate(**_ZBOUND).terms
    neg = [(e, -c) if i == 0 else (e, c) for i, (e, c) in enumerate(good)]
    _refused(match="NEGATIVE coefficient", **dict(_ZBOUND, terms=neg))
    off = [(e, c + 1) if i == 0 else (e, c) for i, (e, c) in enumerate(good)]
    _refused(match="does NOT expand", **dict(_ZBOUND, terms=off))
    _refused(match="length", **dict(_ZBOUND, terms=[((0, 0), 1)]))
    _refused(match="negative exponent", **dict(_ZBOUND, terms=[((0, -1, 0), 1)]))
    _refused(match="zero coefficient", **dict(_ZBOUND, terms=[((0, 0, 1), 0)]))
    _refused(match="not an int", **dict(_ZBOUND, terms=[((0.0, 0, 1), 1)]))


def test_refuses_the_false_claim_behind_a_forged_term_list_with_its_witness():
    """A term list 'certifying' the FALSE C = 1 claim is refused AND the claim is named false."""
    good = zero_sum_majorant_certificate(**_ZBOUND).terms
    msg = _refused(**dict(_ZBOUND, c_far=1, terms=list(good)))
    assert "does NOT expand" in msg and "also FALSE" in msg


def test_refuses_tail_face_phantoms():
    _refused(match="P < 0", mode="tail_envelope", envelope_E=1, rate_P=0)
    _refused(match="P < 0", mode="tail_envelope", envelope_E=1, rate_P="1/4")
    _refused(match="E >= 0", mode="tail_envelope", envelope_E="-1")
    _refused(match="needs envelope_E", mode="tail_envelope")
    _refused(match="requires a rational rate_P", mode="tail_envelope", envelope_E=1,
             faces=("envelope", "rate"))
    _refused(match="not requested", mode="tail_envelope", envelope_E=1, rate_P=-1,
             faces=("envelope",))


def test_refuses_floats_everywhere():
    _refused(match="float", **dict(_ZBOUND, c_far=2.25))
    _refused(match="float", **dict(_ZBOUND, c_far="2.25"))
    _refused(match="float", **dict(_ZBOUND, centre=0.5))
    _refused(match="float", **dict(_ZBOUND, num=1.0))
    _refused(match="float", mode="tail_envelope", envelope_E=1.5)
    _refused(match="float", mode="tail_envelope", envelope_E=1, rate_P=-0.25)
    _refused(match="float", **dict(_ZBOUND, c_far=sp.Float("2.25")))


def test_refuses_undeclared_symbols_and_non_rational_coefficients():
    _refused(match="not declared parameters", **dict(_ZBOUND, c_far="9/4 + q"))
    _refused(match="non-rational", **dict(_POLBOUND, c_far="13/4 + 2*a^2 + I*a^2"))
    _refused(match="not rational", **dict(_ZBOUND, c_far="pi"))


def test_refuses_bad_and_colliding_names():
    _refused(match="collides", **dict(_POLBOUND, params=[("K", "s.im")], centre="K",
                                      c_far="13/4 + 2*K^2"))
    for bad in ("hz", "t1", "key", "f", "b", "hshape", "K"):
        _refused(match="collides", **dict(_POLBOUND, binders=[(bad, "ℂ")]))
    # binder names are ASCII Lean identifiers; the proofs' own `ρ` can never be shadowed
    _refused(match="not a Lean identifier", **dict(_POLBOUND, binders=[("ρ", "ℂ")]))
    _refused(match="not bound", **dict(_POLBOUND, binders=[("z", "ℂ")]))
    _refused(match="only", **dict(_POLBOUND, binders=[("s", "ℕ")]))
    _refused(match="identifier path", **dict(_POLBOUND, params=[("a", "s-im")]))
    _refused(match="duplicate", **dict(_POLBOUND, binders=[("s", "ℂ"), ("s", "ℂ")]))
    # `re` / `im` name the zero coordinates when a declared square base is parsed
    _refused(match="collides", **dict(_POLBOUND, params=[("im", "s.im")], centre="im",
                                      c_far="13/4 + 2*im^2"))


def test_refuses_inconsistent_faces_and_cross_mode_keys():
    _refused(match="consumes 'majorant'", **dict(_ZBOUND, faces=("strip", "summable")))
    _refused(match="consumes 'strip'", **dict(_ZBOUND, faces=("majorant",)))
    _refused(match="unknown face", **dict(_ZBOUND, faces=("strip", "window")))
    _refused(match="duplicate face", **dict(_ZBOUND, faces=("strip", "strip")))
    _refused(match="no faces", **dict(_ZBOUND, faces=()))
    _refused(match="given in zero_window mode", **dict(_ZBOUND, envelope_E=1))
    _refused(match="given in tail_envelope mode", mode="tail_envelope", envelope_E=1,
             c_far="9/4")
    _refused(match="unknown mode", mode="zero_sum")


def test_certify_propagates_the_refusal():
    from telperion.certify import CertificationError
    with pytest.raises(CertificationError, match="REFUSED: the strip inequality is FALSE"):
        certify(_fam(dict(centre=0, h=0, c_far="9/4", den_kind="normSq")))


# --- emission: the frozen tactic skeleton, pinned by substring -------------------------

def test_emit_zbound_strip_pins_the_certificate_proof():
    txt = _emit_text(_ZBOUND, "zb")
    assert ("theorem zb_strip {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)\n"
            "    (him : (1 : ℝ) ≤ |ρ.im|) :\n"
            "    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by\n"
            ) in txt
    for line in (
        "  have hre : (0 : ℝ) < ρ.re := hz.2.1",
        "  have hre1 : ρ.re < 1 := hz.2.2",
        "    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) him 2",
        "    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]",
        "    add_pos_of_pos_of_nonneg (pow_pos hre 2) (sq_nonneg _)",
        "  rw [hn, hg, div_le_div_iff₀ hden hγ]",
        "  have key : (9 / 4) * (ρ.re ^ 2 + ρ.im ^ 2) - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))",
        "      = (5 / 4) * (ρ.im ^ 2 - 1) + 1 * (ρ.re * (1 - ρ.re)) + (9 / 4) * ρ.re ^ 2 := by",
        "  have t1 : (0 : ℝ) ≤ (5 / 4) * (ρ.im ^ 2 - 1) := mul_nonneg (by norm_num) ht0",
        "  have t2 : (0 : ℝ) ≤ 1 * (ρ.re * (1 - ρ.re)) := mul_nonneg (by norm_num) (mul_nonneg hx0 hu0)",
        "  have t3 : (0 : ℝ) ≤ (9 / 4) * ρ.re ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hx0 2)",
        "  linarith only [key, t1, t2, t3]",
    ):
        assert line in txt, line


def test_emitted_gamma_rewrite_is_the_prelude_line_verbatim():
    """The `normSq gamma` rewrite is RvMBridgeXi.inv_im_sq_le_majorant's own line."""
    txt = _emit_text(_ZBOUND, "zb")
    island = _PRELUDE_XI.read_text(encoding="utf-8")
    assert ("rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]"
            in island)
    assert "rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]" in txt


def test_emit_zbound_majorant_and_summable_faces():
    txt = _emit_text(_ZBOUND, "zb")
    for line in (
        "theorem zb_le {f : ℂ → ℂ} {b : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)",
        "    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)",
        "    (hwin : ∀ ρ, Zeta23.IsNontrivialZero ρ → |ρ.im| < (1 : ℝ) → ‖f ρ‖ ≤ b ρ)",
        "      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (K * (1 / Complex.normSq ρ)))",
        "    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt 0 1 (K * (9 / 4)) b ρ := by",
        "  refine RvMBridgeXi.norm_le_zeroBoundAt hzero",
        "    (fun ρ hz hw => hwin ρ hz (by simpa using hw)) (fun ρ hz him => ?_)",
        "    (mul_nonneg hK (by positivity)) ρ",
        "  have him' : (1 : ℝ) ≤ |ρ.im| := by simpa using him",
        "  rw [mul_div_assoc]",
        "  exact mul_le_mul_of_nonneg_left (zb_strip hz him') hK",
        "theorem zb_summable {f : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)",
        "  Summable.of_norm_bounded",
        "    (RvMBridgeXi.summable_zeroBoundAt 0 1 (K * (9 / 4)) (fun ρ => ‖f ρ‖))",
        "    (zb_le (b := fun ρ => ‖f ρ‖) hK hzero (fun _ _ _ => le_rfl) hshape)",
    ):
        assert line in txt, line


def test_emit_polbound_centred_faces():
    txt = _emit_text(_POLBOUND, "pb")
    for line in (
        "theorem pb_strip (s : ℂ) {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)",
        "    (him : (1 : ℝ) ≤ |ρ.im - s.im|) :",
        "    1 / (ρ.im - s.im) ^ 2 ≤ ((13 / 4) + 2 * s.im ^ 2) / (1 + Complex.normSq "
        "(Zeta23.gammaOf ρ)) := by",
        "  have hden : (0 : ℝ) < (ρ.im - s.im) ^ 2 := by linarith",
        "  rw [hg, div_le_div_iff₀ hden hγ]",
        "    mul_nonneg (by norm_num) (sq_nonneg (ρ.im - 2 * s.im))",
        "    mul_nonneg (by norm_num) (mul_nonneg ht0 (sq_nonneg s.im))",
        "  linarith only [key, t1, t2, t3, t4]",
        "theorem pb_le (s : ℂ) {f : ℂ → ℂ} {b : ℂ → ℝ}",
        "    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt s.im 1 ((13 / 4) + 2 * s.im ^ 2) b ρ := by",
        "  refine RvMBridgeXi.norm_le_zeroBoundAt hzero hwin (fun ρ hz him => ?_)",
        "  exact pb_strip s hz him",
        "    (pb_le s (b := fun ρ => ‖f ρ‖) hzero (fun _ _ _ => le_rfl) hshape)",
    ):
        assert line in txt, line
    assert "rw [mul_div_assoc]" not in txt and "{K : ℝ}" not in txt   # no prefactor here


def test_emit_h0_face_uses_the_empty_window_route():
    txt = _emit_text(_LCTERM, "lc")
    assert "    (_him : (0 : ℝ) ≤ |ρ.im - a|) :" in txt
    assert "  have ht0 : (0 : ℝ) ≤ (ρ.im - a) ^ 2 := sq_nonneg _" in txt
    assert "  have hden : (0 : ℝ) < (1 + (ρ.im - a) ^ 2) := by positivity" in txt
    assert "(fun ρ hz _ => ?_)" in txt and "(hshape ρ hz (abs_nonneg _))" in txt
    assert "pow_le_pow_left₀" not in txt


def test_emit_tail_faces():
    txt = _emit_text(_TAIL, "tl")
    for line in (
        "theorem tl_envelope {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)",
        "    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x := by",
        "      ≤ ∑' x : S, ‖f x‖ := norm_tsum_le_tsum_norm hsumN",
        "    _ ≤ ∑' x : S, E * w x := hsumN.tsum_le_tsum hle hsumM",
        "    _ ≤ ∑' x : ι, E * w x := hM.tsum_subtype_le _ _ hM0",
        "    _ = E * ∑' x : ι, w x := tsum_mul_left",
        "theorem tl_rate {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ (-(1 / 4))) :",
        "      ∧ Real.exp (2 * (lam - 1) * (-(1 / 4))) ≤ 1 := by",
        "    have hP : ((-(1 / 4)) : ℝ) ≤ 0 := by norm_num",
        "    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hl) hP",
    ):
        assert line in txt, line
    rat = _emit_text(dict(mode="tail_envelope", envelope_E="3/2"), "tq")
    assert "  have hE : (0 : ℝ) ≤ (3 / 2) := by norm_num" in rat
    assert "(hle : ∀ x : S, ‖f x‖ ≤ (3 / 2) * w x)" in rat and "_rate" not in rat


def test_emit_is_lint_clean_deterministic_and_honest():
    for spec in (_ZBOUND, _POLBOUND, _LCTERM, _TAIL, dict(_ZBOUND, faces=("strip",))):
        txt = _emit_text(spec)
        assert txt == _emit_text(spec), "emission is not byte-deterministic"
        errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
        assert errs == [], errs
        for bad in ("sorry", "admit", "decide", "native_decide", "axiom ", "opaque",
                    "implemented_by", "skipKernelTC"):
            assert bad not in txt, bad
        assert "conjecture1_proved = False" in txt
        for ch in txt:
            assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_theorem_counts():
    fam = zero_sum_majorant_family(
        "Counts", GridSpec([("i", [0, 1, 2])]), lambda pt: f"c{pt['i']}",
        spec=lambda pt: [_ZBOUND, _TAIL, dict(_ZBOUND, faces=("strip",))][pt["i"]])
    report = emit(certify(fam), LeanProfile(namespace=("Counts",), imports=("RvMBridgeXi",)),
                  [ZeroSumMajorantEmitter()], ValidationReport(checks=(("x", True),)))
    assert report.n_theorems == 3 + 2 + 1


def test_emit_refuses_to_ship_without_the_prelude_import():
    with pytest.raises(WorkflowError, match="RvMBridgeXi.zeroBoundAt"):
        emit(certify(_fam(_ZBOUND)), LeanProfile(namespace=("T",), imports=("Mathlib",)),
             [ZeroSumMajorantEmitter()], ValidationReport(checks=(("x", True),)))


def test_private_strip_route_names_the_theorem_exactly():
    c = zero_sum_majorant_certificate(**dict(_ZBOUND, faces=("strip",)))
    txt = ZeroSumMajorantEmitter()._emit_strip(c, "exact_name")
    assert "theorem exact_name {ρ : ℂ}" in txt and "exact_name_strip" not in txt
    with pytest.raises(ValueError):
        ZeroSumMajorantEmitter()._emit_strip(zero_sum_majorant_certificate(**_TAIL), "x")


# --- the dogfood file ---------------------------------------------------------

def _load_generator():
    spec = importlib.util.spec_from_file_location("dogfood_zero_sum_majorant", _DOGFOOD_GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_dogfood_file_is_regenerable_byte_for_byte():
    """The checked-in probe is exactly what the generator writes: banner + frozen emitter output
    + glue + kernel cross-checks -- the emitter cannot drift from the island file."""
    gen = _load_generator()
    assert gen.OUT == _DOGFOOD_LEAN
    assert _DOGFOOD_LEAN.is_file(), "run examples/rvm_bridge/dogfood_zero_sum_majorant.py"
    assert _DOGFOOD_LEAN.read_text(encoding="utf-8") == gen.build_text()


def test_dogfood_regenerates_the_three_sites_under_new_names():
    txt = _DOGFOOD_LEAN.read_text(encoding="utf-8")
    assert txt.startswith("/-\n  Dogfood_zero_sum_majorant")
    assert "conjecture1_proved = False" in txt and "Nothing here bears on RH" in txt
    assert ("import E6Bridge12\nimport E6Bridge15\nimport E6Bridge18\nimport E6Bridge19\n"
            "import RvMBridgeXi") in txt
    assert "namespace DogfoodZeroSumMajorant" in txt and "end DogfoodZeroSumMajorant" in txt
    for nm in ("zbound_regen", "polBound_regen", "liBound_regen"):
        for face in ("strip", "le", "summable"):
            assert f"theorem {nm}_{face} " in txt
            assert f"#print axioms DogfoodZeroSumMajorant.{nm}_{face}" in txt
    for face in ("envelope", "rate"):
        assert f"#print axioms DogfoodZeroSumMajorant.tail_regen_{face}" in txt
    # the originals are consumed, never redefined
    for use in ("RvMBridge19.norm_zterm_le_zbound k ρ hs", "RvMBridge18.norm_polTerm_le_majorant h hfar",
                "RvMBridgeXi.inv_normSq_le_majorant h him", "RvMBridge12.tail_bound_window hD hlam",
                "‖RvMBridge15.liPaired n ρ‖ ≤ RvMBridge15.liBound n ρ",
                "Summable (RvMBridge18.polTerm s)", "Summable (RvMBridge15.liPaired n)"):
        assert use in txt, use
    for redefined in ("def zbound", "def polBound", "def liBound", "theorem norm_zterm_le_zbound"):
        assert redefined not in txt
    assert "sorry" not in txt and "admit" not in txt and "native_decide" not in txt
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the dogfood file"
