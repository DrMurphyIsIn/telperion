"""bohr_mollerup_gamma_ratio emitter -- kernel-checked enclosures of Real.Gamma ratios.

The shape (emitter survey N2, the general form of the hand-built CN-1 lemma
``Gamma_ratio_enclosure``): for rationals ``0 < x1, x2 < 1`` and a shift ``n``, the Bohr-Mollerup
bounds enclose ``Gamma x1 / Gamma x2`` by elementary functions of ``n`` times the exact rational
``P = prod_{k<n} (x2+k)/(x1+k)``; the four ``rpow`` factors are bracketed by kernel-decided
q-th-root inequalities, the product is computed by the kernel in blocks, and the two final
comparisons are ``Nat`` inequalities decided by the kernel.

These tests pin, in order: the exact integer arithmetic (the root brackets and the products,
against the hand-built numbers and against mpmath); the certificate's refusals (above all that a
claim the comparisons do not imply is REFUSED, not printed); the emitted text; the registry
classification and the negative-control adapter; the example's byte-stability; and, Lean-gated,
an end-to-end kernel check plus the two-sided negative control.

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

import mpmath
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_bohr_mollerup_gamma_ratio import (  # noqa: E402
    BohrMollerupGammaRatioEmitter,
    _real_rat,
    bohr_mollerup_gamma_ratio_certificate,
    bohr_mollerup_gamma_ratio_family,
    bohr_mollerup_prelude_body,
    bohr_mollerup_prelude_lean,
    gamma_ratio_products,
    iroot,
    nat_pos_upper,
    rat_neg_lower,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

mpmath.mp.dps = 60
F = Fraction


def _true_ratio(x1: Fraction, x2: Fraction):
    g = mpmath.gamma
    return g(mpmath.mpf(x1.numerator) / x1.denominator) / g(mpmath.mpf(x2.numerator) / x2.denominator)


# --- 1. exact integer arithmetic ------------------------------------------------------

def test_iroot_is_the_integer_floor_root():
    for x in (0, 1, 2, 255, 256, 257, 10 ** 30, 10 ** 30 + 1, 7 ** 40):
        for q in (1, 2, 3, 8):
            r = iroot(x, q)
            assert r ** q <= x < (r + 1) ** q, (x, q, r)


def test_root_brackets_are_one_sided_and_sharp():
    S = 10 ** 12
    U = nat_pos_upper(8000, 7, 8, S)
    assert 8000 ** 7 * S ** 8 <= U ** 8 and (U - 1) ** 8 < 8000 ** 7 * S ** 8
    L = rat_neg_lower(64003, 8, 5, 8, S)
    assert L ** 8 * 64003 ** 5 <= 8 ** 5 * S ** 8 < (L + 1) ** 8 * 64003 ** 5


def test_hand_built_n8000_numbers_are_reproduced():
    """The four bracket integers of the CN-1 GammaRatio.lean instance (g_hA .. g_hD)."""
    c = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 8000)
    assert (c.l1, c.u2, c.u3, c.l4) == (
        3635432077, 2601379650496946, 29084308668980, 325168010868)
    assert c.blocks == 40 and c.block == 200 and c.q == 8 and (c.a1, c.a2) == (3, 7)
    # The hand-built statement 2.1753 <= ratio <= 2.1755 is implied; its C6 twin is not.
    bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 8000, claim_lo="2.1753", claim_hi="2.1755")
    with pytest.raises(ValueError, match="ABOVE the certified lower bound"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 8000, claim_lo="2.1754", claim_hi="2.1755")


def test_products_use_the_common_denominator():
    q, a1, a2, gA, gB = gamma_ratio_products("1/2", "1/4", 3)
    assert (q, a1, a2) == (4, 2, 1)
    assert gA == 1 * 5 * 9 and gB == 2 * 6 * 10


@pytest.mark.parametrize("x1,x2", [("3/8", "7/8"), ("1/3", "2/3"), ("1/2", "1/4"), ("5/7", "1/9")])
def test_enclosure_contains_the_true_ratio_and_has_the_predicted_width(x1, x2):
    c = bohr_mollerup_gamma_ratio_certificate(x1, x2, 400)
    true = _true_ratio(c.x1, c.x2)
    lo = mpmath.mpf(c.lo.numerator) / c.lo.denominator
    hi = mpmath.mpf(c.hi.numerator) / c.hi.denominator
    assert lo <= true <= hi
    assert c.claim_lo <= c.lo and c.hi <= c.claim_hi
    # Relative width ~ (x1(1-x1) + x2(1-x2))/n, within a factor two at n = 400.
    pred = (c.x1 * (1 - c.x1) + c.x2 * (1 - c.x2)) / c.n
    rel = (hi - lo) / true
    assert mpmath.mpf(pred.numerator) / pred.denominator / 2 < rel < 2 * mpmath.mpf(pred.numerator) / pred.denominator


def test_width_halves_when_n_doubles():
    a = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400)
    b = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 800)
    ratio = (a.hi - a.lo) / (b.hi - b.lo)
    assert F(19, 10) < ratio < F(21, 10)


# --- 2. refusals ------------------------------------------------------------------------

def test_refuses_x_outside_the_open_unit_interval():
    for bad in ("0", "1", "9/8", "-1/2"):
        with pytest.raises(ValueError, match="open interval"):
            bohr_mollerup_gamma_ratio_certificate(bad, "1/2", 200)
        with pytest.raises(ValueError, match="open interval"):
            bohr_mollerup_gamma_ratio_certificate("1/2", bad, 200)


def test_refuses_floats_and_bad_shapes():
    with pytest.raises(ValueError, match="float"):
        bohr_mollerup_gamma_ratio_certificate(0.375, "7/8", 200)
    with pytest.raises(ValueError, match="float"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 200, claim_lo=2.1, claim_hi="2.3")
    with pytest.raises(ValueError, match="multiple of the block"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 300)
    with pytest.raises(ValueError, match="must be >= 1"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 0)
    with pytest.raises(ValueError, match="must be >= 1"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 200, scale=0)
    with pytest.raises(ValueError, match="MAX_N"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 200 * 1000)


def test_refuses_a_claim_the_comparisons_do_not_imply():
    c = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400)
    tiny = F(1, 10 ** 30)
    with pytest.raises(ValueError, match="ABOVE the certified lower bound"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400, claim_lo=c.lo + tiny, claim_hi=c.hi)
    with pytest.raises(ValueError, match="BELOW the certified upper bound"):
        bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400, claim_lo=c.lo, claim_hi=c.hi - tiny)
    # The exact bounds themselves are accepted (the comparisons hold with equality).
    d = bohr_mollerup_gamma_ratio_certificate("3/8", "7/8", 400, claim_lo=c.lo, claim_hi=c.hi)
    assert d.claim_lo == c.lo and d.claim_hi == c.hi


def test_refusal_is_the_kernel_comparison():
    """The Python refusal and the emitted Nat inequality are the same predicate."""
    c = bohr_mollerup_gamma_ratio_certificate("1/3", "2/3", 200)
    _q, _a1, _a2, gA, gB = gamma_ratio_products(c.x1, c.x2, c.n)
    assert c.key_lo_holds(gA, gB) and c.key_hi_holds(gA, gB)
    forged = replace(c, claim_lo=c.claim_hi)
    assert not forged.key_lo_holds(gA, gB)
    assert c.claim_lo.numerator * c.u2 * gB <= c.claim_lo.denominator * c.n * c.l1 * gA


# --- 3. the emitted text --------------------------------------------------------------

def _emit_text(specs):
    fam = bohr_mollerup_gamma_ratio_family(
        "BohrMollerupGammaRatioTest",
        GridSpec([("case", list(range(len(specs))))]),
        lambda pt: specs[pt["case"]][0],
        spec=lambda pt: dict(specs[pt["case"]][1]),
    )
    rep = emit(certify(fam),
               LeanProfile(namespace=("BohrMollerupGammaRatioTest",), imports=("BohrMollerupPrelude",)),
               [BohrMollerupGammaRatioEmitter()],
               ValidationReport(checks=(("bmgr", True),)))
    return next(iter(rep.files.values()))


def test_real_literal_rendering():
    assert _real_rat(F(2174, 1000)) == "(2.174 : ℝ)"
    assert _real_rat(F(1, 8)) == "(0.125 : ℝ)"
    assert _real_rat(F(2)) == "(2 : ℝ)"
    assert _real_rat(F(1, 3)) == "((1 : ℝ) / 3)"
    with pytest.raises(ValueError):
        _real_rat(F(-1, 2))


def test_emitted_text_shape_and_lint():
    txt = _emit_text([("g38", dict(x1="3/8", x2="7/8", n=400))])
    assert "import BohrMollerupPrelude" in txt
    assert "theorem g38 :" in txt
    assert "(2.174 : ℝ) ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ∧ " \
           "Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ≤ (2.177 : ℝ)" in txt
    # The products are DEFINED in blocks and the real argument is made for abstract gA gB.
    assert "def g38_gA : ℕ :=\n  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 7)" in txt
    assert "theorem g38_aux (gA gB : ℕ) (gB_pos : 0 < gB)" in txt
    assert txt.count("decide +kernel") == 6
    # The hand-built brackets at n = 400 feed the transport lemmas with the reduced fraction.
    assert "BohrMollerupPrelude.rpow_rat_neg_div_lower 3203 8 5 8" in txt
    assert "BohrMollerupPrelude.rpow_div_upper 400 7 8" in txt
    # Statement gate single-sourced from the theorem's type.
    assert "example : (2.174 : ℝ) ≤ Real.Gamma (3 / 8)" in txt
    assert "sorry" not in txt and "native_decide" not in txt and "axiom " not in txt
    assert lint_lean_text(txt) == []


def test_distinct_denominators_render_the_common_product_and_reduced_brackets():
    txt = _emit_text([("g12", dict(x1="1/2", x2="1/4", n=200))])
    assert "(4 * (200 * c + j) + 1)" in txt and "(4 * (200 * c + j) + 2)" in txt
    assert "((1 : ℝ) / 4 + k) / ((1 : ℝ) / 2 + k)" in txt
    assert "Real.Gamma (1 / 2) / Real.Gamma (1 / 4)" in txt
    assert "rpow_rat_neg_div_lower 401 2 1 2" in txt
    assert "rpow_div_upper 200 1 4" in txt
    assert "(x₁ := 1 / 2) (x₂ := 1 / 4)" in txt


def test_prelude_is_mathlib_only_and_names_the_lemmas_the_body_calls():
    pre = bohr_mollerup_prelude_lean()
    assert pre.startswith("import Mathlib\n")
    assert [ln for ln in pre.splitlines() if ln.startswith("import ")] == ["import Mathlib"]
    for nm in ("Gamma_ratio_bounds", "prod_range_chunk", "rpow_div_upper",
               "rpow_rat_neg_div_lower", "Gamma_add_le", "Gamma_add_ge", "Gamma_add_nat_eq"):
        assert f" {nm} " in pre, nm
    assert "convexOn_log_Gamma" in pre and "BohrMollerup.f_add_nat_le" in pre
    assert "sorry" not in pre and "native_decide" not in pre
    assert bohr_mollerup_prelude_body() == pre.replace("import Mathlib\n", "", 1)
    assert lint_lean_text(pre) == []


def test_emit_refuses_a_profile_without_the_prelude():
    from telperion.workflow import WorkflowError
    fam = bohr_mollerup_gamma_ratio_family(
        "X", GridSpec([("case", [0])]), lambda pt: "x",
        spec=lambda pt: dict(x1="3/8", x2="7/8", n=200))
    with pytest.raises(WorkflowError, match="prelude"):
        emit(certify(fam), LeanProfile(namespace=("X",)), [BohrMollerupGammaRatioEmitter()],
             ValidationReport(checks=(("bmgr", True),)))


def test_kind_is_dispatched_by_certify():
    """certify() reaches this kind's certificate and surfaces its refusal: the per-instance
    ValueError is collected into certify's CertificationError, message intact."""
    from telperion.certify import CertificationError
    assert isinstance(emitter_for("bohr_mollerup_gamma_ratio"), BohrMollerupGammaRatioEmitter)
    fam = bohr_mollerup_gamma_ratio_family(
        "X", GridSpec([("case", [0])]), lambda pt: "x",
        spec=lambda pt: dict(x1="3/8", x2="7/8", n=200, claim_lo="3", claim_hi="4"))
    with pytest.raises(CertificationError, match="ABOVE the certified lower bound"):
        certify(fam)


# --- 4. registry and negative-control wiring ----------------------------------------

def test_emitter_is_classified_certificate_sensitive_with_adapter():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY)
    from telperion.negative_control_harness import registered_adapters
    stance = REGISTRY["BohrMollerupGammaRatioEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE
    assert stance.reason.strip()
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "BohrMollerupGammaRatioEmitter" in registered_adapters()


def test_adapter_forges_a_genuinely_false_claim_and_twins_differ_only_there():
    from telperion.negctrl_adapters.adapter_bohr_mollerup_gamma_ratio import make_false_cert
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["BohrMollerupGammaRatioEmitter"]
    f, t = ad.make_false_cert(), ad.make_true_cert()
    assert f == make_false_cert()
    assert f.claim_lo == t.claim_hi and f.claim_hi == t.claim_hi
    # The forged LO is above the true value (so the forged theorem is FALSE), and Layer 1 refuses it.
    true = _true_ratio(t.x1, t.x2)
    assert mpmath.mpf(f.claim_lo.numerator) / f.claim_lo.denominator > true
    with pytest.raises(ValueError, match="ABOVE the certified lower bound"):
        bohr_mollerup_gamma_ratio_certificate(t.x1, t.x2, t.n, claim_lo=f.claim_lo, claim_hi=f.claim_hi)
    ft, tt = ad.emit_call(f, "twin").splitlines(), ad.emit_call(t, "twin").splitlines()
    assert len(ft) == len(tt)
    diff = [(a, b) for a, b in zip(ft, tt) if a != b]
    assert diff
    lo_t, lo_f = _real_rat(t.claim_lo), _real_rat(f.claim_lo)
    for a, b in diff:
        assert (lo_t in b or str(t.claim_lo.numerator) in b or str(t.claim_lo) in b), (a, b)
        assert (lo_f in a or str(f.claim_lo.numerator) in a or str(f.claim_lo) in a), (a, b)
    assert ad.prelude == bohr_mollerup_prelude_body()


# --- 5. the example is byte-stable ------------------------------------------------------

_EX = Path(__file__).resolve().parents[1] / "examples" / "bohr_mollerup_gamma_ratio"
_ENV = _EX / "lean"


def test_example_regenerates_byte_for_byte():
    import importlib.util
    spec = importlib.util.spec_from_file_location("bmgr_generate", _EX / "generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.main(check=True) == 0
    assert (_ENV / "BohrMollerupPrelude.lean").read_text(encoding="utf-8") == bohr_mollerup_prelude_lean()


# --- 6. Lean end to end (gated on a built env) -----------------------------------------

def _env_ready():
    from lean_env import lean_env_ready
    olean = _ENV / ".lake" / "build" / "lib" / "lean" / "BohrMollerupPrelude.olean"
    return lean_env_ready(_ENV) and olean.is_file()


lean = pytest.mark.skipif(not _env_ready(),
                          reason="bohr_mollerup_gamma_ratio Lean env not built -- skipped")


@lean
def test_lean_end_to_end_small_instance_axiom_clean():
    from telperion.verify import verify_lean
    txt = _emit_text([("bmgr_test_1_3", dict(x1="1/3", x2="2/3", n=200))])
    r = verify_lean(txt, env_dir=_ENV, decls=["BohrMollerupGammaRatioTest.bmgr_test_1_3"])
    assert r.okay and r.axioms_clean, (r.summary(), r.errors[:2])
    assert set(r.axioms["BohrMollerupGammaRatioTest.bmgr_test_1_3"]) <= {
        "propext", "Classical.choice", "Quot.sound"}


@lean
def test_lean_negative_control_lo_above_true_value():
    from telperion.negative_control_harness import (
        generic_negative_control, registered_adapters)
    res = generic_negative_control(registered_adapters()["BohrMollerupGammaRatioEmitter"],
                                   env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail
