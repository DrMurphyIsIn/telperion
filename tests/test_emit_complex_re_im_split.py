"""complex_re_im_split emitter -- kernel-checked real/imaginary-part splits of complex
polynomial expressions (shapes audit 48H, section 2 rank 4; B N3 / B D7 / C 2.10 / D 2.2).

The shape: for a complex polynomial `p` in `z` and real parameters, `(p : C).re = P_re`,
`(p : C).im = P_im`, `||p||^2 = P_re^2 + P_im^2`, `||exp p|| = exp P_re`, and the B D7 cast
face `(p : C) = ((P : R) : C)` / its `.re` for a real-valued `p` over real and natural-number
atoms.  The certificate is the CLAIMED real polynomial; sympy's split is re-verified three
ways (symbolic identity, as_real_imag, an independent exact Fraction evaluator) and a claim not
ring-equal to it is REFUSED (the B N3 forge case).  The emitted proof is the frozen skeleton of
the hand proofs it regenerates: `simp only [Complex.*_re, ..., pow_succ, pow_zero, one_mul]`
then `all_goals ring`, and for the cast face `push_cast` then `all_goals ring` (then
`Complex.ofReal_re`).

These are the pre-CI self-checks; the Lean kernel (the rvm island compile of
`Probes/Dogfood_complex_re_im_split.lean`) is the arbiter.  conjecture1_proved = False.
"""
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    ComplexReImSplitEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    complex_re_im_split_certificate,
    complex_re_im_split_family,
    emit,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_complex_re_im_split import (  # noqa: E402
    IM_SYM,
    MAX_DEGREE,
    RE_SYM,
    SIMP_SET,
    eval_complex_exact,
    render_statement,
    simp_set_for,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_GEN = _ROOT / "examples" / "complex_re_im_split" / "generate.py"
_ISLAND = _ROOT / "examples" / "rvm_bridge" / "lean"
_E6B28 = _ISLAND / "E6Bridge28.lean"
_E6B7 = _ISLAND / "E6Bridge7.lean"
_DOGFOOD = _ISLAND / "Probes" / "Dogfood_complex_re_im_split.lean"

z = sp.Symbol("z")
c, lam = sp.symbols("c lam", real=True)
a, b = sp.symbols("a b", real=True)
x, y = RE_SYM, IM_SYM
EXPO = -(2 * lam) * (z - c) ** 2


def _gen():
    """Import the dogfood generator as a module (it is a script, not a package)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("gen_complex_re_im_split", _GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _cert(p, mode, **kw):
    cert, _n = complex_re_im_split_certificate(p, mode=mode, **kw)
    return cert


def _emit_text(specs: dict, **profile_kw):
    names = list(specs)
    fam = complex_re_im_split_family(
        "ComplexReImSplitTest", GridSpec([("i", list(range(len(names))))]),
        lambda pt: names[pt["i"]], spec=lambda pt: specs[names[pt["i"]]])
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ComplexReImSplitTest",), imports=("Mathlib",), **profile_kw),
        [ComplexReImSplitEmitter()],
        ValidationReport(checks=(("complex_re_im_split", True),)),
    )
    return next(iter(report.files.values()))


# --- registry wiring --------------------------------------------------------

def test_kind_is_complex_re_im_split():
    fam = complex_re_im_split_family("T", GridSpec([("i", [0])]), lambda pt: "t",
                                     spec=lambda pt: dict(p=z ** 2, mode="re", z=z))
    assert fam.kind == "complex_re_im_split"


def test_emitter_for_round_trips():
    assert emitter_for("complex_re_im_split").kind == "complex_re_im_split"


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY, wired_sensitive_emitters)
    from telperion.negative_control_harness import ADAPTERS
    assert "ComplexReImSplitEmitter" in REGISTRY
    stance = REGISTRY["ComplexReImSplitEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE
    assert stance.reason.strip()
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "ComplexReImSplitEmitter" in ADAPTERS
    # the semantic load-bearing check is actually wired, not merely declared
    assert "ComplexReImSplitEmitter" in wired_sensitive_emitters()


# --- the certificate --------------------------------------------------------

def test_gauss_exponent_split_is_exact():
    """E6Bridge7's `hre`/`hEim`: the split of -(2 lam)(z - c)^2 at z = x + i y."""
    cert = _cert(EXPO, "re", z=z, params=(c, lam), claim=2 * lam * (y ** 2 - (x - c) ** 2))
    assert sp.expand(cert.p_re - (2 * lam * (y ** 2 - (x - c) ** 2))) == 0
    assert sp.expand(cert.p_im - (-(4 * lam * (x - c) * y))) == 0
    assert cert.mode == "re" and cert.z == z and cert.params == (c, lam)


def test_norm_sq_target_is_sum_of_squares():
    cert = _cert(z - c, "norm_sq", z=z, params=(c,), claim=(x - c) ** 2 + y ** 2)
    assert sp.expand(cert.target - (cert.p_re ** 2 + cert.p_im ** 2)) == 0


def test_claim_none_uses_the_computed_split():
    cert = _cert((a + b * sp.I) ** 3, "im", params=(a, b))
    assert sp.expand(cert.claim - (3 * a ** 2 * b - b ** 3)) == 0


def test_li_face_powers_match_e6bridge28():
    """Re (a + b i)^N for N = 2..5, the E6Bridge28 hand lemmas' right-hand sides."""
    want = {
        2: a ** 2 - b ** 2,
        3: a ** 3 - 3 * a * b ** 2,
        4: a ** 4 - 6 * a ** 2 * b ** 2 + b ** 4,
        5: a ** 5 - 10 * a ** 3 * b ** 2 + 5 * a * b ** 4,
    }
    for n, rhs in want.items():
        cert = _cert((a + b * sp.I) ** n, "re", params=(a, b), claim=rhs)
        assert sp.expand(cert.p_re - rhs) == 0


def test_independent_engine_agrees_with_sympy_at_a_point():
    env = {a: (Fraction(2, 3), Fraction(0)), b: (Fraction(-1, 5), Fraction(0))}
    got = eval_complex_exact((a + b * sp.I) ** 4, env)
    subs = {a: sp.Rational(2, 3), b: sp.Rational(-1, 5)}
    want = (sp.expand(a ** 4 - 6 * a ** 2 * b ** 2 + b ** 4).subs(subs),
            sp.expand(4 * a ** 3 * b - 4 * a * b ** 3).subs(subs))
    assert got == (Fraction(int(want[0].p), int(want[0].q)), Fraction(int(want[1].p), int(want[1].q)))


def test_certificate_reports_checks():
    _cert_, n = complex_re_im_split_certificate(EXPO, mode="re", z=z, params=(c, lam))
    assert n >= 8  # contract + 3 split routes (one per seed point x3) + degree + claim + sensitivity


# --- anti-phantom refusals (one test each) ----------------------------------

def test_refuses_unknown_mode():
    with pytest.raises(ValueError, match="REFUSED"):
        _cert(z ** 2, "conj", z=z)


def test_refuses_division_by_z():
    """B N3 phantom 1: a non-polynomial p (the declared-denominator face is a follow-on)."""
    with pytest.raises(ValueError, match="REFUSED.*division"):
        _cert(1 / z, "re", z=z)
    with pytest.raises(ValueError, match="REFUSED.*division"):
        _cert((z - c) ** (-1), "re", z=z, params=(c,))


def test_refuses_transcendental_and_conjugate():
    with pytest.raises(ValueError, match="REFUSED"):
        _cert(sp.exp(z), "re", z=z)
    with pytest.raises(ValueError, match="REFUSED"):
        _cert(sp.conjugate(z) * z, "re", z=z)
    with pytest.raises(ValueError, match="REFUSED"):
        _cert(sp.Abs(z), "re", z=z)


def test_refuses_supplied_claim_disagreeing_with_sympy():
    """B N3 phantom 2, THE FORGE CASE: Re (a + b i)^2 is a^2 - b^2, not a^2 + b^2."""
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        _cert((a + b * sp.I) ** 2, "re", params=(a, b), claim=a ** 2 + b ** 2)
    # a sign slip on the Gaussian exponent
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        _cert(EXPO, "re", z=z, params=(c, lam), claim=2 * lam * ((x - c) ** 2 - y ** 2))


def test_refuses_undeclared_symbol():
    w = sp.Symbol("w", real=True)
    with pytest.raises(ValueError, match="REFUSED.*undeclared"):
        _cert(z * w, "re", z=z)


def test_refuses_parameter_not_declared_real():
    k = sp.Symbol("k")  # complex by default
    with pytest.raises(ValueError, match="REFUSED.*real=True"):
        _cert(k * z, "re", z=z, params=(k,))


def test_refuses_real_complex_variable():
    zr = sp.Symbol("zr", real=True)
    with pytest.raises(ValueError, match="REFUSED.*declared real"):
        _cert(zr ** 2, "re", z=zr)


def test_refuses_float_literal():
    with pytest.raises(ValueError, match="REFUSED.*float"):
        _cert(0.5 * z ** 2, "re", z=z)
    with pytest.raises(ValueError, match="REFUSED.*float"):
        _cert(z ** 2, "re", z=z, claim=1.0 * (x ** 2 - y ** 2))


def test_refuses_degree_above_cap_unless_raised():
    with pytest.raises(ValueError, match="REFUSED.*degree"):
        _cert(z ** (MAX_DEGREE + 1), "re", z=z)
    _cert(z ** (MAX_DEGREE + 1), "re", z=z, max_degree=MAX_DEGREE + 1)  # explicit opt-in


def test_refuses_degenerate_bare_variable_and_constant():
    with pytest.raises(ValueError, match="REFUSED.*degenerate"):
        _cert(z, "re", z=z)
    with pytest.raises(ValueError, match="REFUSED.*bare constant"):
        _cert(sp.Integer(2) + sp.I, "re")
    # a bare atom: `(c : C).re = c` IS `Complex.ofReal_re`, `(I).im = 1` IS `Complex.I_im`
    # (found by the kernel stress run: such instances are one Mathlib lemma, not a split)
    with pytest.raises(ValueError, match="REFUSED.*degenerate.*bare atom"):
        _cert(c, "re", params=(c,))
    with pytest.raises(ValueError, match="REFUSED.*degenerate.*bare atom"):
        _cert(c, "norm_exp", params=(c,))
    with pytest.raises(ValueError, match="REFUSED.*degenerate.*bare atom"):
        _cert(sp.I, "im", params=(c,))


def test_refuses_claim_in_z_re_without_a_complex_variable():
    with pytest.raises(ValueError, match="REFUSED"):
        _cert((a + b * sp.I) ** 2, "re", params=(a, b), claim=x ** 2 - b ** 2)


def test_refuses_claim_with_imaginary_unit_or_undeclared_symbol():
    with pytest.raises(ValueError, match="REFUSED.*imaginary unit"):
        _cert(z ** 2, "re", z=z, claim=x ** 2 - y ** 2 + 0 * sp.I + sp.I * 0 + sp.I - sp.I + sp.I)
    with pytest.raises(ValueError, match="REFUSED.*undeclared"):
        _cert(z ** 2, "re", z=z, claim=x ** 2 - y ** 2 + sp.Symbol("q", real=True) * 0 + sp.Symbol("q", real=True))


def test_refuses_re_sym_clashing_with_a_parameter():
    with pytest.raises(ValueError, match="REFUSED.*clashes"):
        _cert(z * x, "re", z=z, params=(x,))


def test_refuses_p_written_in_x_y():
    with pytest.raises(ValueError, match="REFUSED"):
        _cert((x + sp.I * y) ** 2, "re", z=z)


def test_certify_propagates_the_refusal():
    fam = complex_re_im_split_family(
        "Bad", GridSpec([("i", [0])]), lambda pt: "bad",
        spec=lambda pt: dict(p=(a + b * sp.I) ** 2, mode="re", params=(a, b),
                             claim=a ** 2 + b ** 2))
    with pytest.raises(Exception, match="REFUSED"):
        certify(fam)


# --- rendering and emission -------------------------------------------------

def test_statement_rendering_pins():
    cert = _cert(EXPO, "re", z=z, params=(c, lam), claim=2 * lam * (y ** 2 - (x - c) ** 2))
    p_lean, claim_lean, prop = render_statement(cert)
    assert p_lean == "-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2)"
    assert claim_lean == "2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)"
    assert prop == f"({p_lean} : ℂ).re = {claim_lean}"
    cert = _cert(z - c, "norm_sq", z=z, params=(c,), claim=(x - c) ** 2 + y ** 2)
    assert render_statement(cert)[2] == "‖(z - (c : ℂ) : ℂ)‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2"
    cert = _cert(EXPO, "norm_exp", z=z, params=(c, lam))
    assert render_statement(cert)[2].startswith(
        "‖Complex.exp (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ)‖ = Real.exp (")
    cert = _cert(z + sp.Rational(1, 2) * c, "im", z=z, params=(c,))
    assert "((1 / 2) : ℝ) : ℂ)" in render_statement(cert)[0]


def test_li_face_statements_are_byte_identical_to_the_hand_lemmas():
    """The E6Bridge28 statements render EXACTLY as the hand lemmas (modulo `I` for
    `Complex.I` under the island's `open Complex` and the outer type ascription), which is
    what makes the tie gates `example : <stmt> := RvMBridge28.re_pow_N` meaningful."""
    src = " ".join(_E6B28.read_text(encoding="utf-8").split())
    gen = _gen()
    for n, name in ((2, "two"), (3, "three"), (4, "four"), (5, "five")):
        spec = gen.SPECS[f"e6b28_re_pow_{name}"]
        cert = _cert(spec["p"], spec["mode"], params=spec["params"], claim=spec["claim"])
        prop = render_statement(cert)[2]
        hand = prop.replace("Complex.I", "I").replace(" : ℂ).re", ").re")
        assert f"lemma re_pow_{name} (a b : ℝ) : {hand} := by" in src, (n, hand)


def test_gauss_haves_are_reproduced_from_e6bridge7():
    """The E6Bridge7 `have` statements are local (no exported name); pin that the
    regenerated claims are ring-equal to the hand right-hand sides read from the source."""
    src = _E6B7.read_text(encoding="utf-8")
    assert "have hw2re : ((z - c) ^ 2).re = (z.re - c) ^ 2 - z.im ^ 2" in src
    assert "have hw2im : ((z - c) ^ 2).im = 2 * (z.re - c) * z.im" in src
    assert "have hEim : (-(2 * (lam : ℂ)) * (z - c) ^ 2).im = -(4 * lam * (z.re - c) * z.im)" in src
    gen = _gen()
    for name, rhs in (("e6b7_hw2re", (x - c) ** 2 - y ** 2),
                      ("e6b7_hw2im", 2 * (x - c) * y),
                      ("e6b7_heim", -(4 * lam * (x - c) * y))):
        spec = gen.SPECS[name]
        cert = _cert(spec["p"], spec["mode"], z=spec["z"], params=spec["params"], claim=spec["claim"])
        assert sp.expand(cert.claim - rhs) == 0


def test_emit_is_lint_clean_and_deterministic():
    specs = {
        "t_re": dict(p=EXPO, mode="re", z=z, params=(c, lam),
                     claim=2 * lam * (y ** 2 - (x - c) ** 2)),
        "t_sq": dict(p=z - c, mode="norm_sq", z=z, params=(c,), claim=(x - c) ** 2 + y ** 2),
        "t_exp": dict(p=EXPO, mode="norm_exp", z=z, params=(c, lam)),
        "t_im": dict(p=(a + b * sp.I) ** 3, mode="im", params=(a, b)),
    }
    txt = _emit_text(specs)
    assert txt == _emit_text(specs), "emission is not byte-deterministic"
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == [], errs
    assert "sorry" not in txt and "admit" not in txt
    assert "conjecture1_proved = False" in txt
    # the frozen skeleton, verbatim pieces: the tailored simp set of the Gaussian exponent
    # (canonical order; `neg_im` absent because the outermost negation is only ever projected
    # as `.re`; `add`/`I`/`one`/`zero` lemmas absent because no such constructor occurs)
    flat = " ".join(txt.split())
    assert ("simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, "
            "Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, "
            "Complex.im_ofNat, pow_succ, pow_zero, one_mul] all_goals ring") in flat
    assert "Complex.zero_re" not in txt and "Complex.one_re" not in txt
    assert "<;>" not in txt
    assert txt.count("\n  all_goals ring\n") + txt.count("\n    all_goals ring\n") == 4
    used = set(re.findall(r"Complex\.\w+_(?:re|im|ofNat)|pow_succ|pow_zero|one_mul", txt))
    assert used <= set(SIMP_SET) | {"Complex.sq_norm"}, used - set(SIMP_SET)
    assert "rw [Complex.sq_norm, Complex.normSq_apply]" in txt
    assert "have hre : (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re =" in txt
    assert "rw [Complex.norm_exp, hre]" in txt
    # the statement-match gate after every theorem
    assert txt.count("example : ∀ ") == 4
    assert "example : ∀ (c lam : ℝ) (z : ℂ), (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re =" in txt
    assert "theorem t_im (a b : ℝ) :\n    (((a : ℂ) + (b : ℂ) * Complex.I) ^ 3 : ℂ).im = 3 * a ^ 2 * b - b ^ 3 := by" in txt
    # no search tactic anywhere
    for forbidden in ("nlinarith", "polyrith", "aesop", "decide", "simp [", "simp?", "exact?"):
        assert forbidden not in txt, forbidden


def test_simp_set_is_tailored_by_syntax_in_canonical_order():
    """`simp_set_for` keeps exactly the canonical lemmas whose constructors occur in the
    rendered statement (an over-approximation: nothing that can fire is dropped), as a
    subsequence of `SIMP_SET`."""
    cert = _cert((a + b * sp.I) ** 2, "re", params=(a, b))
    assert simp_set_for(cert) == (
        "Complex.add_re", "Complex.add_im", "Complex.mul_re", "Complex.mul_im",
        "Complex.ofReal_re", "Complex.ofReal_im", "Complex.I_re", "Complex.I_im",
        "pow_succ", "pow_zero", "one_mul")
    cert = _cert(EXPO, "re", z=z, params=(c, lam), claim=2 * lam * (y ** 2 - (x - c) ** 2))
    # the outermost negation is projected only as `.re`, so `neg_im` is not needed; the
    # product chain `2 * lam * w ^ 2` is projected both ways inside, so everything else is
    assert simp_set_for(cert) == (
        "Complex.sub_re", "Complex.sub_im", "Complex.mul_re", "Complex.mul_im",
        "Complex.neg_re", "Complex.ofReal_re", "Complex.ofReal_im",
        "Complex.re_ofNat", "Complex.im_ofNat", "pow_succ", "pow_zero", "one_mul")
    assert "Complex.neg_im" in simp_set_for(
        _cert(EXPO, "im", z=z, params=(c, lam)))
    assert "Complex.neg_re" not in simp_set_for(
        _cert(EXPO, "im", z=z, params=(c, lam)))
    # no power anywhere and no product: only the top projection of each piece
    cert = _cert(z + 1, "re", z=z)
    assert simp_set_for(cert) == ("Complex.add_re", "Complex.one_re")
    # sympy stores `z * z` as the literal power `z ** 2`: one product, unfolded
    cert = _cert(z * z, "re", z=z, claim=x ** 2 - y ** 2)
    assert simp_set_for(cert) == ("Complex.mul_re", "pow_succ", "pow_zero", "one_mul")
    # a power only on the claim side still keeps the unfolders (simp rewrites both sides)
    cert = _cert(z * c, "re", z=z, params=(c,), claim=(x + c) ** 2 - x ** 2 - c ** 2 - x * c)
    assert not cert.p.atoms(sp.Pow) and cert.claim.atoms(sp.Pow)
    assert simp_set_for(cert) == ("Complex.mul_re", "Complex.ofReal_re", "Complex.ofReal_im",
                                  "pow_succ", "pow_zero", "one_mul")
    # norm_sq projects both ways at the top
    cert = _cert(z - c, "norm_sq", z=z, params=(c,), claim=(x - c) ** 2 + y ** 2)
    assert simp_set_for(cert) == (
        "Complex.sub_re", "Complex.sub_im", "Complex.ofReal_re", "Complex.ofReal_im",
        "pow_succ", "pow_zero", "one_mul")
    for cert in (_cert(z - sp.Rational(1, 2) * c * sp.I, "im", z=z, params=(c,)),
                 _cert(3 * (a + b * sp.I) ** 3 - 1, "re", params=(a, b))):
        sel = simp_set_for(cert)
        assert [lem for lem in SIMP_SET if lem in sel] == list(sel)


def test_tie_gate_is_emitted_only_when_requested():
    with_tie = _emit_text({"t2": dict(p=(a + b * sp.I) ** 2, mode="re", params=(a, b),
                                      claim=a ** 2 - b ** 2, tie_to="RvMBridge28.re_pow_two")})
    assert ("example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 : ℂ).re = "
            "a ^ 2 - b ^ 2 := RvMBridge28.re_pow_two") in with_tie
    without = _emit_text({"t2": dict(p=(a + b * sp.I) ** 2, mode="re", params=(a, b),
                                     claim=a ** 2 - b ** 2)})
    assert "RvMBridge28" not in without


def test_no_emoji_in_emitted_lean():
    txt = _emit_text({"t2": dict(p=(a + b * sp.I) ** 2, mode="re", params=(a, b))})
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


# --- the dogfood -------------------------------------------------------------

def test_dogfood_regenerates_byte_for_byte():
    """The frozen probe on the rvm island IS the generator's output (the drift gate)."""
    gen = _gen()
    text = gen.build()
    assert _DOGFOOD.is_file(), "dogfood probe missing; run examples/complex_re_im_split/generate.py"
    assert _DOGFOOD.read_text(encoding="utf-8") == text
    assert ("import E6Bridge5\nimport E6Bridge7\nimport E6Bridge11\nimport E6Bridge14\n"
            "import E6Bridge28") in text
    assert "15 theorems" in text
    for nm in gen.NAMES:
        assert f"theorem {nm} " in text
        # every emitted theorem is axiom-printed at the end of the file
        assert f"#print axioms DogfoodComplexReImSplit.{nm}\n" in text
    assert text.count(":= RvMBridge28.re_pow_") == 4
    assert text.startswith(gen.BANNER) and "conjecture1_proved = False" in gen.BANNER
    errs = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errs == []
    assert not re.search(r"\bsorry\b", text)


def test_dogfood_consumer_gates_retire_the_e6bridge7_hand_haves():
    """The E6Bridge7 sites are local `have`s, so they carry no tie gate.  Their analogue is
    the CONSUMER gate: the probe (a) pins each hand lemma's statement by ascribing it to the
    hand lemma, and (b) re-proves it from the emitted splits alone.  Pin both, pin that the
    footer is declared hand-written (it is NOT emitter output), and pin that the only glue is
    `neg_mul` plus `ring` reshapings -- no search tactic."""
    gen = _gen()
    text = gen.build()
    assert gen.CONSUMER_GATES in text and text.endswith(gen.CONSUMER_GATES + gen.AXIOM_PRINTS)
    foot = gen.CONSUMER_GATES
    # (a) the statement pins: the restated goal IS the hand lemma
    assert ":= RvMBridge7.norm_gaussTest" in foot
    assert "RvMBridge7.re_gaussTest" in foot
    # (b) the re-proofs consume the emitted theorems and nothing else from the island
    assert "rw [norm_mul, Complex.norm_pow, neg_mul, e6b7_hexp, e6b7_hsq," in foot
    assert ("rw [neg_mul, Complex.mul_re, Complex.exp_re, Complex.exp_im, e6b7_hre, "
            "e6b7_heim,") in foot
    for nm in ("e6b7_hsq", "e6b7_hexp", "e6b7_hre", "e6b7_heim", "e6b7_hw2re", "e6b7_hw2im"):
        assert nm in foot, nm
    # honesty: the footer declares itself hand-written and names the residual glue
    assert "hand-written" in foot and "Nothing here is emitter output" in foot
    assert "conjecture1_proved = False" in foot
    # determinism: only rw / ring / unfold / show, no search tactic
    for forbidden in ("nlinarith", "linarith", "polyrith", "aesop", "decide", "simp",
                      "exact?", "norm_num"):
        assert forbidden not in foot, forbidden
    assert not re.search(r"\bsorry\b", foot)
    for ch in foot:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the consumer gates"


# --- the audit's OTHER cited instances: what the family reaches, and what it refuses ------

def _audit_reached_cases():
    """`name -> (spec, pin)` for the audit-cited sites the family reaches OUTSIDE the probe
    (design note section 7.3).  Keys carry the AUDIT's line numbers; the comments give where
    each site sits in the current island (the prelude hoist moved several)."""
    b, u, k, Bat, cpar, s = sp.symbols("b u k Bat cpar s", real=True)
    xr = sp.Symbol("xr", real=True)
    zc, zz, zs = sp.Symbol("c"), sp.Symbol("z"), sp.Symbol("s2")
    cre, cim = sp.Symbol("cre", real=True), sp.Symbol("cim", real=True)
    zre, zim = sp.Symbol("zre", real=True), sp.Symbol("zim", real=True)
    sre, sim = sp.Symbol("sre", real=True), sp.Symbol("sim", real=True)
    cases = {
        # E6Bridge8:84-85 -- the complex atom is the SPLIT variable, b and x are parameters
        "e6b8_84": (dict(p=-b * xr ** 2 + zc * xr, mode="re", z=zc, params=(b, xr),
                         re_sym=cre, im_sym=cim, claim=-b * xr ** 2 + cre * xr),
                    "c.re * xr - b * xr ^ 2"),
        # E6Bridge8:308-311
        "e6b8_308": (dict(p=sp.I * zz * u, mode="re", z=zz, params=(u,),
                          re_sym=zre, im_sym=zim, claim=-(zim * u)), "-(z.im * u)"),
        # E6Bridge8:409-410 -- `Bat` stands for the real atom `gaussB lam` (a bound parameter,
        # NOT the atom itself: the consumer instantiates it)
        "e6b8_409": (dict(p=-Bat * u ** 2 - sp.I * cpar * u, mode="re",
                          params=(Bat, u, cpar), claim=-Bat * u ** 2), "-(Bat * u ^ 2)"),
        # E6Bridge10:430-431
        "e6b10_430": (dict(p=(zs - sp.Rational(1, 2)) * u, mode="re", z=zs, params=(u,),
                           re_sym=sre, im_sym=sim,
                           claim=(sre - sp.Rational(1, 2)) * u), "u * (s2.re - (1 / 2))"),
        # E6Bridge11:396 -- the `= 0` face
        "e6b11_396": (dict(p=-(sp.I * cpar * u), mode="re", params=(cpar, u),
                           claim=sp.Integer(0)), "= 0"),
        # E6Bridge11:533
        "e6b11_533": (dict(p=k * u, mode="re", params=(k, u), claim=k * u), "= k * u"),
        # C 2.10, E6Bridge16:282-290 -- the PURE split (see the refusal test below)
        "e6b16_re": (dict(p=(s * sp.I - cpar) ** 2, mode="re", params=(s, cpar),
                          claim=cpar ** 2 - s ** 2), "-(s ^ 2) + cpar ^ 2"),
        "e6b16_im": (dict(p=(s * sp.I - cpar) ** 2, mode="im", params=(s, cpar),
                          claim=-2 * s * cpar), "-(2 * s * cpar)"),
        # E6Bridge6:408-421 (now :411) -- `hre` under `set x := z.re - c`, `set y := z.im`;
        # its `hsq` is the probe's e6b7_hsq instance verbatim
        "e6b6_408": (dict(p=-(2 * lam) * (z - c) ** 2, mode="re", z=z, params=(c, lam),
                          claim=-(2 * lam) * ((x - c) ** 2 - y ** 2)),
                     "(-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re = "),
        # E6Bridge11:649-652 (now :671-673; also RvMBridgeGauss:218-220, E6Bridge16:112-114)
        "e6b11_649_h1": (dict(p=-cpar * xr ** 2, mode="re", params=(cpar, xr),
                              claim=-cpar * xr ** 2), "= -(cpar * xr ^ 2)"),
        "e6b11_649_h2": (dict(p=sp.I * u * xr, mode="re", params=(u, xr),
                              claim=sp.Integer(0)), "= 0"),
        # RvMBridgeGauss:220 / E6Bridge16:114 -- the complex-frequency twin of h2
        "gauss_220_h2": (dict(p=sp.I * zz * xr, mode="re", z=zz, params=(xr,),
                              re_sym=zre, im_sym=zim, claim=-(zim * xr)), "-(z.im * xr)"),
        # E6Bridge11:762-765 (now :789) -- a rational coefficient on I
        "e6b11_762": (dict(p=sp.Rational(1, 4) + (u / 2) * sp.I, mode="re", params=(u,),
                           claim=sp.Rational(1, 4)), "= (1 / 4)"),
        # B D7, E6Bridge12:122-126 -- a natural-number atom times the complex value
        "e6b12_122": (dict(p=m_nat * zz, mode="re", z=zz, params=(m_nat,), nat_params=(m_nat,),
                           re_sym=zre, im_sym=zim, claim=m_nat * zre),
                      "(z * (m : ℂ) : ℂ).re = z.re * (m : ℝ)"),
    }
    return cases


def test_audit_cited_instances_outside_the_probe_are_covered():
    """B N3 / B D7 / C 2.10 list sites beyond the dogfood probe.  Pin that each one certifies
    and renders (the coverage claim of the design note, section 7.3, checked rather than
    asserted); the emitted Lean for all of them elaborates against Mathlib alone (design
    note section 9)."""
    cases = _audit_reached_cases()
    for name, (spec, pin) in cases.items():
        kw = {key: val for key, val in spec.items() if key not in ("p", "mode")}
        cert = _cert(spec["p"], spec["mode"], **kw)
        prop = render_statement(cert)[2]
        assert pin in prop, (name, prop)
    txt = _emit_text({n: spec for n, (spec, _pin) in cases.items()})
    assert [i for i in lint_lean_text(txt) if i.severity == "error"] == []
    assert txt.count("theorem ") == len(cases)


def test_audit_cited_instances_the_family_does_NOT_reach():
    """The design note's honest counter-list (section 7.3).  These sites are cited by the
    audits in the same clusters but are OUTSIDE this kind; pin the refusals so the claim
    cannot rot into an overclaim."""
    lam2, s, cpar = sp.symbols("lam2 s cpar", real=True)
    # (1) E6Bridge6.lean:408-421 `hnormSq` is a `Complex.normSq` face, not `||p|| ^ 2`, and
    #     its expression is the bare variable: refused as degenerate.
    with pytest.raises(ValueError, match="REFUSED: degenerate"):
        complex_re_im_split_certificate(z, mode="norm_sq", z=z, claim=x ** 2 + y ** 2)
    # (2) E6Bridge6.lean:382-392 `gaussTest_axis` is a COMPLEX-valued cast identity carrying
    #     `Complex.exp`: no mode states it, and a transcendental `p` is refused outright.
    with pytest.raises(ValueError, match="non-polynomial node exp"):
        complex_re_im_split_certificate(sp.exp(-(2 * lam2) * (z - cpar) ** 2), mode="re",
                                        z=z, params=(cpar, lam2))
    # (3) E6Bridge16.lean:282-290 `hre` AS WRITTEN substitutes the hypothesis `s^2 = 1/4`
    #     into the split; the emitter refuses to launder a hypothesis into an identity.
    p16 = -(2 * lam2) * ((s * sp.I - cpar) ** 2)
    with pytest.raises(ValueError, match="REFUSED: the supplied claim disagrees"):
        complex_re_im_split_certificate(p16, mode="re", params=(s, cpar, lam2),
                                        claim=-(2 * lam2) * (cpar ** 2 - sp.Rational(1, 4)))
    # the pure split at that site IS reached
    cert = _cert(p16, "re", params=(s, cpar, lam2), claim=-(2 * lam2) * (cpar ** 2 - s ** 2))
    assert sp.expand(cert.claim - cert.p_re) == 0
    # (4) E6Bridge11.lean:942 / 1339, the second half of the archSide bookkeeping,
    #     `(1 / (2 pi)) * J = (((1 / (2 pi)) * J : R) : C)`, divides by the real atom pi:
    #     no division face, refused (the first half, `gaussA lam * log pi`, IS reached).
    pi_, J = sp.symbols("pi_ J", real=True)
    with pytest.raises(ValueError, match="REFUSED.*division"):
        complex_re_im_split_certificate(J / (2 * pi_), mode="cast", params=(pi_, J))
    # (5) E6Bridge28.lean:755-789 `one_sub_inv_eq_div_normSq` / `liKernel_re_eq` divide by
    #     rho and by normSq rho ^ N (a symbolic exponent): refused.
    with pytest.raises(ValueError, match="REFUSED.*division"):
        complex_re_im_split_certificate(1 - 1 / z, mode="re", z=z)
    N = sp.Symbol("N", integer=True, positive=True)
    with pytest.raises(ValueError, match="REFUSED.*exponent"):
        complex_re_im_split_certificate((a + b * sp.I) ** N, mode="re", params=(a, b))


# --- the B D7 cast face and natural-number atoms ------------------------------

m_nat = sp.Symbol("m", integer=True, nonnegative=True)
u_r, g_r = sp.symbols("u g", real=True)


def test_cast_face_certifies_and_renders():
    cert = _cert(m_nat * u_r ** 2, "cast", params=(m_nat, u_r), nat_params=(m_nat,),
                 claim=m_nat * u_r ** 2)
    assert cert.p_im == 0 and sp.expand(cert.claim - cert.p_re) == 0
    assert cert.nat_params == (m_nat,)
    assert render_statement(cert)[2] == (
        "((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = (((m : ℝ) * u ^ 2 : ℝ) : ℂ)")
    cert = _cert(2 * m_nat * g_r, "cast_re", params=(m_nat, g_r), nat_params=(m_nat,))
    assert render_statement(cert)[2] == "(2 * (m : ℂ) * (g : ℂ) : ℂ).re = 2 * (m : ℝ) * g"
    assert simp_set_for(cert) == ()  # the cast face never uses the component set
    # a purely real product (E6Bridge11's gaussA lam * log pi)
    A, L = sp.symbols("A L", real=True)
    cert = _cert(A * L, "cast", params=(A, L))
    assert render_statement(cert)[2] == "((A : ℂ) * (L : ℂ) : ℂ) = ((A * L : ℝ) : ℂ)"


def test_cast_face_emits_the_audit_skeleton():
    """B D7's skeleton verbatim: `push_cast; ring` for the identity, then
    `Complex.ofReal_re` for its real part; nothing from the component simp set."""
    txt = _emit_text({
        "t_cast": dict(p=m_nat * u_r ** 2, mode="cast", params=(m_nat, u_r),
                       nat_params=(m_nat,)),
        "t_cast_re": dict(p=2 * m_nat * g_r, mode="cast_re", params=(m_nat, g_r),
                          nat_params=(m_nat,)),
        "t_rat": dict(p=sp.Rational(1, 2) * a - b ** 3, mode="cast", params=(a, b)),
    })
    assert ("theorem t_cast (m : ℕ) (u : ℝ) :\n"
            "    ((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = (((m : ℝ) * u ^ 2 : ℝ) : ℂ) := by\n"
            "  push_cast\n  all_goals ring\n") in txt
    assert ("theorem t_cast_re (m : ℕ) (g : ℝ) :\n"
            "    (2 * (m : ℂ) * (g : ℂ) : ℂ).re = 2 * (m : ℝ) * g := by\n"
            "  have hcast : (2 * (m : ℂ) * (g : ℂ) : ℂ) = ((2 * (m : ℝ) * g : ℝ) : ℂ) := by\n"
            "    push_cast\n    all_goals ring\n"
            "  rw [hcast, Complex.ofReal_re]\n") in txt
    assert ("theorem t_rat (a b : ℝ) :\n"
            "    ((((1 / 2) : ℝ) : ℂ) * (a : ℂ) - (b : ℂ) ^ 3 : ℂ) = "
            "(((1 / 2) * a - b ^ 3 : ℝ) : ℂ) := by\n") in txt
    assert "simp only" not in txt
    assert "natural-number atoms ['m']" in txt
    assert txt.count("example : ∀ ") == 3
    assert "example : ∀ (m : ℕ) (u : ℝ), ((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = " in txt
    assert [i for i in lint_lean_text(txt) if i.severity == "error"] == []
    assert not re.search(r"\bsorry\b", txt)
    for forbidden in ("nlinarith", "polyrith", "aesop", "decide", "simp [", "exact?"):
        assert forbidden not in txt, forbidden


def test_nat_atoms_in_the_split_modes_use_natCast():
    """A natural-number atom in the re/im modes projects through `Complex.natCast_re` /
    `natCast_im` (the E6Bridge12.lean:122-126 pair), never through `ofReal`."""
    w = sp.Symbol("w")
    cert = _cert(m_nat * w, "re", z=w, params=(m_nat,), nat_params=(m_nat,))
    assert simp_set_for(cert) == ("Complex.mul_re", "Complex.natCast_re", "Complex.natCast_im")
    assert render_statement(cert)[2] == "(w * (m : ℂ) : ℂ).re = w.re * (m : ℝ)"
    cert = _cert(2 * m_nat * g_r * w, "im", z=w, params=(m_nat, g_r), nat_params=(m_nat,))
    sel = simp_set_for(cert)
    assert "Complex.natCast_re" in sel and "Complex.natCast_im" in sel
    assert "Complex.ofReal_re" in sel and "Complex.ofReal_im" in sel
    assert [lem for lem in SIMP_SET if lem in sel] == list(sel)


def test_binders_group_consecutive_atoms_by_type():
    c2, lam2 = sp.symbols("c2 lam2", real=True)
    n_nat = sp.Symbol("n", integer=True, nonnegative=True)
    txt = _emit_text({
        "t_mix": dict(p=c2 * m_nat * lam2 * z, mode="re", z=z, params=(c2, m_nat, lam2),
                      nat_params=(m_nat,)),
        "t_two": dict(p=m_nat * n_nat * u_r, mode="cast", params=(m_nat, n_nat, u_r),
                      nat_params=(m_nat, n_nat)),
    })
    assert "theorem t_mix (c2 : ℝ) (m : ℕ) (lam2 : ℝ) (z : ℂ) :" in txt
    assert "theorem t_two (m n : ℕ) (u : ℝ) :" in txt


def test_cast_face_refusals():
    # a complex variable is not real: the cast identity would be false
    with pytest.raises(ValueError, match="REFUSED.*complex variable"):
        _cert(z * c, "cast", z=z, params=(c,))
    # I in p: push_cast; ring cannot use I^2 = -1 (the product IS real-valued here)
    with pytest.raises(ValueError, match="REFUSED.*I-free"):
        _cert((a + b * sp.I) * (a - b * sp.I), "cast", params=(a, b))
    # a bare atom is the reflexive class / one Mathlib cast lemma
    with pytest.raises(ValueError, match="REFUSED.*degenerate"):
        _cert(u_r, "cast_re", params=(u_r,))
    with pytest.raises(ValueError, match="REFUSED.*degenerate"):
        _cert(m_nat, "cast", params=(m_nat,), nat_params=(m_nat,))
    # the forge case on the cast face
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        _cert(m_nat * u_r ** 2, "cast", params=(m_nat, u_r), nat_params=(m_nat,),
              claim=m_nat * u_r ** 2 + 1)
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        _cert(2 * m_nat * g_r, "cast_re", params=(m_nat, g_r), nat_params=(m_nat,),
              claim=m_nat * g_r)


def test_nat_atom_refusals():
    # a natural-number atom must be a declared parameter ...
    with pytest.raises(ValueError, match="REFUSED.*not a declared parameter"):
        _cert(m_nat * u_r, "cast", params=(u_r,), nat_params=(m_nat,))
    # ... declared integer and nonnegative, so the binder (m : N) is what sympy splits
    k = sp.Symbol("k", real=True)
    with pytest.raises(ValueError, match="REFUSED.*integer=True, nonnegative=True"):
        _cert(k * u_r, "cast", params=(k, u_r), nat_params=(k,))
    kz = sp.Symbol("kz", integer=True)  # may be negative: not a natural number
    with pytest.raises(ValueError, match="REFUSED.*integer=True, nonnegative=True"):
        _cert(kz * u_r, "cast", params=(kz, u_r), nat_params=(kz,))
    with pytest.raises(ValueError, match="REFUSED.*duplicate natural-number"):
        _cert(m_nat * u_r, "cast", params=(m_nat, u_r), nat_params=(m_nat, m_nat))


def test_reserved_binder_names_are_refused():
    """A binder named `Complex` turns the emitted `Complex.I` into field access on a real
    (kernel-checked: `Invalid field I`); keywords are not identifiers; `hre` / `hcast` are the
    proofs' own hypotheses."""
    for nm in ("Complex", "Real", "fun", "by", "hre", "hcast"):
        bad = sp.Symbol(nm, real=True)
        with pytest.raises(ValueError, match="REFUSED.*reserved"):
            _cert(bad * z, "re", z=z, params=(bad,))
    with pytest.raises(ValueError, match="REFUSED.*reserved"):
        _cert(sp.Symbol("Complex") ** 2, "re", z=sp.Symbol("Complex"))
    ok = sp.Symbol("Complexity", real=True)  # a prefix is not the namespace
    _cert(ok * z, "re", z=z, params=(ok,))


def test_tie_to_must_be_a_lean_identifier():
    """`tie_to` is rendered verbatim after `:=`; anything but a dotted identifier is refused
    (it could otherwise smuggle a proof term into the tie gate)."""
    with pytest.raises(ValueError, match="REFUSED.*Lean identifier"):
        _cert((a + b * sp.I) ** 2, "re", params=(a, b), tie_to="by simp")
    with pytest.raises(ValueError, match="REFUSED.*Lean identifier"):
        _cert((a + b * sp.I) ** 2, "re", params=(a, b), tie_to="RvMBridge28.re_pow_two; x")
    _cert((a + b * sp.I) ** 2, "re", params=(a, b), tie_to="RvMBridge28.re_pow_two")


# The hand statements of the five B D7 cast sites, whitespace-normalised, exactly as the
# island writes them (the probe's instantiation gates restate them verbatim).
_CAST_SITES = {
    "E6Bridge5.lean": [
        "(WeilExplicit.zeroMult ρ : ℂ) * ((‖paperFT g ρ.im‖ : ℂ)) ^ 2 = "
        "(((WeilExplicit.zeroMult ρ : ℝ) * ‖paperFT g ρ.im‖ ^ 2 : ℝ) : ℂ)",
    ],
    "E6Bridge7.lean": [
        "(2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ)) = "
        "((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re : ℝ) : ℂ)",
        "(2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ)).re = "
        "2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re",
    ],
    "E6Bridge11.lean": [
        "(gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ)",
    ],
    "E6Bridge14.lean": [
        "((WeilExplicit.zeroMult ρ : ℂ) * ((-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * "
        "(1 / 2 - ρ.re) ^ 2) : ℝ) : ℂ)) = (((WeilExplicit.zeroMult ρ : ℝ) * (-((1 / 2 - ρ.re) "
        "^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2)) : ℝ) : ℂ)",
    ],
}


def test_cast_site_gates_restate_the_island_verbatim():
    """Each instantiation gate in the probe footer states the hand `have` EXACTLY as the
    island writes it (whitespace aside), so the kernel's acceptance of
    `<emitted theorem> <island atoms>` at that type says the hand statement IS an instance of
    the emitted one.  A drift in the island source turns this test red before the probe's
    compile does."""
    gen = _gen()
    foot = " ".join(gen.CONSUMER_GATES.split())
    for fname, stmts in _CAST_SITES.items():
        src = " ".join((_ISLAND / fname).read_text(encoding="utf-8").split())
        for stmt in stmts:
            assert stmt in src, (fname, stmt)
            assert stmt in foot, (fname, stmt)
    # E6Bridge11 writes the same `show` twice (re_archSide_ge and the large-c theorem)
    src11 = " ".join((_ISLAND / "E6Bridge11.lean").read_text(encoding="utf-8").split())
    assert src11.count(_CAST_SITES["E6Bridge11.lean"][0]) == 2
    # each gate is closed by the emitted theorem itself, applied to the island atoms
    for nm in ("e6b5_hcast", "e6b7_pair_hcast", "e6b7_pair_hre", "e6b11_arch_hcast",
               "e6b14_centre_hcast"):
        assert f"\n  {nm} " in gen.CONSUMER_GATES, nm
        assert gen.SPECS[nm]["mode"] in ("cast", "cast_re")
