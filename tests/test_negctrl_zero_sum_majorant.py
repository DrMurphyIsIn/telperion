"""Negative control for ZeroSumMajorantEmitter -- the forged far constant (hence FALSE strip claim).

The emitted strip proof clears denominators and states the certificate identity
`C * (x^2 + w^2) - 1 * (1 + (w^2 + (1/2 - x)^2)) = sum c_alpha * P_alpha` as `key`, closed by
`ring`.  Forge the far constant of the honest 9/4 instance down to `C = 1` (keeping its terms) and
the claim `1/|rho|^2 <= 1/(1 + |gamma_rho|^2)` on `|Im rho| >= 1` is not merely unproved, it is
FALSE: cleared it reads `Re rho >= 5/4`, false at every point of the open strip (at rho = 1/2 + i
the two sides are 4/5 and 1/2).  The TRUSTED Lean kernel is the arbiter: the forged `key` is not a
ring identity.

These tests are OFFLINE (string / exact-arithmetic level): they pin the adapter registration, the
exact falsity of the forgery, the byte relationship between the twins, the stand-in prelude's
faithfulness, and the registry declaration.  The kernel run happens through the generic harness in
`test_certificate_sensitivity` / CI (lean-gated); it was also run by hand against the built
rvm_bridge env (forged twin REJECTED at `ring`, true twin clean).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_zero_sum_majorant import (  # noqa: E402
    zero_sum_majorant_certificate,
    zsm_symbols,
)
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import registered_adapters  # noqa: E402

X, W, _ = zsm_symbols()


def _adapter():
    ad = registered_adapters().get("ZeroSumMajorantEmitter")
    assert ad is not None, "no adapter registered for ZeroSumMajorantEmitter"
    return ad


def _spec(cert):
    return dict(centre=cert.centre, h=cert.h, c_far=cert.c_far, num=cert.num,
                den_kind=cert.den_kind, faces=cert.faces,
                terms=[(e, c) for e, c in cert.terms])


def test_adapter_is_registered():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["ZeroSumMajorantEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one_with_a_witness():
    """Layer 1 would never mint the forgery: the term list does not expand to the C = 1 residual,
    and the claim itself is located FALSE."""
    cert = _adapter().make_false_cert()
    assert cert.c_far == 1
    with pytest.raises(ValueError, match="REFUSED") as ei:
        zero_sum_majorant_certificate(**_spec(cert))
    assert "also FALSE" in str(ei.value)
    with pytest.raises(ValueError, match="FALSE"):   # and without the forged terms
        zero_sum_majorant_certificate(centre=0, h=1, c_far=1, num=1, den_kind="normSq")


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Pin the arithmetic: the cleared C = 1 residual is `Re rho - 5/4 < 0` on the WHOLE strip,
    so the forgery is false at every nontrivial zero, on the critical line or off it."""
    residual = sp.expand(1 * (X ** 2 + W ** 2) - (1 + W ** 2 + (sp.Rational(1, 2) - X) ** 2))
    assert residual == X - sp.Rational(5, 4)
    # rho = 1/2 + i:  1/|rho|^2 = 4/5  >  1/(1 + |gamma|^2) = 1/2
    x0, w0 = sp.Rational(1, 2), sp.Integer(1)
    lhs = 1 / (x0 ** 2 + w0 ** 2)
    rhs = sp.Integer(1) / (1 + w0 ** 2 + (sp.Rational(1, 2) - x0) ** 2)
    assert (lhs, rhs) == (sp.Rational(4, 5), sp.Rational(1, 2)) and lhs > rhs
    # and the true twin's cleared residual is the certified nonnegative combination
    true_res = sp.expand(sp.Rational(9, 4) * (X ** 2 + W ** 2)
                         - (1 + W ** 2 + (sp.Rational(1, 2) - X) ** 2))
    assert true_res == sp.expand(sp.Rational(5, 4) * (W ** 2 - 1) + X * (1 - X)
                                 + sp.Rational(9, 4) * X ** 2)


def test_true_twin_is_accepted_by_layer_one():
    cert = _adapter().make_true_cert()
    ok = zero_sum_majorant_certificate(**_spec(cert))
    assert ok.c_far == sp.Rational(9, 4) and ok.terms == cert.terms and ok.faces == ("strip",)


def _code(txt):
    """The emitted theorem without its (reflowed) doc comment."""
    assert txt.startswith("/-- ") and "-/\n" in txt
    return txt.split("-/\n", 1)[1]


def test_twins_differ_only_in_the_far_constant():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "zsm_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "zsm_twin")
    f_lines, t_lines = _code(false_txt).splitlines(), _code(true_txt).splitlines()
    assert len(f_lines) == len(t_lines)
    diff = [(a, b) for a, b in zip(f_lines, t_lines) if a != b]
    # exactly the statement and the `key` left-hand side move -- both only in the C literal
    assert len(diff) == 2, diff
    for a, b in diff:
        assert "(9 / 4)" in b and "(9 / 4)" not in a
        assert b.replace("(9 / 4)", "1", 1) == a
    assert ("    1 / Complex.normSq ρ ≤ 1 / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by"
            in f_lines)
    assert ("    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by"
            in t_lines)
    # the certificate's right-hand side, the summand facts and the closer are shared verbatim
    for line in ("      = (5 / 4) * (ρ.im ^ 2 - 1) + 1 * (ρ.re * (1 - ρ.re)) + (9 / 4) * ρ.re ^ 2 := by",
                 "  have t3 : (0 : ℝ) ≤ (9 / 4) * ρ.re ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hx0 2)",
                 "  linarith only [key, t1, t2, t3]"):
        assert line in f_lines and line in t_lines, line
    assert "sorry" not in false_txt and "sorry" not in true_txt


def test_false_twin_states_the_false_theorem_verbatim():
    ad = _adapter()
    txt = ad.emit_call(ad.make_false_cert(), "negctrl_forged_false")
    assert "theorem negctrl_forged_false {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)" in txt
    assert "    (him : (1 : ℝ) ≤ |ρ.im|) :" in txt
    # the load-bearing step the kernel cannot discharge: a false ring identity
    assert "  have key : 1 * (ρ.re ^ 2 + ρ.im ^ 2) - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))" in txt
    assert "    ring" in txt
    # the harness names exactly this declaration in `#print axioms`
    assert "negctrl_forged_false_strip" not in txt


def test_prelude_stand_ins_are_faithful():
    """The stand-in `gammaOf` is Zeta23's `(rho - 1/2) / I` by components, and the stand-in
    `IsNontrivialZero` keeps exactly the two strip conjuncts the emitted proof reads."""
    pre = _adapter().prelude
    assert "def IsNontrivialZero (ρ : ℂ) : Prop := True ∧ 0 < ρ.re ∧ ρ.re < 1" in pre
    assert "noncomputable def gammaOf (ρ : ℂ) : ℂ := ⟨ρ.im, 1 / 2 - ρ.re⟩" in pre
    assert "theorem gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := rfl" in pre
    assert "theorem gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := rfl" in pre
    assert pre.startswith("namespace Zeta23\n") and pre.rstrip().endswith("end Zeta23")
    x, w = sp.symbols("x w", real=True)
    g = sp.expand((x + sp.I * w - sp.Rational(1, 2)) / sp.I)
    assert sp.simplify(sp.re(g) - w) == 0 and sp.simplify(sp.im(g) - (sp.Rational(1, 2) - x)) == 0
    # the emitted strip proof reads a zero only through `.2.1` / `.2.2`
    ad = _adapter()
    txt = ad.emit_call(ad.make_true_cert(), "t")
    assert "hz.2.1" in txt and "hz.2.2" in txt and "hz.1" not in txt
    assert "sorry" not in pre and "axiom" not in pre
