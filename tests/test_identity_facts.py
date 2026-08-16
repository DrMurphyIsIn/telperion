"""B+C tests: identity families and exact-fact emission."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    ExactFactEmitter,
    fact_pow,
    GridSpec,
    IdentityEmitter,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    int_expr_lean,
)
from telperion.interchange import export_certificates  # noqa: E402
from telperion.recheck import recheck  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


def poly_eq(pt):
    # (u^2 + (a+1)u + a)/(u + 1) = u + a — true, and the denominator SURVIVES
    # sympy's construction-time evaluation (unlike (1+u)/(1+u) -> 1)
    a = pt["a"]
    return ((u**2 + (a + 1) * u + a) / (u + 1), u + a)


def eq_fam(equation):
    return InequalityFamily(
        name="Id",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"id_a{pt['a']}",
        equation=equation,
    )


# ---- B: identity families ---------------------------------------------------
def test_identity_certifies_true_equation():
    cf = certify(eq_fam(poly_eq))
    assert all(i.equation is not None for i in cf.instances)


def test_identity_refuses_false_equation():
    with pytest.raises(CertificationError, match="identity self-check"):
        certify(eq_fam(lambda pt: ((pt["a"] + u) / (1 + u), sp.Integer(1))))


def test_identity_emitter_renders_field_simp_shape():
    cf = certify(eq_fam(poly_eq))
    res = emit(cf, LeanProfile(), [IdentityEmitter()], GREEN)
    text = next(iter(res.files.values()))
    assert "theorem id_a1 (u : ℝ) (hu : 0 ≤ u) :" in text
    assert "have hd1 : (1 + u : ℝ) ≠ 0 := by positivity" in text
    assert "field_simp" in text and "try ring" in text
    assert "/ (u + 1)" in text or "/ (1 + u)" in text   # the spelling survives
    assert res.n_theorems == 2


def test_identity_export_recheck_roundtrip_and_tamper():
    cf = certify(eq_fam(poly_eq))
    doc = export_certificates(cf, "e" * 64)
    assert recheck(doc, trials=15) == []
    doc["instances"][0]["equation"]["rhs"] = {"rat": "2/1"}
    assert any("IDENTITY FAILS" in p for p in recheck(doc, trials=15))


# ---- C: exact facts ---------------------------------------------------------
def test_int_expr_lean_keeps_powers_unevaluated():
    e = sp.Mul(fact_pow(3, 317), fact_pow(2, 81), evaluate=False)
    assert int_expr_lean(e) == "(3 : ℤ) ^ 317 * 2 ^ 81"
    assert int_expr_lean(fact_pow(23, 129)) == "(23 : ℤ) ^ 129"


def test_exact_fact_family_certifies_and_emits_the_crux():
    # THE campaign crux: 3^317 * 2^81 <= 23^129, certified exactly then
    # emitted in unevaluated spelling with `decide`
    lhs = sp.Mul(fact_pow(3, 317), fact_pow(2, 81), evaluate=False)
    rhs = fact_pow(23, 129)
    fam = InequalityFamily(
        name="Crux",
        symbols=(),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "s_tail_crux",
        target=lambda pt: rhs.doit() - lhs.doit(),
    )
    cf = certify(fam)
    res = emit(
        cf,
        LeanProfile(),
        [ExactFactEmitter(spelling=lambda pt: (lhs, "≤", rhs), tactic="decide")],
        GREEN,
    )
    text = next(iter(res.files.values()))
    assert "theorem s_tail_crux : (3 : ℤ) ^ 317 * 2 ^ 81 ≤ (23 : ℤ) ^ 129 := by decide" in text


def test_exact_fact_spelling_mismatch_refused():
    fam = InequalityFamily(
        name="Bad",
        symbols=(),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "bad_fact",
        target=lambda pt: sp.Integer(5),
    )
    cf = certify(fam)
    with pytest.raises(ValueError, match="does not match"):
        emit(
            cf,
            LeanProfile(),
            [ExactFactEmitter(spelling=lambda pt: (sp.Integer(1), "≤", sp.Integer(2)))],
            GREEN,
        )


def test_exact_fact_refuses_symbolic_family():
    fam = InequalityFamily(
        name="Sym",
        symbols=(u,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "sym",
        target=lambda pt: 1 + u,
    )
    with pytest.raises(ValueError, match="symbol-free"):
        emit(
            certify(fam),
            LeanProfile(),
            [ExactFactEmitter(spelling=lambda pt: (sp.Integer(0), "≤", sp.Integer(1)))],
            GREEN,
        )
