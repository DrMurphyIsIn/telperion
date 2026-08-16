"""Kind-2/3 emitter tests: rendering shapes, hash sensitivity, guard rails."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CaseDispatchAssemblyEmitter,
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    Reparam,
    ReparamAdapterEmitter,
    ValidationReport,
    certify,
    emit,
)

u, q, r = sp.symbols("u q r", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


def fam3():
    return InequalityFamily(
        name="adapt",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"adapt_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


def _rp(inst) -> Reparam:
    return Reparam(
        nat_binders="(n : ℕ) (h1 : 1 ≤ n)",
        nat_body="((n : ℝ) - 1)",
        cast_eq=("((n : ℝ) - 1)", "((n - 1 : ℕ) : ℝ)"),
        cast_lemmas=("Nat.cast_sub h1",),
        image="((n - 1 : ℕ) : ℝ)",
    )


def test_reparam_renders_cast_shape():
    res = emit(certify(fam3()), LeanProfile(),
               [ReparamAdapterEmitter(reparam=_rp)], GREEN)
    text = next(iter(res.files.values()))
    assert text.count("push_cast [Nat.cast_sub h1]") == 3
    assert "exact adapt_a1 ((n - 1 : ℕ) : ℝ)" in text
    assert "adapt_a3_nat" in text


def test_assembly_substitutes_axis_and_literals():
    asm = CaseDispatchAssemblyEmitter(
        name="adapt_all", axis="a",
        binders="(a : ℕ) (h1 : 1 ≤ a) (h3 : a ≤ 3) (u : ℝ) (hu : 0 ≤ u)",
        body_template="(«axisR» + u) / (u + 1) - «axisR» / (u + 2)",
    )
    res = emit(certify(fam3()), LeanProfile(), [asm], GREEN)
    text = next(iter(res.files.values()))
    assert "((a : ℝ) + u) / (u + 1) - (a : ℝ) / (u + 2)" in text
    assert "(3 + u) / (u + 1) - 3 / (u + 2)" in text
    assert text.count("· push_cast") == 3
    assert "interval_cases a" in text


def test_assembly_rejects_multi_axis_and_bilinear():
    multi = InequalityFamily(
        name="m", symbols=(u,),
        grid=GridSpec([("a", [1]), ("b", [1])]),
        lean_name=lambda pt: f"m_{pt['a']}{pt['b']}",
        target=lambda pt: 1 + u,
    )
    asm = CaseDispatchAssemblyEmitter(body_template="x")
    with pytest.raises(ValueError, match="single grid axis"):
        emit(certify(multi), LeanProfile(), [asm], GREEN)


def test_emitter_config_changes_hash():
    cf = certify(fam3())
    r1 = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    r2 = emit(cf, LeanProfile(),
              [DirectPolyaEmitter(), ReparamAdapterEmitter(reparam=_rp)], GREEN)
    assert r1.input_hash != r2.input_hash
