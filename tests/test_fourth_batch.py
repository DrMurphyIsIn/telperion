"""Fourth batch: hole contracts, cost ledger, adequacy, varmaps, dichotomy,
and the gate negative-controls."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    DichotomyGlueEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    MapSpec,
    TemplateError,
    ValidationReport,
    VarMapAdapterEmitter,
    certify,
    emit,
    profile_report,
)
from telperion.lean import render  # noqa: E402
from telperion.lint import LintError, lint_files  # noqa: E402
from telperion.margins import bracket_adequacy  # noqa: E402

u = sp.Symbol("u", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


def fam2():
    return InequalityFamily(
        name="F4",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"f4_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


# ---- N: typed hole contracts ------------------------------------------------
def test_empty_binder_is_unconstructible():
    with pytest.raises(TemplateError, match="EMPTY BINDER"):
        render("theorem «name» «binders» : True := trivial",
               {"name": "ok", "binders": "( : ℝ)"})


def test_name_hole_rejects_non_identifier():
    with pytest.raises(TemplateError, match="not a Lean identifier"):
        render("theorem «name» : True := trivial", {"name": "bad name!"})


def test_unbalanced_binder_rejected():
    with pytest.raises(TemplateError, match="unbalanced"):
        render("theorem «name» «binders» : True := trivial",
               {"name": "ok", "binders": "(u : ℝ"})


def test_empty_binders_fill_is_fine():
    out = render("theorem «name» «binders» : True := trivial",
                 {"name": "ok", "binders": ""})
    assert "theorem ok  : True" in out


# ---- O: cost ledger ---------------------------------------------------------
def test_profile_records_timings():
    cf = certify(fam2(), profile=True)
    assert len(cf.timings) == 2
    assert all(dt >= 0 for _, dt in cf.timings)
    rep = profile_report(cf)
    assert "certified 2 instance(s)" in rep and "hottest" in rep


def test_budget_aborts_with_hot_report():
    big = InequalityFamily(
        name="Slow",
        symbols=(u,),
        grid=GridSpec([("a", list(range(1, 200)))]),
        lean_name=lambda pt: f"slow_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) ** 3 / (u + 1) ** 2 / (u + 2),
    )
    with pytest.raises(CertificationError, match="BUDGET EXCEEDED"):
        certify(big, profile=True, budget_seconds=0.05)


# ---- S: bracket adequacy ----------------------------------------------------
def test_adequacy_flags_thin_margin():
    from telperion import interval_family

    rho = sp.Symbol("rho", nonnegative=True)
    fam = interval_family(
        name="Adeq",
        symbols=(),
        grid=GridSpec([("i", [0, 1])]),
        lean_name=lambda pt: f"adeq_{pt['i']}",
        # cell 0: margin tiny vs width (FRAGILE); cell 1: comfortable
        target=lambda pt: (
            rho - sp.Rational(999999, 1000000) if pt["i"] == 0 else rho
        ),
        brackets={rho: (sp.Integer(1), sp.Integer(2))},
    )
    rows = bracket_adequacy(certify(fam))
    assert rows[0].lean_name == "adeq_0"
    assert rows[0].slack_ratio < 1          # fragile first
    assert rows[1].slack_ratio >= 1


# ---- P: varmap adapters -----------------------------------------------------
def test_varmap_adapter_renders_general_glue():
    cf = certify(fam2())
    em = VarMapAdapterEmitter(
        spec=lambda inst: MapSpec(
            binders="(n : ℕ) (h2 : 2 ≤ n)",
            body="(1 : ℝ)",  # stand-in original-variable body
            eqs=(("e1", "((n : ℝ) - 2)", "((n - 2 : ℕ) : ℝ)",
                  "push_cast [Nat.cast_sub h2]\n    ring"),),
            images=(("himg", "((n - 2 : ℕ) : ℝ)", "positivity"),),
            call="((n - 2 : ℕ) : ℝ) himg",
        ),
    )
    res = emit(cf, LeanProfile(), [em], GREEN)
    text = next(iter(res.files.values()))
    assert "theorem f4_a1_orig (n : ℕ) (h2 : 2 ≤ n)" in text
    assert "have e1 : ((n : ℝ) - 2) = ((n - 2 : ℕ) : ℝ)" in text
    assert "rw [e1]" in text
    assert "exact f4_a1 ((n - 2 : ℕ) : ℝ) himg" in text


# ---- Q: dichotomy glue ------------------------------------------------------
def test_dichotomy_glue_case_split():
    cf = certify(fam2())
    em = DichotomyGlueEmitter(
        theorem_name="f4_dichotomy",
        binders="(z T : ℝ) (hz : 0 ≤ z)",
        claim="0 ≤ z * T",
        lhs="23 * z", rhs="3 + 3 * T",
        left_call="light_top z T hz h",
        right_call="heavy_top z T hz h",
    )
    res = emit(cf, LeanProfile(), [em], GREEN)
    text = next(iter(res.files.values()))
    assert "rcases le_total 23 * z 3 + 3 * T with h | h" in text
    assert "exact light_top z T hz h" in text
    assert "exact heavy_top z T hz h" in text


# ---- R: gate negative-controls ---------------------------------------------
GOLDEN_BAD = {
    "empty_binder": "/- telperion x -/\nnoncomputable def c1 ( : ℝ) : ℝ := 1\n",
    "hole_marker": "/- telperion x -/\ntheorem a : «oops» := rfl\n",
    "unbalanced": "/- telperion x -/\ntheorem a : (1 = 1 := rfl\n",
    "no_header": "theorem a : True := trivial\n",
}


@pytest.mark.parametrize("kind", sorted(GOLDEN_BAD))
def test_gate_negative_controls_lint(kind):
    """Every known-bad artifact class must go RED in lint — silence from a
    gate is indistinguishable from safety (REVIEW_20260816_TELPERION_G1)."""
    with pytest.raises(LintError):
        lint_files({f"{kind}.lean": GOLDEN_BAD[kind]})


def test_gate_negative_control_recheck_tamper():
    from telperion.interchange import export_certificates
    from telperion.recheck import recheck

    doc = export_certificates(certify(fam2()), "0" * 64)
    key = next(iter(doc["instances"][0]["corners"][0]["numerator"]))
    doc["instances"][0]["corners"][0]["numerator"][key] = "1000000/1"
    assert recheck(doc, trials=10)   # nonempty problem list


def test_gate_negative_control_drift(tmp_path):
    from telperion import DirectPolyaEmitter, diff_frozen, freeze

    from telperion import emit as _emit

    res = _emit(certify(fam2()), LeanProfile(), [DirectPolyaEmitter()], GREEN)
    freeze(res, tmp_path)
    fname = next(iter(res.files))
    (tmp_path / fname).write_text(
        (tmp_path / fname).read_text().replace("0 ≤", "0 <", 1)
    )
    assert not diff_frozen(res, tmp_path).ok
