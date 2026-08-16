"""Hardening tests: lint gate, sharding, diagnose triage."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
)
from telperion.diagnose import diagnose_expr, find_counterexample  # noqa: E402
from telperion.lint import LintError, lint_files  # noqa: E402
from telperion.workflow import ShardSpec  # noqa: E402

u = sp.Symbol("u", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


def famN(n):
    return InequalityFamily(
        name="Sharded",
        symbols=(u,),
        grid=GridSpec([("a", list(range(1, n + 1)))]),
        lean_name=lambda pt: f"sh_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


# ---- lint -------------------------------------------------------------------
def test_lint_catches_unfilled_hole():
    with pytest.raises(LintError, match="hole"):
        lint_files({"X.lean": "/- telperion x -/\ntheorem a : «oops» := rfl\n"})


def test_lint_catches_duplicate_names_across_files():
    a = "/- telperion x -/\ntheorem dup : True := trivial\n"
    with pytest.raises(LintError, match="duplicate"):
        lint_files({"A.lean": a, "B.lean": a})


def test_lint_catches_unbalanced_parens():
    with pytest.raises(LintError, match="unclosed"):
        lint_files({"X.lean": "/- telperion x -/\ntheorem a : (1 = 1 := rfl\n"})


# ---- sharding ---------------------------------------------------------------
def test_shard_splits_and_imports():
    cf = certify(famN(7))
    res = emit(
        cf,
        LeanProfile(namespace=("S",), prelude="-- prelude lives only in shard 1"),
        [DirectPolyaEmitter()],
        GREEN,
        shard=ShardSpec(max_theorems=3, module_base="S.Cells"),
    )
    assert sorted(res.files) == ["Cells.lean", "Cells2.lean", "Cells3.lean"]
    assert "-- prelude lives only in shard 1" in res.files["Cells.lean"]
    assert "prelude" not in res.files["Cells2.lean"]
    assert "import S.Cells\n" in res.files["Cells2.lean"]
    assert "import S.Cells\n" in res.files["Cells3.lean"]
    assert "import S.Cells2" in res.files["Cells3.lean"]
    assert res.n_theorems == 7
    # every theorem present exactly once across shards
    all_text = "".join(res.files.values())
    for a in range(1, 8):
        assert all_text.count(f"theorem sh_a{a} ") == 1


def test_shard_config_changes_hash():
    cf = certify(famN(4))
    r1 = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    r2 = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN,
              shard=ShardSpec(max_theorems=2, module_base="S.C"))
    assert r1.input_hash != r2.input_hash


# ---- diagnose ---------------------------------------------------------------
def test_diagnose_false_finds_witness():
    d = diagnose_expr(u - 3, (u,))
    assert d.verdict == "FALSE"
    assert d.counterexample is not None


def test_diagnose_nonpolya_hints_even_power():
    d = diagnose_expr((u - 1) ** 2 / (u + 1), (u,))
    assert d.verdict == "NOT_POLYA_IN_THIS_FORM"
    assert any("even power" in h for h in d.hints)


def test_diagnose_certifiable():
    d = diagnose_expr((1 + u) / (2 + u), (u,))
    assert d.verdict == "CERTIFIABLE"


def test_counterexample_is_exact():
    wit = find_counterexample(u - sp.Rational(1, 3), (u,))
    assert wit is not None
    val = (u - sp.Rational(1, 3)).subs({u: wit["u"]})
    assert val < 0  # exact rational, no float artifact
