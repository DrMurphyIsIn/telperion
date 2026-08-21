"""Cone/Farkas certifier — the OVERCOMPLETE-basis (underdetermined) case.

`cone_combination` solved `target = Σ λ_i b_i, λ_i ≥ 0` with `sp.solve`, which
on an OVERCOMPLETE basis returns a PARAMETRIC solution with free variables and
the certifier bailed (`"undecided over this basis — needs LP; named-open"`).
The exact basic-feasible-solution enumeration (a vertex of the weight cone,
supported on ≤ rank basis elements — the same sympy-only pattern the Handelman
finder uses) closes that gap without any SDP/LP dependency.  A genuinely
infeasible overcomplete basis is still refused (Farkas dual unaffected).
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, ValidationReport, certify,
    check_lean_text, emit,
)
from telperion.cone import cone_combination  # noqa: E402
from telperion.emit_cone import ConeFarkasEmitter, cone_family  # noqa: E402

GREEN = ValidationReport(checks=(("spot", True),))
x, y = sp.symbols("x y")


def _reproduces(cc, target):
    return cc is not None and sp.expand(cc.as_expr() - target) == 0


def test_overcomplete_basis_with_syms_is_solved():
    # (x+y)^2 over an OVERCOMPLETE basis {x^2, y^2, x*y, (x+y)^2}: 4 columns,
    # 3 monomial equations -> underdetermined; the direct solve bails, BFS finds
    # a vertex (e.g. the single (x+y)^2, or x^2 + y^2 + 2xy).
    cc = cone_combination((x + y) ** 2, [x ** 2, y ** 2, x * y, (x + y) ** 2], (x, y))
    assert _reproduces(cc, (x + y) ** 2)
    assert all(w >= 0 for w in cc.weights)


def test_overcomplete_constant_basis_is_solved():
    cc = cone_combination(sp.Integer(2), [sp.Integer(1)] * 3, ())
    assert _reproduces(cc, sp.Integer(2))
    assert all(w >= 0 for w in cc.weights)


def test_determined_case_still_works():
    cc = cone_combination(x ** 2, [x ** 2], (x,))
    assert _reproduces(cc, x ** 2) and list(cc.weights) == [1]


def test_infeasible_overcomplete_is_still_refused():
    # target has a negative pure-x^2 part no nonnegative combination can hit.
    assert cone_combination(-x ** 2, [x ** 2, y ** 2, (x + y) ** 2], (x, y)) is None


def test_is_deterministic():
    a = cone_combination((x + y) ** 2, [x ** 2, y ** 2, x * y, (x + y) ** 2], (x, y))
    b = cone_combination((x + y) ** 2, [x ** 2, y ** 2, x * y, (x + y) ** 2], (x, y))
    assert a == b


def test_certify_and_emit_overcomplete_basis():
    fam = cone_family(
        "F", (x, y), GridSpec([("i", [0])]), lambda pt: "cone_overcomplete",
        lambda pt: ((x + y) ** 2, [x ** 2, y ** 2, x * y, (x + y) ** 2]))
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [ConeFarkasEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "positivity" in body


def test_certify_refuses_infeasible_overcomplete():
    fam = cone_family(
        "B", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
        lambda pt: (-x ** 2, [x ** 2, y ** 2, (x + y) ** 2]))
    with pytest.raises(CertificationError):
        certify(fam)


def test_emitted_theorem_binds_symbols_explicitly():
    # The emitted theorem must bind its free variables with an explicit ∀ (and
    # `intro` them), not rely on Lean's autoImplicit — so it compiles under
    # `autoImplicit false` like every other emitter.
    fam = cone_family(
        "F", (x, y), GridSpec([("i", [0])]), lambda pt: "cone_bound",
        lambda pt: (x ** 2 + y ** 2, [x ** 2, y ** 2]))
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [ConeFarkasEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert "∀ x y : ℝ" in body
    assert "intro x y" in body


def test_constant_target_needs_no_binder():
    # A symbol-free family emits a bare statement (no ∀, no intro).
    z = sp.Symbol("z")  # a symbol declared but the family has none
    del z
    fam = cone_family(
        "C", (), GridSpec([("i", [0])]), lambda pt: "cone_const",
        lambda pt: (sp.Integer(2), [sp.Integer(1), sp.Integer(1)]))
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [ConeFarkasEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert "∀" not in body and "intro" not in body
