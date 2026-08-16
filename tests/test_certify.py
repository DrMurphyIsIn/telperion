"""Certification-layer tests: green paths, refusal paths, and the workflow gate.

The refusal paths ARE the product: a family that fails any self-check must be
un-emittable, loudly, with the offending instance named.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BoxAxis,
    CertificationError,
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    WorkflowError,
    certify,
    emit,
    polya_certify,
)
from telperion.certify import CertifiedFamily  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
q, r = sp.symbols("q r", nonnegative=True)


def direct_fam(target):
    return InequalityFamily(
        name="t",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: f"t_a{pt['a']}",
        target=target,
    )


def test_polya_certify_green():
    cert = polya_certify((1 + u) / (2 + u), (u,))
    assert sp.expand(cert.numerator - (1 + u)) == 0


def test_polya_certify_negative_numerator_refused():
    with pytest.raises(ValueError, match="numerator"):
        polya_certify((u - 1) / (2 + u), (u,))


def test_polya_certify_mixed_sign_denominator_refused():
    with pytest.raises(ValueError, match="denominator|numerator"):
        polya_certify((1 + u) / (u - 1), (u,))


def test_certify_names_failing_instance():
    fam = direct_fam(lambda pt: (u - 5) / (1 + u))
    with pytest.raises(CertificationError) as ei:
        certify(fam)
    assert ei.value.failures[0][0] == {"a": 1}


def test_duplicate_lean_names_refused():
    fam = InequalityFamily(
        name="dup",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: "same_name",
        target=lambda pt: 1 + u,
    )
    with pytest.raises(CertificationError, match="duplicate"):
        certify(fam)


def test_bilinear_nonbilinear_difference_refused():
    fam = InequalityFamily(
        name="nb",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "nb_1",
        before=lambda pt: sp.Integer(0),
        after=lambda pt: q**2 * r,
        box=lambda pt: (BoxAxis(q, sp.Integer(0), sp.Integer(1)),
                        BoxAxis(r, sp.Integer(0), sp.Integer(1))),
    )
    with pytest.raises(CertificationError, match="not bilinear"):
        certify(fam)


def test_bad_corner_refused():
    # after - before = -q: corner at q=1 is negative -> refusal
    fam = InequalityFamily(
        name="bc",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "bc_1",
        before=lambda pt: q,
        after=lambda pt: sp.Integer(0),
        box=lambda pt: (BoxAxis(q, sp.Integer(0), sp.Integer(1)),
                        BoxAxis(r, sp.Integer(0), sp.Integer(1))),
    )
    with pytest.raises(CertificationError):
        certify(fam)


def test_certified_family_not_directly_constructible():
    fam = direct_fam(lambda pt: 1 + u)
    with pytest.raises(RuntimeError, match="only be constructed"):
        CertifiedFamily(family=fam, instances=(), checks_passed=0)


def test_emit_refuses_red_validation():
    cf = certify(direct_fam(lambda pt: 1 + u))
    red = ValidationReport(checks=(("x", False),))
    with pytest.raises(WorkflowError, match="refused"):
        emit(cf, LeanProfile(), [DirectPolyaEmitter()], red)


def test_emit_refuses_non_witness():
    with pytest.raises(WorkflowError, match="witness"):
        emit(object(), LeanProfile(), [DirectPolyaEmitter()],
             ValidationReport(checks=(("x", True),)))


def test_emit_refuses_missing_prelude_dependency():
    # The bilinear assembly calls `bilinear_corner_nonneg`; a profile that does
    # not define it (bare LeanProfile) must be refused LOCALLY, not shipped to
    # fail in `lake build` (the H-floor missing-prelude incident, 2026-08-16).
    from telperion import BilinearBoxEmitter

    fam = InequalityFamily(
        name="mp",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "mp_1",
        before=lambda pt: sp.Integer(0),
        after=lambda pt: q + r,
        box=lambda pt: (BoxAxis(q, sp.Integer(0), sp.Integer(1)),
                        BoxAxis(r, sp.Integer(0), sp.Integer(1))),
    )
    cf = certify(fam)
    good = ValidationReport(checks=(("x", True),))
    with pytest.raises(WorkflowError, match="bilinear_corner_nonneg"):
        emit(cf, LeanProfile(), [BilinearBoxEmitter()], good)
    # and PASSES once the profile provides it
    ok = emit(cf, LeanProfile(prelude="theorem bilinear_corner_nonneg := trivial"),
              [BilinearBoxEmitter()], good)
    assert ok.n_theorems >= 1


def test_validation_from_asserts_raises_and_records():
    def bad():
        raise AssertionError("boom")

    with pytest.raises(WorkflowError, match="validation failed"):
        ValidationReport.from_asserts([("ok", lambda: None), ("bad", bad)])
