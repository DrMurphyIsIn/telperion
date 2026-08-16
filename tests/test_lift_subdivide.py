"""Pólya lift + subdivision engine tests."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    BoxAxis,
    CertificationError,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    SubdivisionGlueEmitter,
    ValidationReport,
    certify,
    emit,
    polya_certify,
)
from telperion.lift import polya_lift  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
q, r = sp.symbols("q r", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


# ---- lifting ----------------------------------------------------------------
def test_lift_finds_minimal_n():
    n, lifted = polya_lift(u**2 - u + 1, (u,), 4)
    assert n == 1
    assert sp.expand(lifted - (u**3 + 1)) == 0


def test_lift_zero_at_tie_never_converges():
    assert polya_lift((u - 1) ** 2, (u,), 10) is None


def test_polya_certify_with_lift():
    cert = polya_certify((u**2 - u + 1) / (u + 1), (u,), lift_max=3)
    assert cert.lift_n == 1
    assert sp.expand(cert.numerator - (u**3 + 1)) == 0
    # the lifted pair is still a faithful certificate
    assert sp.simplify(cert.numerator / cert.denominator - (u**2 - u + 1) / (u + 1)) == 0


def test_polya_certify_without_lift_still_refuses():
    with pytest.raises(ValueError):
        polya_certify((u**2 - u + 1) / (u + 1), (u,))


def test_family_auto_lift_end_to_end():
    fam = InequalityFamily(
        name="L",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"L_a{pt['a']}",
        target=lambda pt: (u**2 - u + pt["a"]) / (u + 1),
        auto_lift=3,
    )
    cf = certify(fam)
    assert all(inst.corners[0].lift_n == 1 for inst in cf.instances)
    # without the knob: refused
    fam0 = InequalityFamily(
        name="L0",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "L0_a1",
        target=lambda pt: (u**2 - u + 1) / (u + 1),
    )
    with pytest.raises(CertificationError):
        certify(fam0)


# ---- subdivision ------------------------------------------------------------
def _box_fam():
    za = sp.Integer(1) / (2 + u)
    zb = sp.Integer(1) / (2 + v)
    delta = sp.Integer(1) / ((2 + u) * (2 + v))
    return InequalityFamily(
        name="S",
        symbols=(u, v),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "S_a1",
        before=lambda pt: (1 + za * q) * (1 + zb * r),
        after=lambda pt: 1 + delta + (za / 2) * q + (zb / 2) * r + 2 * za * zb * (q * r),
        box=lambda pt: (
            BoxAxis(q, sp.Integer(0), sp.Integer(1) / (2 + v)),
            BoxAxis(r, sp.Integer(0), sp.Integer(1) / (2 + u)),
        ),
    )


def test_force_subdivide_builds_tree_and_leaves():
    cf = certify(_box_fam(), force_subdivide=1)
    names = sorted(i.lean_name for i in cf.instances)
    assert names == ["S_a1_qL", "S_a1_qR"]
    assert len(cf.subdivisions) == 1
    tree = cf.subdivisions[0]
    assert tree["axis"] == "q"
    assert [c["name"] for c in tree["children"]] == ["S_a1_qL", "S_a1_qR"]
    # right child's lower bound is the midpoint, stated as a floor
    right = cf.instances[[i.lean_name for i in cf.instances].index("S_a1_qR")]
    assert right.decomposition.q_axis.lo_is_floor


def test_glue_emits_le_total_case_split():
    cf = certify(_box_fam(), force_subdivide=1)
    res = emit(cf, LeanProfile(prelude="theorem bilinear_corner_nonneg : True := trivial"),
               [BilinearBoxEmitter(), SubdivisionGlueEmitter()], GREEN)
    text = next(iter(res.files.values()))
    assert "theorem S_a1_cell " in text
    assert "rcases le_total q" in text
    assert "exact S_a1_qL_cell u v q r hu hv hQ0 h hS0 hS1" in text
    assert "exact S_a1_qR_cell u v q r hu hv h hQ1 hS0 hS1" in text
    # leaves come before the glue that references them
    assert text.index("S_a1_qL_cell ") < text.index("theorem S_a1_cell ")


def test_deep_force_subdivide_alternates_axes():
    cf = certify(_box_fam(), force_subdivide=2)
    assert len(cf.instances) == 4
    assert any("_rL" in i.lean_name or "_rR" in i.lean_name for i in cf.instances)
