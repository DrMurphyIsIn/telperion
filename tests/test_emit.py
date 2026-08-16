"""Emission tests: determinism, provenance stamps, freeze/diff drift detection,
and golden-shape assertions on the rendered Lean."""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    BoxAxis,
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)

u, v = sp.symbols("u v", nonnegative=True)
q, r = sp.symbols("r q", nonnegative=True)[::-1]

GREEN = ValidationReport(checks=(("stub", True),))


def small_direct():
    return InequalityFamily(
        name="gold",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"gold_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


def small_box():
    za = sp.Integer(1) / (2 + u)
    zb = sp.Integer(1) / (2 + v)
    delta = sp.Integer(1) / ((2 + u) * (2 + v))
    return InequalityFamily(
        name="goldbox",
        symbols=(u, v),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "goldbox_a1",
        before=lambda pt: (1 + za * q) * (1 + zb * r),
        after=lambda pt: 1 + delta + (za / 2) * q + (zb / 2) * r + 2 * za * zb * (q * r),
        box=lambda pt: (
            BoxAxis(q, sp.Integer(0), sp.Integer(1) / (2 + v)),
            BoxAxis(r, sp.Integer(0), sp.Integer(1) / (2 + u)),
        ),
    )


def test_emit_deterministic():
    cf = certify(small_direct())
    r1 = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    r2 = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    assert r1.files == r2.files
    assert r1.input_hash == r2.input_hash


def test_header_carries_hash_and_counts():
    cf = certify(small_direct())
    res = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    text = next(iter(res.files.values()))
    assert res.input_hash[:16] in text
    assert "2 theorems" in text
    assert "DO NOT EDIT BY HAND" in text


def test_profile_shapes_output():
    cf = certify(small_direct())
    prof = LeanProfile(
        namespace=("A", "B"),
        imports=("Mathlib", "My.Prelude"),
        options=("set_option maxHeartbeats 1000000",),
        prelude="-- user prelude here",
    )
    text = next(iter(emit(cf, prof, [DirectPolyaEmitter()], GREEN).files.values()))
    assert "import My.Prelude" in text
    assert "namespace A" in text and "namespace B" in text
    assert text.rstrip().endswith("end A")
    assert "maxHeartbeats" in text
    assert "-- user prelude here" in text


def test_bilinear_emits_all_pieces():
    cf = certify(small_box())
    res = emit(cf, LeanProfile(), [BilinearBoxEmitter()], GREEN)
    text = next(iter(res.files.values()))
    for piece in (
        "goldbox_a1c1", "goldbox_a1c4", "goldbox_a1_bilinear",
        "goldbox_a1_corner00", "goldbox_a1_corner11", "goldbox_a1_cell",
        "bilinear_corner_nonneg",
    ):
        assert piece in text, piece
    assert res.n_theorems == 6


def test_freeze_then_diff_green_then_drift(tmp_path):
    cf = certify(small_direct())
    res = emit(cf, LeanProfile(), [DirectPolyaEmitter()], GREEN)
    freeze(res, tmp_path)
    assert diff_frozen(res, tmp_path).ok
    # tamper -> drift flagged
    fname = next(iter(res.files))
    p = tmp_path / fname
    p.write_text(p.read_text().replace("0 ≤", "0 ≤ ", 1))
    rep = diff_frozen(res, tmp_path)
    assert not rep.ok
    assert any("content drift" in d for d in rep.details)


def test_family_change_changes_hash(tmp_path):
    res1 = emit(certify(small_direct()), LeanProfile(), [DirectPolyaEmitter()], GREEN)
    fam2 = InequalityFamily(
        name="gold",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"gold_a{pt['a']}",
        target=lambda pt: (pt["a"] + 2 * u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )
    res2 = emit(certify(fam2), LeanProfile(), [DirectPolyaEmitter()], GREEN)
    assert res1.input_hash != res2.input_hash
    freeze(res1, tmp_path)
    rep = diff_frozen(res2, tmp_path)
    assert not rep.ok
    assert any("hash drift" in d for d in rep.details)
