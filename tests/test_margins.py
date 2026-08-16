"""Tie-variety extraction and margin report tests."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import GridSpec, InequalityFamily, certify  # noqa: E402
from telperion.margins import margin_report, tie_faces, tie_points  # noqa: E402

u, v, w = sp.symbols("u v w", nonnegative=True)


# ---- tie faces (certified / nonneg-coefficient numerators) ------------------
def test_positive_constant_term_means_no_ties():
    assert tie_faces(1 + u + u * v, (u, v)) == []


def test_product_monomial_gives_union_of_faces():
    faces = tie_faces(u * v + u**2 * v, (u, v))
    assert sorted(tuple(str(s) for s in f) for f in faces) == [("u",), ("v",)]


def test_sum_of_variables_gives_corner_face():
    faces = tie_faces(u + v, (u, v))
    assert [tuple(str(s) for s in f) for f in faces] == [("u", "v")]


def test_mixed_supports_minimal_hitting_sets():
    # u*v + u*w + v*w: minimal hitting sets are any two of the three variables
    faces = tie_faces(u * v + u * w + v * w, (u, v, w))
    got = sorted(tuple(str(s) for s in f) for f in faces)
    assert got == [("u", "v"), ("u", "w"), ("v", "w")]


def test_tie_faces_refuses_mixed_sign():
    with pytest.raises(ValueError):
        tie_faces(u - 1, (u,))


# ---- tie points (mixed-sign numerators) -------------------------------------
def test_univariate_exact_roots_deduped():
    pts = tie_points((u - 1) ** 2 * (u - 3) ** 2, (u,))
    assert [p["u"] for p in pts] == [1, 3]


def test_univariate_negative_roots_filtered():
    pts = tie_points((u + 2) * (u - sp.Rational(1, 2)), (u,))
    assert [p["u"] for p in pts] == [sp.Rational(1, 2)]


# ---- margin reports ---------------------------------------------------------
def test_margin_report_flags_tight_instance_first():
    fam = InequalityFamily(
        name="M",
        symbols=(u, v),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"M_a{pt['a']}",
        # a=1: tie faces (num = u*v); a=2: strictly positive (num has +1)
        target=lambda pt: (u * v if pt["a"] == 1 else 1 + u * v) / (1 + u),
    )
    reports = margin_report(certify(fam), samples=10)
    assert reports[0].lean_name == "M_a1"
    assert reports[0].is_tight
    assert reports[0].empirical_min == 0          # attained exactly at a sample
    assert [tuple(str(s) for s in f) for f in reports[0].ties] == [("u",), ("v",)]
    assert not reports[1].is_tight
    assert reports[1].constant_term == 1


def test_margin_report_bilinear_labels_corners():
    q, r = sp.symbols("q r", nonnegative=True)
    from telperion import BoxAxis

    za, zb = sp.Integer(1) / (2 + u), sp.Integer(1) / (2 + v)
    delta = sp.Integer(1) / ((2 + u) * (2 + v))
    fam = InequalityFamily(
        name="MB",
        symbols=(u, v),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "MB_a1",
        before=lambda pt: (1 + za * q) * (1 + zb * r),
        after=lambda pt: 1 + delta + (za / 2) * q + (zb / 2) * r + 2 * za * zb * q * r,
        box=lambda pt: (
            BoxAxis(q, sp.Integer(0), sp.Integer(1) / (2 + v)),
            BoxAxis(r, sp.Integer(0), sp.Integer(1) / (2 + u)),
        ),
    )
    reports = margin_report(certify(fam), samples=5)
    assert {r_.corner for r_ in reports} == {"00", "01", "10", "11"}
    assert all(not r_.is_tight for r_ in reports)
