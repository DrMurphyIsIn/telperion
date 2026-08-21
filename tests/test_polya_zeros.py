"""Pólya-with-zeros (Castle–Powers–Reznick) emitter + finder.

`lift.py`'s inhomogeneous lift refuses tie-touching claims ("a zero on the
closed orthant means no finite N works").  The HOMOGENEOUS Pólya certificate
`(Σ xᵢ)^N · p = Q` with all Q-coefficients ≥ 0 tolerates zeros ON FACES —
the CPR 2011 class — and is refused exactly when the zero set leaves the face
lattice (the a=2 Castle–Powers–Reznick tie).  The finder is untrusted — the
certifier re-verifies every expansion exactly.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, PolyaZerosEmitter,
    ValidationReport, certify, check_lean_text, emit,
    find_polya_zeros_certificate, polya_zeros_family, polya_zeros_obstruction,
)

GREEN = ValidationReport(checks=(("spot", True),))
x, y = sp.symbols("x y")


def _all_coeffs_nonneg(q, syms):
    poly = sp.Poly(sp.expand(q), *syms)
    return all(c >= 0 for c in poly.coeffs())


# ---------------------------------------------------------------- finder

def test_finder_n0_when_already_nonneg_coeffs():
    assert find_polya_zeros_certificate(x ** 2 + y ** 2, (x, y), 4) == 0


def test_finder_lifts_strictly_positive_form():
    # x^2 - xy + y^2 > 0 off the origin; (x+y)*(x^2-xy+y^2) = x^3 + y^3
    n = find_polya_zeros_certificate(x ** 2 - x * y + y ** 2, (x, y), 4)
    assert n == 1
    q = sp.expand((x + y) ** n * (x ** 2 - x * y + y ** 2))
    assert _all_coeffs_nonneg(q, (x, y))


def test_finder_tolerates_zeros_on_faces():
    # xy(x^2 - xy + y^2) vanishes on BOTH faces x=0 and y=0 — the tie-safe
    # case lift.py refuses — yet lifts at N=1 to x^4 y + x y^4.
    p = x * y * (x ** 2 - x * y + y ** 2)
    n = find_polya_zeros_certificate(p, (x, y), 4)
    assert n == 1
    assert _all_coeffs_nonneg(sp.expand((x + y) ** n * p), (x, y))


def test_finder_refuses_interior_zero_tie():
    # (x-y)^2: zero ray x=y is NOT a face — CPR: no exponent exists at ANY N.
    assert find_polya_zeros_certificate((x - y) ** 2, (x, y), 6) is None


def test_finder_is_deterministic():
    p = x ** 2 - x * y + y ** 2
    assert (find_polya_zeros_certificate(p, (x, y), 4)
            == find_polya_zeros_certificate(p, (x, y), 4))


# ---------------------------------------------------------------- obstruction

def test_obstruction_flags_interior_zero():
    reason = polya_zeros_obstruction((x - y) ** 2, (x, y))
    assert reason is not None and "face" in reason


def test_obstruction_flags_negative_point():
    reason = polya_zeros_obstruction(x * y - x ** 2 - y ** 2, (x, y))
    assert reason is not None


def test_obstruction_none_for_face_zero_certificand():
    assert polya_zeros_obstruction(x * y * (x ** 2 - x * y + y ** 2), (x, y)) is None


# ---------------------------------------------------------------- certify + emit

def _family(p, n):
    return polya_zeros_family(
        "PZ", (x, y), GridSpec([("i", [0])]), lambda pt: "pz_case",
        lambda pt: (p, n))


def test_certify_supplied_exponent_and_emit():
    res = emit(certify(_family(x ** 2 - x * y + y ** 2, 1)),
               LeanProfile(namespace=("T",)), [PolyaZerosEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1
    assert "pow_pos" in body and "mul_nonneg" in body


def test_certify_refuses_insufficient_exponent():
    with pytest.raises(CertificationError):
        certify(_family(x ** 2 - x * y + y ** 2, 0))


def test_finder_mode_certifies():
    res = emit(certify(_family(x * y * (x ** 2 - x * y + y ** 2), None)),
               LeanProfile(namespace=("T",)), [PolyaZerosEmitter()], GREEN)
    assert res.n_theorems == 1


def test_finder_mode_refusal_names_the_obstruction():
    with pytest.raises(CertificationError, match="face"):
        certify(_family((x - y) ** 2, None))


def test_certify_refuses_negative_exponent():
    with pytest.raises(CertificationError):
        certify(_family(x ** 2 + y ** 2, -1))
