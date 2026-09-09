"""NS/Euler wave-4 emitters (two_row_solve, ratio_telescope, monomial_ladder,
rpow_budget): certify → emit → lint + refusal negative controls."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    monomial_ladder_certificate, monomial_ladder_family,
    ratio_telescope_family,
    rpow_budget_certificate, rpow_budget_family,
    two_row_solve_family,
)
from telperion.emit_monomial_ladder import MonomialLadderEmitter  # noqa: E402
from telperion.emit_ratio_telescope import RatioTelescopeEmitter  # noqa: E402
from telperion.emit_rpow_budget import RpowBudgetEmitter  # noqa: E402
from telperion.emit_two_row_solve import TwoRowSolveEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text

_VR = ValidationReport(checks=(("s", True),))
_G = GridSpec([("k", [0])])


def _emit(fam, em, ns):
    return emit(certify(fam), LeanProfile(namespace=("NS", ns)), [em], _VR)


# --- two_row_solve ---------------------------------------------------------- #

def test_two_row_solve_atom():
    fam = two_row_solve_family(name="TRChk", grid=_G, lean_name=lambda pt: "tr")
    assert fam.kind == "two_row_solve"
    text = _emit(fam, TwoRowSolveEmitter(), "TR").files["TRChk.lean"]
    assert "theorem two_row_solve_bound" in text
    assert "Rmax" in text  # the generalized ceiling
    check_lean_text(text)


# --- ratio_telescope -------------------------------------------------------- #

def test_ratio_telescope_atoms():
    fam = ratio_telescope_family(name="RTChk", grid=_G, lean_name=lambda pt: "rt")
    assert fam.kind == "ratio_telescope"
    res = _emit(fam, RatioTelescopeEmitter(), "RT")
    text = res.files["RTChk.lean"]
    for nm in ("ratio_factorial_telescope", "ratio_geometric_reciprocal",
               "ratio_index_domination"):
        assert f"theorem {nm}" in text
    assert res.n_theorems == 3
    check_lean_text(text)


# --- monomial_ladder -------------------------------------------------------- #

def test_monomial_ladder_certifies_and_emits():
    # master Cm=1000000, Kmax=40; rung (800, 5, 1/2): 800 ≤ 1000000·(1/2) ✓
    fam = monomial_ladder_family(
        name="MLChk", grid=_G, lean_name=lambda pt: "guard",
        spec=lambda pt: (1000000, 40, [(800, 5, sp.Rational(1, 2)), (8, 21, 1)]))
    text = _emit(fam, MonomialLadderEmitter(), "ML").files["MLChk.lean"]
    assert "theorem guard_rung1" in text and "theorem guard_rung2" in text
    assert "pow_le_pow_right₀" in text
    check_lean_text(text)


def test_monomial_ladder_refusals():
    with pytest.raises(ValueError, match="c ≤ Cm·b"):
        monomial_ladder_certificate(10, 5, [(100, 3, sp.Rational(1, 2))])  # 100 > 5
    with pytest.raises(ValueError, match="exponent"):
        monomial_ladder_certificate(10, 5, [(1, 6, 1)])  # k > Kmax
    with pytest.raises(ValueError, match="Cm > 0"):
        monomial_ladder_certificate(0, 5, [(1, 3, 1)])


# --- rpow_budget ------------------------------------------------------------ #

def test_rpow_budget_source_instance():
    # source shape: a = [1/2, 102/100], r = -99/100, N0 = 5, t = -21/5 (=-(7/10)*6)
    cert = rpow_budget_certificate(
        4, [sp.Rational(1, 2), sp.Rational(102, 100)], sp.Rational(-99, 100),
        5, sp.Rational(-21, 5))
    assert sum(cert.a) + cert.r * (cert.N0 + 1) <= cert.t


def test_rpow_budget_emits():
    fam = rpow_budget_family(
        name="RBChk", grid=_G, lean_name=lambda pt: "tail_budget",
        spec=lambda pt: (4, [sp.Rational(1, 2), sp.Rational(102, 100)],
                         sp.Rational(-99, 100), 5, sp.Rational(-21, 5)))
    text = _emit(fam, RpowBudgetEmitter(), "RB").files["RBChk.lean"]
    assert "theorem tail_budget" in text
    assert "Real.rpow_le_rpow_of_exponent_le" in text
    assert "Real.rpow_mul_natCast" in text
    check_lean_text(text)


def test_rpow_budget_refusals():
    with pytest.raises(ValueError, match="margin"):
        rpow_budget_certificate(4, [2], sp.Rational(-1, 10), 0, 0)  # 2 - 1/10 > 0
    with pytest.raises(ValueError, match="r < 0"):
        rpow_budget_certificate(4, [1], 0, 0, 10)
    with pytest.raises(ValueError, match="kmin"):
        rpow_budget_certificate(sp.Rational(1, 2), [1], -1, 0, 10)


# --- byte stability across all four ---------------------------------------- #

def test_byte_stability():
    fam = monomial_ladder_family(
        name="MLChk", grid=_G, lean_name=lambda pt: "guard",
        spec=lambda pt: (100, 10, [(50, 3, 1)]))
    a = _emit(fam, MonomialLadderEmitter(), "ML").files["MLChk.lean"]
    b = _emit(fam, MonomialLadderEmitter(), "ML").files["MLChk.lean"]
    assert a == b
