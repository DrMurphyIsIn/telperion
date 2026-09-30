"""Tests for the mobius_tangent_cell emitter (tangent-line cells with a Mobius term).

Offline (no Lean): the exact template split, every refusal, the soundness of the rational
`log u <= H` bounds (against mpmath at 50 digits), Layer-1 rejection of tampered cells and
tilings, the emitted Lean text, the family/certify registration, and the dogfood drift
check.  The kernel run is the dogfood `lake build` (examples/mobius_tangent_cell/lean).

conjecture1_proved = False.
"""
import subprocess
import sys
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

import mpmath  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_mobius_tangent_cell import (  # noqa: E402
    H_DIGITS,
    MobiusTangentCellCert,
    MobiusTangentCellEmitter,
    MobiusTangentRefusal,
    check_cell,
    check_tiling,
    log_upper,
    mobius_tangent_cell_certificate,
    mobius_tangent_cell_family,
    mobius_tangent_problem,
    problem_from_sides,
    split_pow2,
    verify_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

x = sp.Symbol("x")
mpmath.mp.dps = 50


def _pade(p="1/4", q="1"):
    return problem_from_sides(sp.log(1 + x), x * (6 + x) / (6 + 4 * x), x, p, q)


def _concave():
    return problem_from_sides(sp.log(sp.Rational(1, 4) + x) + sp.Rational(1, 2) * sp.log(3 + x),
                              x + 1 / (2 * (1 + x)) - sp.Rational(8, 25), x, 0, 2)


def _logmean(p="1/4", q="1/2"):
    return mobius_tangent_problem(a=-2, logs=[(1, 0, 1)], sigma=4, B=1, A=1, p=p, q=q)


# --- the template split ------------------------------------------------------------

def test_pade_split_is_exact():
    pr = _pade()
    assert (pr.a, pr.b, pr.sigma, pr.B, pr.A) == (Fr(-9, 8), Fr(-1, 4), 27, 24, 16)
    assert len(pr.logs) == 1 and (pr.logs[0].kappa, pr.logs[0].alpha, pr.logs[0].beta) == (1, 1, 1)


def test_two_logs_and_negative_sigma_split():
    pr = _concave()
    assert pr.sigma == -1 and (pr.B, pr.A) == (2, 2)
    assert sorted((lt.kappa, lt.alpha, lt.beta) for lt in pr.logs) == [
        (Fr(1, 2), 3, 1), (1, Fr(1, 4), 1)]


def test_denominator_sign_is_normalised_positive():
    # 1/(1 - x) on [2, 3] has a negative denominator: sign moves into sigma
    pr = problem_from_sides(sp.log(x), 1 / (1 - x) + 5, x, 2, 3)
    assert pr.B + pr.A * 2 > 0 and pr.B + pr.A * 3 > 0
    assert sp.simplify(sp.log(x) - 1 / (1 - x) - 5 - (
        pr.a + pr.b * x + sp.log(x) + sp.Rational(pr.sigma.numerator, pr.sigma.denominator)
        / (sp.Rational(pr.B.numerator, pr.B.denominator)
           + sp.Rational(pr.A.numerator, pr.A.denominator) * x))) == 0


# --- refusals -----------------------------------------------------------------------

@pytest.mark.parametrize("kw, frag", [
    (dict(logs=[(-1, 1, 1)], p=0, q=1), "CONVEX"),
    (dict(logs=[(0, 1, 1)], p=0, q=1), "vacuous"),
    (dict(logs=[], p=0, q=1), "no log term"),
    (dict(logs=[(1, 1, 1)], p=1, q=1), "degenerate"),
    (dict(logs=[(1, 1, 1)], p=0.5, q=1), "float"),
    (dict(logs=[(1, -1, 1)], p=0, q=2), "log argument"),
    (dict(logs=[(1, 1, 1)], sigma=1, B=1, A=-1, p=0, q=2), "must not change"),
])
def test_problem_refusals(kw, frag):
    with pytest.raises(MobiusTangentRefusal, match=frag):
        mobius_tangent_problem(**kw)


def test_convex_log_lower_bound_does_not_fit():
    """log(1 + x) >= 2x/(2 + x), i.e. 2x/(2+x) - log(1+x) <= 0: kappa = -1, refused."""
    with pytest.raises(MobiusTangentRefusal, match="CONVEX"):
        problem_from_sides(2 * x / (2 + x), sp.log(1 + x), x, 0, 1)


@pytest.mark.parametrize("lhs, rhs, frag", [
    (sp.log(1 + x ** 2), x, "not affine"),
    (sp.log(1 + x), 1 / (1 + x) + 1 / (2 + x), "more than one Mobius"),
    (sp.log(1 + x), 1 / (1 + x) ** 2, "single simple pole"),
    (sp.log(1 + x), x ** 2, "degree > 1"),
    (sp.log(1 + x) * x, x, "rational"),
])
def test_sides_refusals(lhs, rhs, frag):
    with pytest.raises(MobiusTangentRefusal, match=frag):
        problem_from_sides(lhs, rhs, x, 1, 2)


def test_false_claim_is_refused_as_false():
    pr = mobius_tangent_problem(a=Fr(-19, 10), logs=[(1, 0, 1)], sigma=4, B=1, A=1,
                                p="1/4", q="1/2")
    with pytest.raises(MobiusTangentRefusal, match="FALSE"):
        mobius_tangent_cell_certificate(pr, max_depth=6)


def test_pade_tight_at_zero_is_refused():
    """F vanishes to order 4 at 0; the majorant loses a quadratic term: no cell at 0 passes."""
    with pytest.raises(MobiusTangentRefusal, match="tight to order"):
        mobius_tangent_cell_certificate(_pade("0", "1"), max_depth=6)


def test_cell_cap_refusal():
    with pytest.raises(MobiusTangentRefusal, match="more than 3 cells"):
        mobius_tangent_cell_certificate(_pade(), max_cells=3)


# --- the log constant bound ------------------------------------------------------------

@pytest.mark.parametrize("u", [Fr(1), Fr(2), Fr(4), Fr(1, 5), Fr(7, 16), Fr(323, 256),
                               Fr(19, 4), Fr(2, 3), Fr(4, 3), Fr(1000, 3), Fr(1, 1000)])
def test_log_upper_is_an_upper_bound(u):
    n, v = split_pow2(u)
    assert Fr(2, 3) <= v < Fr(4, 3) and v * Fr(2) ** n == u
    for order in (1, 2, 5, 12):
        bd = log_upper(u, order)
        H = mpmath.mpf(bd.H.numerator) / bd.H.denominator
        assert mpmath.log(mpmath.mpf(u.numerator) / u.denominator) <= H
        assert bd.H.denominator <= 10 ** H_DIGITS


def test_log_upper_tightens_with_order():
    u = Fr(323, 256)
    gaps = [float(log_upper(u, n).H) - float(mpmath.log(mpmath.mpf(323) / 256))
            for n in (1, 4, 8)]
    assert gaps[0] > gaps[1] > gaps[2] >= 0


# --- certificates and Layer-1 re-checks ------------------------------------------------

def test_pade_certificate_tiles_and_every_cell_passes():
    cert = mobius_tangent_cell_certificate(_pade())
    assert len(cert.cells) >= 2
    check_tiling(cert.problem, cert.cells)
    for c in cert.cells:
        assert c.mode == "convex" and c.psi_p <= 0 and c.psi_q <= 0 and c.p <= c.t <= c.q


def test_modes_are_all_exercised():
    assert {c.mode for c in mobius_tangent_cell_certificate(_concave()).cells} == {"tangent"}
    pr = mobius_tangent_problem(a=-1, b=Fr(-1, 2), logs=[(1, 1, 1)], p=0, q=2)
    assert {c.mode for c in mobius_tangent_cell_certificate(pr).cells} == {"none"}


def test_float_dense_sampling_agrees_with_certified_claim():
    for pr in (_pade(), _concave(), _logmean("1/10", "1/2")):
        mobius_tangent_cell_certificate(pr)
        for i in range(201):
            xx = pr.p + (pr.q - pr.p) * Fr(i, 200)
            assert pr.value(xx) <= 1e-12


def test_tampered_cells_are_refused():
    cert = mobius_tangent_cell_certificate(_pade())
    pr, c0 = cert.problem, cert.cells[0]
    bd = c0.bounds[0]
    bad = [
        (replace(c0, bounds=(replace(bd, H=bd.H - Fr(1, 10 ** 6)),)), "recomputation"),
        (replace(c0, m=c0.m - 1), "recomputation"),
        (replace(c0, psi_p=Fr(-1)), "recomputation"),
        (replace(c0, t=c0.q + 1), "outside its cell"),
        (replace(c0, bounds=(replace(bd, order=99),)), "order"),
    ]
    for cell, frag in bad:
        with pytest.raises(MobiusTangentRefusal, match=frag):
            check_cell(pr, cell)


def test_tiling_gap_and_overlap_are_refused():
    cert = mobius_tangent_cell_certificate(_pade())
    cells = list(cert.cells)
    with pytest.raises(MobiusTangentRefusal, match="gap or overlap"):
        check_tiling(cert.problem, cells[:1] + cells[2:])
    with pytest.raises(MobiusTangentRefusal, match="not \\["):
        check_tiling(cert.problem, cells[:-1])


def test_breakpoints_are_honoured():
    cert = mobius_tangent_cell_certificate(_logmean("1/10", "1/2"), breakpoints=["1/5"])
    assert Fr(1, 5) in {c.q for c in cert.cells}
    with pytest.raises(MobiusTangentRefusal, match="strictly increasing"):
        mobius_tangent_cell_certificate(_logmean("1/10", "1/2"), breakpoints=["1"])


def test_sides_identity_mismatch_is_refused():
    cert = mobius_tangent_cell_certificate(_pade())
    forged = MobiusTangentCellCert(replace(cert.problem, a=cert.problem.a + 1), cert.cells)
    with pytest.raises(MobiusTangentRefusal):
        verify_certificate(forged)


# --- emission ------------------------------------------------------------------------

def _emit(specs, names):
    fam = mobius_tangent_cell_family(
        "MT", GridSpec([("case", list(range(len(specs))))]),
        lambda pt: names[pt["case"]], spec=lambda pt: specs[pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("MT",)), [MobiusTangentCellEmitter()],
               ValidationReport(checks=(("mobius_tangent_cell", True),)))
    return next(iter(rep.files.values()))


def test_emitted_lean_shape():
    txt = _emit([{"problem": _logmean("1/10", "1/2")},
                 {"lhs": sp.log(1 + x), "rhs": x * (6 + x) / (6 + 4 * x), "var": x,
                  "p": "1/2", "q": "1"}], ["lm", "pd"])
    for bad in ("sorry", "native_decide", "admit", "axiom "):
        assert bad not in txt
    assert txt.count("theorem lm_mtc_convex_endpoint") == 1       # generic lemmas once
    assert "theorem lm (x : ℝ)" in txt and "theorem pd_sides (x : ℝ)" in txt
    assert "Real.log_two_gt_d9" in txt                            # u < 2/3 path
    assert "rcases le_or_gt x" in txt
    assert "Goldwasser" in txt and "conjecture1_proved = False" in txt


def test_unknown_spec_keys_are_refused():
    with pytest.raises(Exception, match="unknown spec key"):
        _emit([{"a": -2, "logs": [(1, 0, 1)], "p": 1, "q": 2, "typo": 1}], ["z"])


def test_dogfood_regeneration_matches():
    r = subprocess.run([sys.executable, "examples/mobius_tangent_cell/generate.py", "--check"],
                       cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "check: OK" in r.stdout


def test_order_zero_is_only_for_u_equal_one():
    pr = mobius_tangent_problem(a=-1, b=Fr(-1, 2), logs=[(1, 1, 1)], p=0, q=2)
    cert = mobius_tangent_cell_certificate(pr, breakpoints=["1/2"])
    c0 = cert.cells[0]
    forged = replace(c0, bounds=(log_upper(c0.bounds[0].u, 0),))
    if c0.bounds[0].u != 1:
        with pytest.raises(MobiusTangentRefusal, match="order 0"):
            check_cell(pr, forged)
    assert log_upper(Fr(1), 7).order == 0 and log_upper(Fr(1), 7).H == 0


def test_non_template_function_is_refused():
    with pytest.raises(MobiusTangentRefusal):
        problem_from_sides(sp.log(1 + x), sp.exp(x), x, 0, 1)


@pytest.mark.parametrize("positive", [False, True])
def test_sides_keep_log_atoms_whole(positive):
    """Regression (2026-09-30): `log(t/2)` must stay one log atom.  The default sympy log hint
    split it into `log t - log 2` (for positive symbols) and the constant `-log 2` was refused as
    a convex log.  Zhu, arXiv:2608.24827 Lemma 3.1, band [15/4, 23/5] of ZhuEnvelope.lean."""
    t = sp.Symbol("t", positive=True) if positive else sp.Symbol("t")
    pr = problem_from_sides(sp.log(t / 2) - 1 / t, sp.Rational(1243, 2000), t,
                            sp.Rational(15, 4), sp.Rational(23, 5))
    assert len(pr.logs) == 1
    mobius_tangent_cell_certificate(pr)


def test_explicit_negative_constant_log_refusal_names_the_rewrite():
    with pytest.raises(MobiusTangentRefusal, match=r"CONSTANT log\(2\).*log\(1/2\)"):
        mobius_tangent_problem(a=0, logs=[(-1, 2, 0)], p=0, q=1)
