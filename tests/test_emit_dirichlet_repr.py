"""emit_dirichlet_repr: the Euler-Maclaurin representation shape.

The correction-term closed forms are re-verified by symbolic differentiation (anti-phantom).
"""
import sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.emit_dirichlet_repr import verify_corrections, emit_zeta_trunc_statement  # noqa: E402


def test_correction_closed_forms_verify_by_differentiation():
    ok, antideriv, deriv = verify_corrections()
    assert ok
    x, s = sp.symbols("x s")
    assert sp.simplify(sp.diff(antideriv, x) - x ** (-s)) == 0        # ∫x^{-s} = x^{1-s}/(1-s)


def test_emitted_statement_shape():
    stmt = emit_zeta_trunc_statement("zeta_trunc")
    assert "riemannZeta s" in stmt and "(N : ℂ) ^ (1 - s)" in stmt and "Int.fract" in stmt


def test_wrong_antiderivative_fails_check():
    x, s = sp.symbols("x s")
    wrong = x ** (1 - s) / (s - 1)   # wrong pole sign
    assert sp.simplify(sp.diff(wrong, x) - x ** (-s)) != 0
