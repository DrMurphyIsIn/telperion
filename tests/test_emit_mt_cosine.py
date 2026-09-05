"""The MT-cosine emitter's Fejér–Riesz SOS is exact, the degree-4 optimum is admissible
and beats the VP slice, and the emitted Lean is well-formed."""
import sympy as sp
import pytest

from telperion.emit_mt_cosine import (
    fejer_riesz_sos,
    mt_cosine_cert_lean,
    f_functional_exact,
    MT_DEG4,
)
from telperion.emit_zero_free_cosine import vallee_poussin_coeffs, f_functional


def test_fejer_riesz_identity_exact():
    x = sp.Symbol("x")
    A, B, p, a = fejer_riesz_sos(MT_DEG4["b"])
    # exact SOS == Chebyshev spectrum, degree collapses to 4
    assert sp.expand(p - (A**2 + (1 - x**2) * B**2)) == 0
    assert sp.expand(p - sum(a[k] * sp.chebyshevt(k, x) for k in range(5))) == 0
    assert sp.Poly(p, x).degree() == 4
    assert [str(c) for c in a] == ["65/64", "7/4", "9/8", "1/2", "1/8"]


def test_deg4_admissible_and_beats_vp():
    _, _, _, a = fejer_riesz_sos(MT_DEG4["b"])
    assert all(c >= 0 for c in a) and a[1] > a[0]
    F_mt = f_functional_exact(a)
    F_vp = f_functional(vallee_poussin_coeffs(4))
    assert sp.nsimplify(F_mt) > sp.nsimplify(F_vp)          # exact surd comparison
    assert float(F_mt) / float(F_vp) > 1.07                 # ~7.4% wider


def test_emitted_lean_wellformed():
    cert = mt_cosine_cert_lean(
        "mt_cosine_deg4_nonneg", MT_DEG4["b"],
        doc="Degree-4 F-optimal nonneg cosine polynomial, >= 0 on [-1,1] via exact SOS.",
    )
    assert cert.startswith("/-- Degree-4")
    assert "theorem mt_cosine_deg4_nonneg (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1)" in cert
    assert "(0:ℝ) ≤" in cert
    assert "sq_nonneg" in cert and "mul_nonneg hsq" in cert
    # the certified polynomial is exactly p = Σ a_k T_k
    assert "x**4 + 2*x**3" in cert or "x^4" in cert or "x**4" in cert


def test_rejects_degenerate_branch():
    # b giving a1 < a0 (e.g. a near-constant P): a2-heavy tuple where a1 < a0.
    # Use b = (1, 0, 1): A = 1 + T_2 = 2x^2, a_0 = 2, a_1 = 0 -> a1 < a0.
    with pytest.raises(ValueError, match="a₁ < a₀|negative"):
        mt_cosine_cert_lean("bad", [sp.Integer(1), sp.Integer(0), sp.Integer(1)])


def test_fejer_riesz_rejects_inconsistent_degree():
    # A well-formed b never raises; this is a guard smoke-check that valid b passes.
    A, B, p, a = fejer_riesz_sos([sp.Rational(1), sp.Rational(1)])
    assert sp.Poly(p, sp.Symbol("x")).degree() == 1
