"""spectral_factor round-trips nonneg cosine tuples; the emitted SOS cert is well-formed
and nonnegativity-only (no admissibility gate)."""
import numpy as np
import sympy as sp
import pytest

from telperion.emit_spectral_factorization import (
    spectral_factor,
    rationalize_factor,
    emit_spectral_sos_cert,
)
from telperion.emit_mt_cosine import fejer_riesz_sos, MT_DEG4
from telperion.emit_zero_free_cosine import vallee_poussin_coeffs


def _autocorr(b):
    d = len(b) - 1
    a = [float(np.dot(b, b))]
    for k in range(1, d + 1):
        a.append(float(2 * np.sum(np.asarray(b)[: d + 1 - k] * np.asarray(b)[k:])))
    return a


@pytest.mark.parametrize("a", [
    [sp.Rational(35, 8), 7, sp.Rational(7, 2), 1, sp.Rational(1, 8)],   # VP deg-4
    list(MT_DEG4["a"]),                                                  # MT deg-4
    [sp.Integer(2), sp.Integer(1)],                                      # simple deg-1
])
def test_spectral_factor_roundtrips(a):
    b = spectral_factor(a)
    ar = _autocorr(b)
    # `b` is a NUMERIC intermediate from np.roots (double-precision companion-matrix
    # root-finding); on clustered-root cases (VP deg-4) the residual is ~1e-4 and its
    # exact size shifts with the BLAS/root-ordering path across environments. The
    # shipped certificate uses the RATIONALIZED exact factor, whose correctness is
    # gated by the exact SOS identity in test_rationalize_gives_exact_nonneg_sos; this
    # roundtrip only guards against gross breakage, so 1e-3 is the principled bound.
    assert max(abs(ar[k] - float(a[k])) for k in range(len(a))) < 1e-3


def test_rejects_indefinite_trig_poly():
    # a0=1, a1=3 -> P(pi)=1-3=-2 < 0, not a nonnegative trig polynomial.
    with pytest.raises(ValueError, match="not nonnegative|dips"):
        spectral_factor([sp.Integer(1), sp.Integer(3)])


def test_rationalize_gives_exact_nonneg_sos():
    # rationalized factor -> exact rational spectrum whose SOS is exact by construction.
    x = sp.Symbol("x")
    b_rat, a_exact = rationalize_factor(MT_DEG4["a"], denom=8)
    A, B, p, a2 = fejer_riesz_sos(b_rat)
    assert list(a2) == list(a_exact)
    assert sp.expand(p - (A**2 + (1 - x**2) * B**2)) == 0     # exact SOS identity


def test_emitted_cert_wellformed_and_general():
    # a general nonneg trig poly with a1 < a0 (NOT M-T admissible) still certifies:
    # P = 2 + cos θ  (a=[2,1]) is >= 0; emit_mt_cosine would reject it, this must not.
    lean, a_exact = emit_spectral_sos_cert("spec_test", [sp.Integer(2), sp.Integer(1)], denom=32)
    assert "theorem spec_test (x : ℝ)" in lean
    assert "(0:ℝ) ≤" in lean and "sq_nonneg" in lean and "mul_nonneg hsq" in lean
    assert "**" not in lean            # Lean uses ^, not Python **


def test_exact_target_succeeds_for_perfect_square():
    # VP (1+cosθ)^n is a perfect square: exact rational factor b=(1/4,1,3/2,1,1/4) at denom 8.
    lean, a_exact = emit_spectral_sos_cert(
        "vp4", [sp.Rational(35, 8), 7, sp.Rational(7, 2), 1, sp.Rational(1, 8)],
        denom=8, target="exact",
    )
    assert list(a_exact) == [sp.Rational(35, 8), sp.Integer(7), sp.Rational(7, 2),
                             sp.Integer(1), sp.Rational(1, 8)]
    assert "theorem vp4 (x : ℝ)" in lean


def test_exact_target_raises_when_not_rational():
    # [3,2,1] (P = 2(1+cosθ+cos²θ) >= 0) has irrational Fejér–Riesz roots -> no exact factor.
    with pytest.raises(ValueError, match="exact rational factorization not found"):
        emit_spectral_sos_cert("nonsq", [sp.Integer(3), sp.Integer(2), sp.Integer(1)],
                               denom=8, target="exact")
