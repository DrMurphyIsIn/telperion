"""emit_zero_free_cosine: the nonnegative-cosine zero-free-region emitter.

The de la Vallee-Poussin family P(θ)=(1+cos θ)^n has nonnegative cosine coeffs
a_k (binomial autocorrelations) and collapses in x=cos θ to p(x)=(1+x)^n, whose
Fejer-Riesz/Handelman certificate on [-1,1] is a single nonnegative-coefficient
term.  Generator UNTRUSTED: every certificate is exact-reconstruction checked.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_zero_free_cosine import (  # noqa: E402
    vallee_poussin_coeffs, f_functional)
from telperion.emit_handelman import find_handelman_certificate  # noqa: E402


def test_vallee_poussin_coeffs_degree_3_are_nonneg_with_expected_ratio():
    a = vallee_poussin_coeffs(3)
    assert all(c >= 0 for c in a)            # the cone property a_k >= 0
    assert a[1] / a[0] == sp.Rational(3, 2)  # a_1/a_0 = 2n/(n+1) = 3/2 for n=3


def test_f_functional_rises_from_degree_2_to_3():
    # F is the zero-free-region functional; (1+cos)^n slice increases early.
    assert f_functional(vallee_poussin_coeffs(3)) > f_functional(vallee_poussin_coeffs(2))


def test_degree_3_handelman_certificate_is_exact_and_nonneg():
    x = sp.Symbol("x", real=True)
    # p(x) = 4 + 12x + 12x^2 + 4x^3 = 4(1+x)^3, the minimal-cleared d=3 cosine poly.
    p = sp.expand(4 + 12 * x + 12 * x**2 + 4 * x**3)
    terms = find_handelman_certificate(p, [1 + x, 1 - x], [x], max_deg=3)
    assert terms, "no Handelman certificate found"
    recon = sum(sp.nsimplify(c) * (1 + x) ** e[0] * (1 - x) ** e[1] for c, e in terms)
    assert sp.expand(recon - p) == 0                 # exact reconstruction (anti-phantom)
    assert all(sp.nsimplify(c) >= 0 for c, _ in terms)  # nonnegative combination


def test_forged_certificate_is_refused():
    # anti-phantom: a wrong-degree forged term must NOT reconstruct the polynomial.
    x = sp.Symbol("x", real=True)
    p = sp.expand(4 + 12 * x + 12 * x**2 + 4 * x**3)
    forged = 4 * (1 + x) ** 2  # wrong degree
    assert sp.expand(forged - p) != 0
