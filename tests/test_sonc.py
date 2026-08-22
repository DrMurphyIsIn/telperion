"""SONC — nonnegative circuit polynomial certificates (exact rationalized AM-GM).

A circuit polynomial is `Σⱼ cⱼ x^{α(j)} + c_β x^β` with the `α(j)` the vertices
of a simplex (even exponents, positive coeffs — monomial squares) and `β` a
rational-barycentric interior point.  Iliman–de Wolff: it is nonnegative iff
`|c_β| ≤ Θ = Πⱼ (cⱼ/λⱼ)^{λⱼ}` (β not even) — an inequality with an irrational
circuit number Θ.  The key exact move: with rational `λⱼ = pⱼ/q`, raising to the
q-th power clears the fractional exponents, giving the EXACT rational condition
`|c_β|^q ≤ Πⱼ (cⱼ/λⱼ)^{pⱼ}`.  This is sparse positivity independent of SOS.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.sonc import (  # noqa: E402
    SONCCertificate,
    find_circuit_certificate,
    verify_circuit_certificate,
)

x, y = sp.symbols("x y", real=True)


def test_certifies_the_motzkin_circuit_polynomial():
    # Motzkin: nonneg but NOT SOS; a single circuit with a tight (equality) AM-GM.
    motzkin = x**4 * y**2 + x**2 * y**4 + 1 - 3 * x**2 * y**2
    cert = find_circuit_certificate(motzkin, (x, y))

    assert isinstance(cert, SONCCertificate)
    assert verify_circuit_certificate(cert) is True
    # the exact rationalized AM-GM is 27 <= 27 (tight)
    assert cert.lhs_pow == 27
    assert cert.rhs_pow == 27


def test_certifies_a_strict_circuit():
    # shift the negative coefficient up: |c_beta| = 2 < 3 = Theta ⇒ strictly nonneg
    p = x**4 * y**2 + x**2 * y**4 + 1 - 2 * x**2 * y**2
    cert = find_circuit_certificate(p, (x, y))

    assert cert is not None
    assert verify_circuit_certificate(cert) is True
    assert cert.lhs_pow <= cert.rhs_pow


def test_rejects_a_circuit_that_is_not_nonnegative():
    # |c_beta| = 4 > 3 = Theta ⇒ the circuit is NOT nonnegative
    p = x**4 * y**2 + x**2 * y**4 + 1 - 4 * x**2 * y**2
    assert find_circuit_certificate(p, (x, y)) is None


def test_verifier_rejects_a_tampered_bound():
    motzkin = x**4 * y**2 + x**2 * y**4 + 1 - 3 * x**2 * y**2
    cert = find_circuit_certificate(motzkin, (x, y))
    bad = SONCCertificate(
        poly=cert.poly, symbols=cert.symbols, vertices=cert.vertices,
        interior=cert.interior, coeffs=cert.coeffs, lambdas=cert.lambdas,
        q=cert.q, lhs_pow=cert.lhs_pow + 1, rhs_pow=cert.rhs_pow,  # inflate LHS past RHS
    )
    assert verify_circuit_certificate(bad) is False
