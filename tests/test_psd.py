"""Exact LDLᵀ positive-semidefiniteness certificate finder + verifier.

Matrix inequalities are a class Telperion's scalar-polynomial emitters cannot
state.  The certificate is an exact rational `A = L D Lᵀ` (unit-lower-triangular
L, diagonal D); `A ≽ 0 ⇔ Dᵢᵢ ≥ 0`, `A ≻ 0 ⇔ Dᵢᵢ > 0`.  Both L,D and the check
are exact rationals — a deterministic finder (no SDP, no rounding), unlike the
SOS Gram path.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.psd import (  # noqa: E402
    PSDCertificate,
    find_psd_certificate,
    verify_psd_certificate,
)


def test_certifies_a_positive_definite_matrix():
    A = sp.Matrix([[2, 1], [1, 2]])
    cert = find_psd_certificate(A)

    assert isinstance(cert, PSDCertificate)
    assert verify_psd_certificate(cert) is True
    assert cert.positive_definite is True          # eigenvalues 1, 3 > 0


def test_certifies_a_singular_positive_semidefinite_matrix():
    A = sp.Matrix([[1, 1], [1, 1]])                # PSD, rank 1 (eigenvalues 0, 2)
    cert = find_psd_certificate(A)

    assert cert is not None
    assert verify_psd_certificate(cert) is True
    assert cert.positive_definite is False         # singular ⇒ PSD but not PD


def test_rejects_an_indefinite_matrix():
    A = sp.Matrix([[1, 2], [2, 1]])                # eigenvalues 3, -1
    assert find_psd_certificate(A) is None


def test_factorization_reconstructs_the_matrix_exactly():
    A = sp.Matrix([[4, 2, 0], [2, 5, 1], [0, 1, 3]])
    cert = find_psd_certificate(A)

    L, D = cert.L, cert.D
    assert L * D * L.T == A                         # exact rational identity
    assert all(d >= 0 for d in D.diagonal())


def test_verifier_rejects_tampered_diagonal():
    A = sp.Matrix([[2, 1], [1, 2]])
    cert = find_psd_certificate(A)
    bad_D = cert.D.copy()
    bad_D[0, 0] = -bad_D[0, 0] - 1                  # force a negative pivot
    bad = PSDCertificate(A=cert.A, L=cert.L, D=bad_D, positive_definite=cert.positive_definite)

    assert verify_psd_certificate(bad) is False
