"""Pratt/Lucas primality certificate finder + independent exact verifier.

The untrusted-generator core of a primality emitter: find a recursive Pratt
certificate for a prime (a primitive-root witness `a` mod n, the full prime
factorization of n-1, and a Pratt certificate for each prime factor), and
re-check it in independent exact integer arithmetic.  Number theory is a domain
Telperion's 35 positivity/identity emitters do not touch.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.pratt import (  # noqa: E402
    PrattCertificate,
    find_pratt_certificate,
    verify_pratt_certificate,
)


def test_finds_and_verifies_certificate_for_a_prime():
    cert = find_pratt_certificate(1009)  # a prime

    assert isinstance(cert, PrattCertificate)
    assert cert.n == 1009
    assert verify_pratt_certificate(cert) is True


def test_returns_none_for_a_composite():
    assert find_pratt_certificate(1001) is None  # 7 * 11 * 13


def test_certificate_is_recursively_structured():
    # n-1 factors must each carry their own Pratt sub-certificate (recursion
    # bottoms out at 2), and the declared factorization must reconstruct n-1.
    cert = find_pratt_certificate(1009)

    prod = 1
    for q, e in cert.factorization:
        prod *= q**e
    assert prod == cert.n - 1
    # every prime factor > 2 carries a sub-certificate for its own primality
    for q, _e in cert.factorization:
        if q > 2:
            assert q in cert.sub_certificates
            assert verify_pratt_certificate(cert.sub_certificates[q]) is True


def test_verifier_rejects_a_tampered_witness():
    cert = find_pratt_certificate(1009)
    bad = PrattCertificate(
        n=cert.n,
        witness=cert.witness + 1 if cert.witness + 1 < cert.n else 2,
        factorization=cert.factorization,
        sub_certificates=cert.sub_certificates,
    )
    # a wrong primitive-root witness must fail the exact re-check
    assert verify_pratt_certificate(bad) is False
