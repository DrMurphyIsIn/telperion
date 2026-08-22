"""Pratt / Lucas primality certificates — exact-integer finder + verifier.

A Pratt certificate proves `n` prime by Lucas's test: a witness `a` with
`a^(n-1) ≡ 1 (mod n)` and `a^((n-1)/q) ≢ 1 (mod n)` for every prime `q | n-1`
(so `a` has order exactly `n-1`, forcing `Z/nZ*` to have `n-1` elements, i.e.
`n` prime).  Pratt's insight: the primality of each factor `q` is witnessed
recursively by its own Pratt certificate, bottoming out at 2 — a compact,
finite, exactly-checkable proof object.

This module is the untrusted generator: `find_pratt_certificate` searches for the
witness and recursively factors, `verify_pratt_certificate` re-checks everything
in independent exact integer arithmetic.  The emitted-Lean side (a follow-up)
discharges the same object through Mathlib's `lucas_primality`; the kernel — not
this code — is the trusted checker there.  Here the verifier exists to catch a
bad certificate before a CI round-trip, mirroring the rest of Telperion.
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class PrattCertificate:
    """A recursive Lucas/Pratt primality witness for ``n``.

    ``witness`` a has order n-1 mod n; ``factorization`` is the complete prime
    factorization of n-1 as (prime, exponent) pairs; ``sub_certificates`` maps
    each prime factor q > 2 to its own Pratt certificate.
    """

    n: int
    witness: int
    factorization: tuple[tuple[int, int], ...]
    sub_certificates: dict = field(default_factory=dict)


def _factor(m: int) -> tuple[tuple[int, int], ...]:
    """Complete prime factorization of m as sorted (prime, exponent) pairs."""
    factors: dict[int, int] = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            factors[d] = factors.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        factors[m] = factors.get(m, 0) + 1
    return tuple(sorted(factors.items()))


def _is_primitive_root(a: int, n: int, prime_factors: tuple[int, ...]) -> bool:
    """True iff a has order exactly n-1 mod n (the Lucas condition)."""
    if pow(a, n - 1, n) != 1:
        return False
    return all(pow(a, (n - 1) // q, n) != 1 for q in prime_factors)


def find_pratt_certificate(n: int) -> PrattCertificate | None:
    """Search for a Pratt certificate of ``n``; return None if none (n composite).

    Recurses into the prime factors of n-1.  Deterministic: witnesses are tried
    in increasing order, so the same n always yields the same certificate.
    """
    if n < 2:
        return None
    if n == 2:
        return PrattCertificate(n=2, witness=1, factorization=(), sub_certificates={})

    fac = _factor(n - 1)
    prime_factors = tuple(q for q, _ in fac)

    witness = None
    for a in range(2, n):
        if _is_primitive_root(a, n, prime_factors):
            witness = a
            break
    if witness is None:
        return None  # no primitive root ⇒ n is composite

    sub: dict[int, PrattCertificate] = {}
    for q in prime_factors:
        if q > 2:
            sub_cert = find_pratt_certificate(q)
            if sub_cert is None:
                return None  # a claimed factor is not actually prime
            sub[q] = sub_cert

    return PrattCertificate(n=n, witness=witness, factorization=fac, sub_certificates=sub)


def verify_pratt_certificate(cert: PrattCertificate) -> bool:
    """Independently re-check a Pratt certificate in exact integer arithmetic."""
    n = cert.n
    if n == 2:
        return cert.n == 2
    if n < 2:
        return False

    # 1. the declared factorization must reconstruct n-1 exactly
    prod = 1
    for q, e in cert.factorization:
        if e < 1:
            return False
        prod *= q**e
    if prod != n - 1:
        return False

    prime_factors = tuple(q for q, _ in cert.factorization)

    # 2. the witness must have order exactly n-1 (Lucas)
    if not (1 < cert.witness < n):
        return False
    if not _is_primitive_root(cert.witness, n, prime_factors):
        return False

    # 3. every claimed prime factor must itself be certified prime
    for q in prime_factors:
        if q == 2:
            continue
        sub = cert.sub_certificates.get(q)
        if sub is None or sub.n != q or not verify_pratt_certificate(sub):
            return False

    return True
