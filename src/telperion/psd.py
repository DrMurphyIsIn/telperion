"""Exact LDLᵀ positive-semidefiniteness certificates.

For a symmetric rational matrix `A`, the square-root-free Cholesky
`A = L D Lᵀ` (unit-lower-triangular `L`, diagonal `D`) is an exact rational
certificate of definiteness:

    xᵀ A x = (Lᵀx)ᵀ D (Lᵀx) = Σᵢ Dᵢᵢ · (Lᵀx)ᵢ²   ⟹   A ≽ 0 ⇔ Dᵢᵢ ≥ 0,  A ≻ 0 ⇔ Dᵢᵢ > 0.

Both the factors and the sign check are exact rationals — a deterministic finder
with no SDP and no floating-point rounding (unlike the SOS Gram path).  This is
the untrusted generator: `find_psd_certificate` computes the factorization,
`verify_psd_certificate` re-checks `A = L D Lᵀ` and the diagonal signs.  The
Lean emitter (a follow-up) discharges the same object against Mathlib's
`Matrix.PosSemidef` / `Matrix.PosDef`; the kernel is the trusted checker there.

The factorization uses the no-pivot LDLᵀ recursion with zero-pivot tolerance:
a zero pivot is admissible for PSD iff the rest of its column is zero (the
coordinate contributes nothing to the form).  A zero pivot with a nonzero entry
below it means this pivot order cannot certify PSD; `find_psd_certificate`
returns None (a symmetric-pivoting refinement is future work).  A negative
Schur-complement pivot means `A` is indefinite ⇒ None.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class PSDCertificate:
    """`A = L D Lᵀ` with unit-lower-triangular L and diagonal D ≥ 0."""

    A: sp.Matrix
    L: sp.Matrix
    D: sp.Matrix
    positive_definite: bool


def _ldl_exact(A: sp.Matrix):
    """No-pivot square-root-free LDLᵀ over exact rationals, zero-pivot tolerant.

    Returns (L, D) with A = L D Lᵀ, or None if a pivot is negative (indefinite)
    or a zero pivot has a nonzero column below it (needs symmetric pivoting).
    """
    n = A.rows
    L = sp.eye(n)
    D = sp.zeros(n, n)
    for j in range(n):
        d = A[j, j] - sum(L[j, k] ** 2 * D[k, k] for k in range(j))
        d = sp.nsimplify(sp.together(d)) if not d.is_number else d
        d = sp.Rational(d) if d.is_rational else d
        if d < 0:
            return None  # negative pivot ⇒ indefinite
        D[j, j] = d
        for i in range(j + 1, n):
            off = A[i, j] - sum(L[i, k] * L[j, k] * D[k, k] for k in range(j))
            if d == 0:
                if sp.simplify(off) != 0:
                    return None  # zero pivot but nonzero below ⇒ this order can't certify
                L[i, j] = 0
            else:
                L[i, j] = sp.together(off / d)
    return L, D


def find_psd_certificate(A: sp.Matrix) -> PSDCertificate | None:
    """Find an exact LDLᵀ PSD certificate for symmetric rational `A`, or None.

    None means: not square, not symmetric, indefinite, or PSD only under a pivot
    order this no-pivot factorization does not reach.
    """
    A = sp.Matrix(A)
    if A.rows != A.cols:
        return None
    if A != A.T:
        return None

    res = _ldl_exact(A)
    if res is None:
        return None
    L, D = res
    if L * D * L.T != A:  # exact rational sanity check before we trust it
        return None
    diag = [D[i, i] for i in range(A.rows)]
    if any(d < 0 for d in diag):
        return None
    return PSDCertificate(A=A, L=L, D=D, positive_definite=all(d > 0 for d in diag))


def verify_psd_certificate(cert: PSDCertificate) -> bool:
    """Independently re-check `A = L D Lᵀ`, D diagonal ≥ 0, L unit lower triangular."""
    A, L, D = sp.Matrix(cert.A), sp.Matrix(cert.L), sp.Matrix(cert.D)
    n = A.rows
    if L.rows != n or D.rows != n:
        return False
    # L unit lower triangular
    for i in range(n):
        if L[i, i] != 1:
            return False
        for k in range(i + 1, n):
            if L[i, k] != 0:
                return False
    # D diagonal
    for i in range(n):
        for k in range(n):
            if i != k and D[i, k] != 0:
                return False
    # exact reconstruction + nonnegative diagonal
    if L * D * L.T != A:
        return False
    diag = [D[i, i] for i in range(n)]
    if any(d < 0 for d in diag):
        return False
    # positive_definite flag must match the exact diagonal
    return cert.positive_definite == all(d > 0 for d in diag)
