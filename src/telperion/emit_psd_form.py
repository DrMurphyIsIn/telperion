"""Positive-definite quadratic-form emitter — a deterministic, cvxpy-free PSD
certificate via exact rational LDLᵀ congruence.

The recurring shape across the SoS / P=NP moment-matrix work and the BG
Gram-bridges is "this explicit rational symmetric matrix M is positive
(semi)definite".  For a positive-DEFINITE M the exact LDLᵀ decomposition
``M = L·D·Lᵀ`` (L unit lower-triangular, D diagonal, all Dᵢ > 0, computed in exact
rationals — no SDP) gives the congruence

    xᵀ M x = Σᵢ Dᵢ · (Lᵀx)ᵢ²   with (Lᵀx)ᵢ = Σⱼ Lⱼᵢ·xⱼ,

so ``0 ≤ xᵀMx`` is the robust, search-free

    theorem <name> (x₁ … xₙ : ℝ) : 0 ≤ xᵀMx := by
      have hid : xᵀMx = Σᵢ Dᵢ·(Lᵀx)ᵢ² := by ring
      rw [hid]; positivity

Distinct from ``SOSEmitter`` (which uses the limited exact path or an SDP solver
for a general polynomial): this is the DETERMINISTIC exact-LDLᵀ primitive for an
explicit matrix.  NEGATIVE CONTROL: a non-positive-definite matrix is refused
(sympy's LDLᵀ has no positive pivot).  A singular positive-semidefinite matrix is
named-open (needs pivoting / rank reduction — v1 is positive-definite)."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp
from sympy.matrices.exceptions import NonPositiveDefiniteMatrixError

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class PSDCertificate:
    """A verified positive-definite LDLᵀ → SOS certificate for a matrix."""

    n: int
    matrix: tuple            # the symmetric matrix as a tuple of tuples (rationals)
    sos_terms: tuple         # ((Dᵢ, baseᵢ), ...): xᵀMx = Σ Dᵢ·baseᵢ², every Dᵢ > 0


def _to_matrix(M) -> sp.Matrix:
    return sp.Matrix([[sp.nsimplify(v) for v in row] for row in M])


def psd_certificate(M) -> PSDCertificate:
    """Build and EXACTLY self-check a positive-definite LDLᵀ → SOS certificate.
    Refuses a non-square, non-symmetric, or non-positive-definite matrix."""
    mat = _to_matrix(M)
    n = mat.rows
    if mat.cols != n:
        raise ValueError(f"PSD-form needs a square matrix; got {n}×{mat.cols}")
    if mat != mat.T:
        raise ValueError("PSD-form needs a SYMMETRIC matrix")
    try:
        L, D = mat.LDLdecomposition()
    except NonPositiveDefiniteMatrixError as e:
        raise ValueError(
            f"matrix is not positive-definite — refused (negative control). "
            f"A singular positive-semidefinite matrix is named-open (v1 is "
            f"positive-definite). [{e}]"
        ) from e
    xs = sp.symbols(f"x1:{n + 1}")
    sos = []
    for i in range(n):
        d = sp.nsimplify(D[i, i])
        if d <= 0:
            raise ValueError("non-positive LDLᵀ pivot — matrix not positive-definite")
        base = sp.expand(sum(L[j, i] * xs[j] for j in range(n)))
        sos.append((d, base))
    # exact self-check: xᵀMx − Σ Dᵢ·baseᵢ² == 0
    x = sp.Matrix(xs)
    quad = sp.expand((x.T * mat * x)[0])
    if sp.expand(quad - sum(w * b**2 for w, b in sos)) != 0:
        raise ValueError("LDLᵀ SOS self-check failed — certificate rejected")
    return PSDCertificate(
        n=n,
        matrix=tuple(tuple(sp.nsimplify(v) for v in row) for row in mat.tolist()),
        sos_terms=tuple(sos),
    )


def certify_psd_point(family, pt, name):
    """Certify one PSD-form instance from ``family.special[1](pt) -> matrix``."""
    M = family.special[1](pt)
    cert = psd_certificate(M)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class PSDFormEmitter(Emitter):
    """Emit `0 ≤ xᵀMx` for a positive-definite M via the LDLᵀ congruence,
    discharged deterministically by `ring` (the identity) + `positivity`."""

    def __post_init__(self):
        self.kind = "psd_form"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: PSDCertificate = inst.payload  # type: ignore[assignment]
            n = cert.n
            xs = sp.symbols(f"x1:{n + 1}")
            binders = " ".join(f"x{i}" for i in range(1, n + 1))
            M = [[cert.matrix[i][j] for j in range(n)] for i in range(n)]
            quad = sp.expand(sum(M[i][j] * xs[i] * xs[j] for i in range(n) for j in range(n)))
            quad_s = expr_lean(quad, xs)
            sos_s = " + ".join(
                f"{rat_lean(w)} * ({expr_lean(base, xs)})^2" for w, base in cert.sos_terms
            )
            lines.append(
                f"theorem {inst.lean_name} ({binders} : ℝ) :\n"
                f"    (0:ℝ) ≤ {quad_s} := by\n"
                f"  have hid : {quad_s} = {sos_s} := by ring\n"
                f"  rw [hid]; positivity\n"
            )
            nthm += 1
        return "".join(lines), nthm


def psd_form_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a positive-definite quadratic-form family (kind='psd_form').

    ``spec``: a callable ``pt -> M`` returning a symmetric positive-definite
    matrix (a sequence of rows of rationals).  Refuses a non-PD matrix."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("psd_form", spec),
        constants=dict(constants or {}),
    )
