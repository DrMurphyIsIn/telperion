"""Positive-definite quadratic-form emitter — a deterministic, cvxpy-free PSD
certificate via exact rational LDLᵀ congruence.

The recurring shape across the SoS / P=NP moment-matrix work and the BG
Gram-bridges is "this explicit rational symmetric matrix M is positive
(semi)definite".  For a positive-semidefinite M the exact symmetric completing-the-square
congruence (all pivots Dᵢ ≥ 0, computed in exact rationals — no SDP, no
`LDLdecomposition`) gives

    xᵀ M x = Σᵢ Dᵢ · (Lᵀx)ᵢ²   with (Lᵀx)ᵢ = Σⱼ Lⱼᵢ·xⱼ,

so ``0 ≤ xᵀMx`` is the robust, search-free

    theorem <name> (x₁ … xₙ : ℝ) : 0 ≤ xᵀMx := by
      have hid : xᵀMx = Σᵢ Dᵢ·(Lᵀx)ᵢ² := by ring
      rw [hid]; positivity

Distinct from ``SOSEmitter`` (which uses the limited exact path or an SDP solver
for a general polynomial): this is the DETERMINISTIC exact-LDLᵀ primitive for an
explicit matrix.  Handles positive-DEFINITE and singular positive-SEMIdefinite matrices alike.
NEGATIVE CONTROL: an indefinite matrix (a negative pivot, or a bare cross term)
is refused; a trivially-zero form (`0 ≤ 0`) is refused as vacuous."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class PSDCertificate:
    """A verified positive-semidefinite (completing-the-square) SOS certificate."""

    n: int
    matrix: tuple            # the symmetric matrix as a tuple of tuples (rationals)
    sos_terms: tuple         # ((cᵢ, baseᵢ), ...): xᵀMx = Σ cᵢ·baseᵢ², every cᵢ > 0


def _to_matrix(M) -> sp.Matrix:
    return sp.Matrix([[sp.nsimplify(v) for v in row] for row in M])


def psd_certificate(M) -> PSDCertificate:
    """Build and EXACTLY self-check a positive-semidefinite SOS certificate via a
    symmetric completing-the-square (LDLᵀ) congruence — exact rationals, no SDP,
    version-robust (no `LDLdecomposition`).  Handles positive-DEFINITE and
    singular positive-SEMIdefinite matrices alike; refuses an indefinite matrix
    (the negative control) and a trivially-zero form (`0 ≤ 0`, vacuous)."""
    mat = _to_matrix(M)
    n = mat.rows
    if mat.cols != n:
        raise ValueError(f"PSD-form needs a square matrix; got {n}×{mat.cols}")
    if mat != mat.T:
        raise ValueError("PSD-form needs a SYMMETRIC matrix")
    xs = sp.symbols(f"x1:{n + 1}")
    quad = sp.expand((sp.Matrix(xs).T * mat * sp.Matrix(xs))[0])
    q = quad
    sos = []
    for i in range(n):
        xi = xs[i]
        c = q.coeff(xi, 2)
        if c == 0:
            # a zero pivot is only PSD if xᵢ has vanished entirely; a bare cross
            # term (xᵢ·xⱼ with no xᵢ²) is an indefinite direction.
            if q.coeff(xi, 1) != 0:
                raise ValueError(
                    f"matrix is INDEFINITE (a bare cross term in x{i + 1} with no "
                    f"square) — refused (negative control)"
                )
            continue
        if c < 0:
            raise ValueError(
                f"matrix is NOT positive-semidefinite (negative pivot {c} at "
                f"x{i + 1}) — refused (negative control)"
            )
        lin = q.coeff(xi, 1)                    # linear-in-others coefficient of xᵢ
        base = sp.expand(xi + lin / (2 * c))    # complete the square: c·(xᵢ + …)²
        sos.append((sp.nsimplify(c), base))
        q = sp.expand(q - c * base**2)          # Schur-complement remainder (no xᵢ)
    if sp.expand(q) != 0:
        raise ValueError(f"congruence residual nonzero ({q}) — matrix not PSD, refused")
    if not sos:
        raise ValueError("the quadratic form is identically zero (0 ≤ 0 is vacuous) — refused")
    # exact self-check: xᵀMx − Σ cᵢ·baseᵢ² == 0
    if sp.expand(quad - sum(w * b**2 for w, b in sos)) != 0:
        raise ValueError("PSD SOS self-check failed — certificate rejected")
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
    """Emit `0 ≤ xᵀMx` for a positive-semidefinite M via the completing-the-square congruence,
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
    """Build a positive-semidefinite quadratic-form family (kind='psd_form').

    ``spec``: a callable ``pt -> M`` returning a symmetric positive-semidefinite
    matrix (a sequence of rows of rationals).  Refuses an indefinite matrix."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("psd_form", spec),
        constants=dict(constants or {}),
    )
