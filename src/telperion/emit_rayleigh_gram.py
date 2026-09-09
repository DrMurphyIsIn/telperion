"""RayleighGram emitter — a concrete-instance shadow of the generalized-eigenvalue
/ Rayleigh-quotient lower bound from Axiom Math ``bgp212`` Theorem 11.1 (the
"H₁ ≤ 212" development).

The analytic statement being instantiated is a variational lower bound on the
largest generalized eigenvalue of a symmetric matrix pencil ``(J, I)``: for an
explicit rational direction vector ``c``,

    λ_max(J, I) = max_x (xᵀ J x) / (xᵀ I x)  ≥  (cᵀ J c) / (cᵀ I c)  >  θ ,

equivalently the positivity of the quadratic form ``J − θ·I`` in the direction
``c``:

    cᵀ J c − θ · cᵀ I c  >  0     (and, for the Rayleigh reading, cᵀ I c > 0).

In bgp212 Thm 11.1 the pencil is ``(J_T(F*), I_T(F*))`` — the variational Gram
integrals of a specific polynomial basis at the extremizer ``F*`` — and the
threshold is ``θ = 4``; the certificate ``J_T(F*) − 4·I_T(F*) > 0`` in the
explicit rational direction ``c`` is the arithmetic heart of the bound.

This emitter certifies the SELF-CONTAINED CONCRETE-INSTANCE form: given two
symmetric rational matrices ``J``, ``I``, a rational vector ``c``, and a rational
threshold ``θ > 0``, the two quadratic forms are exact rationals and the
inequality is a rational fact the Lean kernel closes by ``norm_num``.  To be
LOAD-BEARING (non-vacuous), the emitted theorem does NOT hand the kernel the
pre-computed literals ``qJ`` / ``qI``: it spells out both contractions as
explicit finite double-sums ``Σᵢⱼ Jᵢⱼ·cᵢ·cⱼ`` / ``Σᵢⱼ Iᵢⱼ·cᵢ·cⱼ`` over the
matrix entries and vector components — every ``Jᵢⱼ``, ``Iᵢⱼ``, ``cᵢ`` a rational
literal — so the kernel re-does the entire Gram contraction and re-checks the
inequality from scratch.

HONESTY SEAM.  The emitted theorem is a TRUE, NON-VACUOUS, ``norm_num``-decidable
rational statement: the kernel verifies the full ``cᵀJc − θ·cᵀIc`` and ``cᵀIc``
contractions and their sign.  What the kernel does NOT establish is the Gram-
matrix SEMANTICS — that ``J`` and ``I`` are the correct variational integrals of
a particular polynomial basis (so that the certified sign actually bounds
``λ_max`` for the intended operator).  That identification is the documented
generator-side input, the trust seam, and lives only in the provenance comment.
The builder REFUSES any non-symmetric matrix, dimension mismatch, ``θ ≤ 0``, zero
``c``, ``cᵀIc ≤ 0``, or — crucially — ``cᵀJc − θ·cᵀIc ≤ 0`` (a false inequality is
never emitted; honest refusal).  Dimension is capped at 25 (the emitted sum has
dim² terms).  ``conjecture1_proved = False``.  This is a positive-instance
witness family, NOT a step toward RH or toward the bgp212 conjecture.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# The emitted double-sum has dim² rational terms; keep the theorem small enough
# for norm_num to discharge without pathological blowup.
_MAX_DIM = 25


@dataclass(frozen=True)
class RayleighGramCert:
    """One certified concrete Rayleigh/Gram instance.

    ``dim`` — the common dimension of ``J``, ``I``, ``c``.
    ``J`` / ``I`` — the symmetric rational matrices, as row-major tuples of
        tuples of ``sp.Rational``.
    ``c`` — the rational direction vector (tuple of ``sp.Rational``), nonzero.
    ``theta`` — the rational threshold ``θ > 0`` (bgp212 uses ``θ = 4``).
    ``qJ`` — the exact rational ``cᵀ J c``.
    ``qI`` — the exact rational ``cᵀ I c`` (``> 0``).
    ``gap`` — the exact rational ``cᵀJc − θ·cᵀIc`` (``> 0``).
    """

    dim: int
    J: tuple[tuple[sp.Rational, ...], ...]
    I: tuple[tuple[sp.Rational, ...], ...]
    c: tuple[sp.Rational, ...]
    theta: sp.Rational
    qJ: sp.Rational
    qI: sp.Rational
    gap: sp.Rational


def _as_rational_matrix(M, name: str) -> tuple[tuple[sp.Rational, ...], ...]:
    """Coerce ``M`` (a sympy Matrix or nested sequence) to a square tuple-of-
    tuples of exact rationals; REFUSE a non-square or non-symmetric matrix."""
    if isinstance(M, sp.MatrixBase):
        rows = [[M[i, j] for j in range(M.cols)] for i in range(M.rows)]
    else:
        rows = [list(r) for r in M]
    n = len(rows)
    for r in rows:
        if len(r) != n:
            raise ValueError(
                f"rayleigh_gram REFUSED: matrix {name} is not square "
                f"({n} rows, a row of length {len(r)})")
    R = tuple(tuple(sp.Rational(sp.nsimplify(x)) for x in r) for r in rows)
    for i in range(n):
        for j in range(i + 1, n):
            if R[i][j] != R[j][i]:
                raise ValueError(
                    f"rayleigh_gram REFUSED: matrix {name} is not symmetric at "
                    f"({i},{j}): {R[i][j]} != {R[j][i]}")
    return R


def _quad_form(M: tuple[tuple[sp.Rational, ...], ...],
               c: tuple[sp.Rational, ...]) -> sp.Rational:
    """Exact rational contraction ``cᵀ M c = Σᵢⱼ Mᵢⱼ·cᵢ·cⱼ``."""
    total = sp.Integer(0)
    n = len(c)
    for i in range(n):
        for j in range(n):
            total += M[i][j] * c[i] * c[j]
    return sp.Rational(total)


def rayleigh_gram_certificate(J, I, c, theta=4) -> RayleighGramCert:
    """Build (and exactly re-check) a concrete Rayleigh/Gram certificate.

    Refuses, in order: a non-square / non-symmetric ``J`` or ``I``; a dimension
    mismatch among ``J``, ``I``, ``c``; a dimension over the cap (25); a
    non-positive threshold ``θ ≤ 0``; a zero direction vector ``c``; a
    non-positive ``cᵀIc`` (the Rayleigh denominator); and — crucially — a
    configuration with ``cᵀJc − θ·cᵀIc ≤ 0`` (the certified inequality would be
    FALSE).  Each refusal is a ``ValueError`` (the negative control), so a false
    inequality is never emitted."""
    Jm = _as_rational_matrix(J, "J")
    Im = _as_rational_matrix(I, "I")
    cv = tuple(sp.Rational(sp.nsimplify(x)) for x in c)
    n = len(Jm)
    if len(Im) != n:
        raise ValueError(
            f"rayleigh_gram REFUSED: dim(J)={n} != dim(I)={len(Im)}")
    if len(cv) != n:
        raise ValueError(
            f"rayleigh_gram REFUSED: dim(J)={n} != len(c)={len(cv)}")
    if n == 0:
        raise ValueError("rayleigh_gram REFUSED: empty matrices (dim 0)")
    if n > _MAX_DIM:
        raise ValueError(
            f"rayleigh_gram REFUSED: dim={n} exceeds the cap {_MAX_DIM} "
            f"(the emitted sum has dim² = {n * n} rational terms)")
    theta = sp.Rational(sp.nsimplify(theta))
    if theta <= 0:
        raise ValueError(
            f"rayleigh_gram REFUSED: threshold θ={theta} ≤ 0 (need θ > 0)")
    if all(x == 0 for x in cv):
        raise ValueError(
            "rayleigh_gram REFUSED: direction vector c is zero "
            "(the Rayleigh quotient is undefined)")
    qJ = _quad_form(Jm, cv)
    qI = _quad_form(Im, cv)
    if not (qI > 0):
        raise ValueError(
            f"rayleigh_gram REFUSED: cᵀIc = {qI} ≤ 0 (the Rayleigh denominator "
            "must be positive)")
    gap = sp.Rational(qJ - theta * qI)
    if not (gap > 0):
        raise ValueError(
            f"rayleigh_gram REFUSED: cᵀJc − θ·cᵀIc = {gap} ≤ 0 — the "
            f"generalized-eigenvalue inequality is FALSE at θ={theta} (honest "
            "refusal; a false inequality is never emitted)")
    return RayleighGramCert(
        dim=n, J=Jm, I=Im, c=cv, theta=theta,
        qJ=sp.Rational(qJ), qI=sp.Rational(qI), gap=gap,
    )


def certify_rayleigh_gram_point(family, pt, name):
    """Certify one Rayleigh/Gram instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(J, I, c[, θ]) = family.special[1](pt)``.  ``n_checks`` counts the
    two exact contractions (``cᵀIc > 0`` and ``cᵀJc − θ·cᵀIc > 0``), both
    re-verified in ``rayleigh_gram_certificate``."""
    spec = family.special[1](pt)
    if len(spec) == 3:
        J, I, c = spec
        theta = 4
    else:
        J, I, c, theta = spec
    cert = rayleigh_gram_certificate(J, I, c, theta)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


def _sum_src(M: tuple[tuple[sp.Rational, ...], ...],
             c: tuple[sp.Rational, ...]) -> str:
    """Spell ``Σᵢⱼ Mᵢⱼ·cᵢ·cⱼ`` as an explicit Lean sum of rational-literal
    products, skipping structurally-zero terms (a zero entry or a zero vector
    component contributes nothing).  Every surviving factor is a rational
    literal, so the kernel re-does the contraction by ``norm_num``."""
    n = len(c)
    terms: list[str] = []
    for i in range(n):
        for j in range(n):
            if M[i][j] == 0 or c[i] == 0 or c[j] == 0:
                continue
            terms.append(
                f"{rat_lean(M[i][j])} * {rat_lean(c[i])} * {rat_lean(c[j])}")
    return " + ".join(terms) if terms else "0"


@dataclass
class RayleighGramEmitter(Emitter):
    """Emit ``theorem <name> : (Σᵢⱼ Jᵢⱼcᵢcⱼ − θ·Σᵢⱼ Iᵢⱼcᵢcⱼ > 0) ∧
    (Σᵢⱼ Iᵢⱼcᵢcⱼ > 0) := by norm_num``, with both Gram contractions spelled out
    as explicit finite double-sums of rational literals.  Self-contained over ℚ;
    the kernel re-does the contraction and closes the sign by ``norm_num``.
    Concrete-instance shadow of the bgp212 Thm 11.1 generalized-eigenvalue bound
    — NOT the variational lemma (the Gram semantics is the trust seam; see the
    module docstring)."""

    def __post_init__(self):
        self.kind = "rayleigh_gram"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: RayleighGramCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            th = rat_lean(cert.theta)
            j_src = _sum_src(cert.J, cert.c)
            i_src = _sum_src(cert.I, cert.c)
            lines.append(
                f"-- {nm}: Rayleigh/Gram generalized-eigenvalue certificate "
                f"(shape of Axiom Math bgp212 Thm 11.1, J_T(F*)−4·I_T(F*)>0):\n"
                f"-- an explicit rational vector certifies a rigorous lower bound "
                f"on the largest\n"
                f"-- generalized eigenvalue λ_max(J,I) ≥ (cᵀJc)/(cᵀIc) > θ.  "
                f"dim={cert.dim}, θ={cert.theta};\n"
                f"-- cᵀJc = {cert.qJ}, cᵀIc = {cert.qI}, "
                f"cᵀJc − θ·cᵀIc = {cert.gap} > 0.  Exact-rational, norm_num.\n"
                f"-- HONESTY: the Gram-matrix SEMANTICS (that J,I are the "
                f"variational integrals of a\n"
                f"-- specific polynomial basis) is the documented generator-side "
                f"input, NOT kernel-checked.\n"
                f"-- conjecture1_proved = False.\n"
                f"theorem {nm} : "
                f"(({j_src} : ℚ) - {th} * ({i_src}) > 0) ∧ "
                f"(({i_src} : ℚ) > 0) := by norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def rayleigh_gram_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Rayleigh/Gram family (kind ``rayleigh_gram``).

    ``spec: pt -> (J, I, c)`` (θ defaults to 4, the bgp212 value) or
    ``(J, I, c, θ)``, with ``J``, ``I`` symmetric rational matrices (sympy
    Matrix or nested sequence) and ``c`` a rational vector.  The theorem is a
    closed rational statement, so a single dummy symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("rayleigh_gram", spec),
        constants=dict(constants or {}),
    )
