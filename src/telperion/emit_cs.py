"""Cauchy–Schwarz / QM–AM emitter — a pairwise-difference SOS symmetric inequality.

A second combinatorial family, distinct from the tangent-line trick: it is
CONSTRAINT-FREE (no ``Σxᵢ = S`` hypothesis) and its certificate is a sum over
PAIRS, not per-term tangents.  For positive weights ``wᵢ``,

    (Σ wᵢ·xᵢ)² ≤ (Σ wᵢ)·(Σ wᵢ·xᵢ²),

which is exactly the identity

    (Σwᵢ)(Σwᵢxᵢ²) − (Σwᵢxᵢ)² = Σ_{i<j} wᵢwⱼ·(xᵢ − xⱼ)²  ≥ 0.

Unweighted (all ``wᵢ = 1``) it is the classic ``(Σxᵢ)² ≤ n·Σxᵢ²`` (QM–AM).  The
emitted Lean is deterministic — ``ring`` proves the identity, ``positivity``
closes the nonnegative pairwise-difference squares, ``linarith`` assembles:

    theorem <name> (x₁ … xₙ : ℝ) : (Σ wᵢ·xᵢ)² ≤ W·(Σ wᵢ·xᵢ²) := by
      have key : W·(Σ wᵢ·xᵢ²) − (Σ wᵢ·xᵢ)² = Σ_{i<j} wᵢwⱼ·(xᵢ − xⱼ)² := by ring
      have hpos : 0 ≤ Σ_{i<j} wᵢwⱼ·(xᵢ − xⱼ)² := by positivity
      linarith [key, hpos]

NEGATIVE CONTROL: a non-positive weight (which breaks the SOS coefficients) is
refused at certification.
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


@dataclass(frozen=True)
class CSCertificate:
    """A verified Cauchy–Schwarz certificate for positive weights."""

    n: int
    weights: tuple            # (w₁, …, wₙ), each > 0
    W: sp.Rational            # Σ wᵢ
    sos_terms: tuple          # ((coeff, (i, j)), …): coeff = wᵢ·wⱼ, base = xᵢ − xⱼ


def cs_certificate(weights: Sequence) -> CSCertificate:
    """Build and EXACTLY self-check a Cauchy–Schwarz certificate.  Refuses a
    non-positive weight or n < 2."""
    ws = [sp.nsimplify(w) for w in weights]
    n = len(ws)
    if n < 2:
        raise ValueError("Cauchy–Schwarz needs n ≥ 2 terms")
    if any(w <= 0 for w in ws):
        raise ValueError(f"Cauchy–Schwarz needs strictly positive weights; got {ws}")
    W = sum(ws)
    sos = [(ws[i] * ws[j], (i + 1, j + 1)) for i in range(n) for j in range(i + 1, n)]
    # exact self-check of the SOS identity
    xs = sp.symbols(f"x1:{n + 1}")
    lhs = W * sum(ws[i] * xs[i] ** 2 for i in range(n)) - (sum(ws[i] * xs[i] for i in range(n))) ** 2
    rhs = sum(c * (xs[i - 1] - xs[j - 1]) ** 2 for c, (i, j) in sos)
    if sp.expand(lhs - rhs) != 0:
        raise ValueError("Cauchy–Schwarz SOS self-check failed — certificate rejected")
    return CSCertificate(n=n, weights=tuple(ws), W=sp.nsimplify(W), sos_terms=tuple(sos))


def certify_cs_point(family, pt, name):
    """Certify one Cauchy–Schwarz instance from ``family.special[1](pt) -> weights``."""
    weights = family.special[1](pt)
    cert = cs_certificate(weights)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class CauchySchwarzEmitter(Emitter):
    """Emit `(Σ wᵢxᵢ)² ≤ W·(Σ wᵢxᵢ²)` — one theorem per instance, closed
    deterministically by `ring` (identity) + `positivity` + `linarith`."""

    def __post_init__(self):
        self.kind = "cauchy_schwarz"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: CSCertificate = inst.payload  # type: ignore[assignment]
            n = cert.n
            ws = cert.weights
            binders = " ".join(f"x{i}" for i in range(1, n + 1))
            sum_wx = " + ".join(f"{rat_lean(ws[i - 1])} * x{i}" for i in range(1, n + 1))
            sum_wx2 = " + ".join(f"{rat_lean(ws[i - 1])} * x{i}^2" for i in range(1, n + 1))
            sos = " + ".join(
                f"{rat_lean(c)} * (x{i} - x{j})^2" for c, (i, j) in cert.sos_terms
            )
            W = rat_lean(cert.W)
            lines.append(
                f"theorem {inst.lean_name} ({binders} : ℝ) :\n"
                f"    ({sum_wx})^2 ≤ {W} * ({sum_wx2}) := by\n"
                f"  have key : {W} * ({sum_wx2}) - ({sum_wx})^2 = {sos} := by ring\n"
                f"  have hpos : (0:ℝ) ≤ {sos} := by positivity\n"
                f"  linarith [key, hpos]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def cauchy_schwarz_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Cauchy–Schwarz family (kind='cauchy_schwarz').

    ``spec``: a callable ``pt -> weights`` returning a sequence of strictly
    positive rational weights (length n ≥ 2).  Refuses a non-positive weight."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("cauchy_schwarz", spec),
        constants=dict(constants or {}),
    )
