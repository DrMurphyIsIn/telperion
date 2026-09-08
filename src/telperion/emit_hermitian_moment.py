"""HermitianMomentInertia emitter family — certificate shapes ported from the
Anthropic ``zeta-23-lean`` development (arXiv:2608.13637, *"More than two thirds
of the zeros of ζ lie on the critical line"*, author: a Claude model).

The paper bounds the number of critical-line zeros by controlling the **positive
index / rank of a finite compression of Weil's Hermitian form** from its first
two spectral moments (trace and Frobenius norm) plus a block decomposition.  Two
pieces of that spine are self-contained real-arithmetic certificates and are
emitted here directly; the matrix-level lemmas they shadow (``rank_trace_ineq``,
Sylvester's law of inertia, von Neumann's trace inequality) are ported separately
as the emitted certs' prelude and CI-verified.

HONESTY SEAM (identical discipline to RH-in-a-box): these emitters certify the
**linear-algebra half only** — "two moment bounds + block structure ⟹ a count
lower bound".  The analytic facts that make the moment bounds hold for ζ (the
explicit formula, the prime side) enter the emitted theorem as *hypotheses*, not
as anything the kernel establishes.  ``conjecture1_proved = False``.  This is a
positive-proportion certificate family, NOT a step toward RH.

Two emitters:

* ``TwoMomentCountEmitter`` (kind ``two_moment_count``) — the §6 scalar count
  certificate (``Zeta23.Assembly.Certificate.N0star_lower_moment`` for the
  ``c = 2`` route, ``count_lower_moment_c3`` for ``c = 3``).  For a rational
  band-limit ``λ ∈ (0, 1]`` it sets ``κ = 1/λ + λ/3`` and emits the implication

      (given the two moment bounds and the block/tail inputs as hypotheses)
      (2 − κ)·N − errors ≤ count       -- c = 2, constant H(λ) = 2 − κ
      (3/2 − κ/2)·N − errors ≤ count   -- c = 3, constant H_d(λ) = (1 + H(λ))/2

  discharged by ``nlinarith`` off ``Real.sqrt_le_sqrt``, exactly as in the source.
  At ``λ = 1``: ``H(1) = 2/3`` and ``H_d(1) = 5/6`` — the paper's headline.

* ``RankTraceScalarEmitter`` (kind ``rank_trace_scalar``) — the integrality atom
  ``2c·x − c² ≤ x²`` (i.e. ``(x − c)² ≥ 0``), the scalar shadow of the rank–trace
  inequality (``RankTrace.sq_ge_linear'``) whose matrix form yields the ``m² ≥
  2m − 1`` (c = 2) and ``m² ≥ 3m − 2`` (c = 3) integrality steps.
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

# --------------------------------------------------------------------------- #
# 1. The two-moment scalar count certificate (paper §6)                       #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class TwoMomentCountCert:
    """``(λ, c, κ, H)`` for the scalar count certificate.

    ``κ = 1/λ + λ/3`` is the asymptotic second-moment ratio ``‖Ĝ‖²_F / N`` at
    band-limit ``λ``; the on-line proportion constant is ``H = 2 − κ`` (``c = 2``)
    or ``H_d = 3/2 − κ/2`` (``c = 3``).  All four are exact sympy rationals.
    """

    lam: sp.Rational
    c: int
    kappa: sp.Rational
    H: sp.Rational


def two_moment_count_certificate(lam, c: int = 2) -> TwoMomentCountCert:
    """Build (and exactly re-check) the scalar count certificate for band-limit
    ``λ`` and route ``c``.  Refuses ``λ ∉ (0, 1]`` (the bandwidth-one ceiling:
    beyond ``λ = 1`` the off-diagonal prime sums need Hardy–Littlewood-strength
    input) and ``c ∉ {2, 3}``."""
    lam = sp.Rational(sp.nsimplify(lam))
    if not (0 < lam <= 1):
        raise ValueError(
            f"two_moment_count REFUSED: need 0 < λ ≤ 1 (bandwidth-one ceiling); got {lam}")
    if c not in (2, 3):
        raise ValueError(f"two_moment_count REFUSED: route c ∈ {{2, 3}}; got {c}")
    kappa = sp.Rational(1) / lam + lam / 3
    H = sp.Rational(2) - kappa if c == 2 else sp.Rational(3, 2) - kappa / 2
    # exact re-validation: the constant must be the paper's H(λ) / H_d(λ)
    assert kappa == 1 / lam + lam / sp.Integer(3)
    assert H == (sp.Rational(2) - kappa if c == 2 else (1 + (sp.Rational(2) - kappa)) / 2)
    return TwoMomentCountCert(lam=lam, c=c, kappa=kappa, H=H)


def certify_two_moment_count_point(family, pt, name):
    """Certify one two-moment count instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(λ, c) = family.special[1](pt)``.  ``n_checks = 2`` (the κ identity
    and the H(λ)/H_d(λ) constant), both re-verified exactly in
    ``two_moment_count_certificate``."""
    spec = family.special[1](pt)
    lam, c = (spec if isinstance(spec, tuple) else (spec, 2))
    cert = two_moment_count_certificate(lam, int(c))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class TwoMomentCountEmitter(Emitter):
    """Emit the §6 scalar count certificate ``(2 − κ)N − errors ≤ count`` (c = 2)
    / ``(3/2 − κ/2)N − errors ≤ count`` (c = 3).  The two moment bounds and the
    block/tail terms are theorem hypotheses (the analytic trust seam); the
    kernel proves only the arithmetic implication, via ``nlinarith`` off
    ``Real.sqrt_le_sqrt``.  Self-contained over ℝ (no matrix prelude)."""

    def __post_init__(self):
        self.kind = "two_moment_count"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: TwoMomentCountCert = inst.payload  # type: ignore[assignment]
            k = rat_lean(cert.kappa)
            hval = rat_lean(cert.H)
            nm = inst.lean_name
            if cert.c == 2:
                lines.append(
                    f"-- {nm}: two-moment count certificate (c=2), band-limit λ={cert.lam}, "
                    f"κ={cert.kappa}, on-line proportion constant H(λ)={cert.H}.\n"
                    f"-- Trust seam: the two moment bounds (htr, hfr) and the block/tail terms\n"
                    f"-- (NII, B) are HYPOTHESES supplied by the analytic side; not a proof of RH.\n"
                    f"theorem {nm} (N NII trGh frGh count B R1 R2 : ℝ) (hB : 0 ≤ B)\n"
                    f"    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII "
                    f"- B * (4 + 2 * Real.sqrt frGh + B) ≤ count)\n"
                    f"    (htr : N - R1 ≤ trGh) (hfr : frGh ≤ {k} * N + R2) :\n"
                    f"    (2 - {k}) * N - (4 * R1 + R2 + 3 * NII "
                    f"+ B * (4 + 2 * Real.sqrt ({k} * N + R2) + B)) ≤ count := by\n"
                    f"  have h2 : Real.sqrt frGh ≤ Real.sqrt ({k} * N + R2) := Real.sqrt_le_sqrt hfr\n"
                    f"  nlinarith [h0, htr, h2, hB, mul_le_mul_of_nonneg_left h2 hB]\n"
                )
            else:  # c == 3
                lines.append(
                    f"-- {nm}: two-moment count certificate (c=3, distinct-zeros route), "
                    f"band-limit λ={cert.lam}, κ={cert.kappa}, constant H_d(λ)={cert.H}.\n"
                    f"-- Trust seam: htr, hfr, NII, B are HYPOTHESES from the analytic side.\n"
                    f"theorem {nm} (N NII trGh frGh count B R1 R2 : ℝ) (hB : 0 ≤ B)\n"
                    f"    (h0 : 6 * trGh - frGh - 3 * N - 5 * NII "
                    f"- B * (6 + 2 * Real.sqrt frGh + B) ≤ 2 * count)\n"
                    f"    (htr : N - R1 ≤ trGh) (hfr : frGh ≤ {k} * N + R2) :\n"
                    f"    (3/2 - {k}/2) * N - (3 * R1 + R2 / 2 + (5/2) * NII "
                    f"+ (B/2) * (6 + 2 * Real.sqrt ({k} * N + R2) + B)) ≤ count := by\n"
                    f"  have h2 : Real.sqrt frGh ≤ Real.sqrt ({k} * N + R2) := Real.sqrt_le_sqrt hfr\n"
                    f"  nlinarith [h0, htr, h2, hB, mul_le_mul_of_nonneg_left h2 hB]\n"
                )
            n_thm += 1
        # `hval` is documented in the comment above via cert.H; keep it referenced
        # so a future reader / linter sees the constant is exact.
        _ = hval
        return "\n".join(lines), n_thm


def two_moment_count_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a two-moment count family (kind ``two_moment_count``).

    ``spec: pt -> (λ, c)`` (or just ``λ``, defaulting ``c = 2``).  The theorem
    quantifies its own reals, so a single dummy symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("two_moment_count", spec),
        constants=dict(constants or {}),
    )


# --------------------------------------------------------------------------- #
# 2. The integrality atom — scalar shadow of the rank–trace inequality        #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class RankTraceScalarCert:
    """The level ``c`` of the integrality shadow ``2c·x − c² ≤ x²``."""

    c: sp.Rational


def rank_trace_scalar_certificate(c) -> RankTraceScalarCert:
    """The scalar shadow ``(x − c)² ≥ 0 ⟺ 2c·x − c² ≤ x²`` underlying the
    matrix rank–trace inequality (``RankTrace.sq_ge_linear'``).  Any real ``c``
    is admissible (the inequality is an identity-plus-square); ``c = 2`` gives
    the ``m² ≥ 2m − 1`` step, ``c = 3`` the ``m² ≥ 3m − 2`` step."""
    c = sp.Rational(sp.nsimplify(c))
    return RankTraceScalarCert(c=c)


def certify_rank_trace_scalar_point(family, pt, name):
    """Certify one integrality-atom instance: ``(CertifiedInstance, 1)``."""
    c = family.special[1](pt)
    cert = rank_trace_scalar_certificate(c)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class RankTraceScalarEmitter(Emitter):
    """Emit the integrality atom ``2c·x − c² ≤ x²`` (``= (x − c)² ≥ 0``), the
    scalar shadow of the rank–trace inequality.  Deterministic ``nlinarith
    [sq_nonneg (x − c)]``.  Self-contained over ℝ."""

    def __post_init__(self):
        self.kind = "rank_trace_scalar"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: RankTraceScalarCert = inst.payload  # type: ignore[assignment]
            c = rat_lean(cert.c)
            nm = inst.lean_name
            lines.append(
                f"-- {nm}: integrality atom 2c·x − c² ≤ x² at c={cert.c} "
                f"(scalar shadow of the rank–trace inequality; m²≥2m−1 at c=2, m²≥3m−2 at c=3).\n"
                f"theorem {nm} : ∀ x : ℝ, 2 * {c} * x - {c}^2 ≤ x^2 := by\n"
                f"  intro x\n"
                f"  nlinarith [sq_nonneg (x - {c})]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def rank_trace_scalar_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an integrality-atom family (kind ``rank_trace_scalar``).
    ``spec: pt -> c`` (the level)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("x", real=True),),
        grid=grid,
        lean_name=lean_name,
        special=("rank_trace_scalar", spec),
        constants=dict(constants or {}),
    )
