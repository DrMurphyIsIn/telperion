"""AutocorrSupport emitter (kind ``autocorr_support``) — the support-geometry
autocorrelation bound, ported from anthropics/zeta-23-lean ``Taper/Decay.lean``
(``autocorr_le_of_support``).

Analytic lemma being instantiated
---------------------------------
For a taper ``v`` supported in ``(−M, M)`` with ``0 ≤ v ≤ 1``, the (continuous)
autocorrelation ``(v ⋆ v)(y) = ∫ v(x) v(x − y) dx`` is bounded by the support
triangle::

    (v ⋆ v)(y) ≤ (2M − |y|)₊        [= max 0 (2M − |y|)]

with EQUALITY exactly for the box ``v = 1_{[−M, M]}`` (the widest admissible
taper).  That is the general analytic fact ``autocorr_le_of_support``; the box
saturates it.

What this emitter certifies (the honest self-contained form)
------------------------------------------------------------
The box realization is an equality, hence ``X ≤ X`` — vacuous.  To emit a REAL,
non-trivial, kernel-checkable rational inequality we instantiate the lemma on a
**finite nonnegative simple step taper**::

    v = Σ_i c_i · 1_{[i, i+1)}    on  [0, K),   K = 2M,   c_i ∈ [0, 1]

whose autocorrelation at an INTEGER shift ``k`` is the exact discrete
autocorrelation ``Σ_i c_i c_{i+|k|}`` (rational).  The box (all ``c_i = 1``)
gives ``Σ_i 1 = (K − |k|) = (2M − |k|)₊`` exactly, so for any admissible taper::

    (v ⋆ v)(k) = Σ_i c_i c_{i+|k|} ≤ Σ_i 1 = (2M − |k|)₊

with STRICT inequality whenever some overlapping ``c_i < 1``.  Each emitted
sample is therefore a genuine rational inequality ``a_k ≤ max 0 (2M − |k|)`` with
``a_k`` the computed exact autocorrelation value — checked by ``norm_num``.

The generator supplies ``M : ℚ`` (> 0), the coefficient vector ``c`` (length
``K = 2M``, entries in ``[0, 1]``), and a finite list of integer sample shifts.
The certificate builder REFUSES ``M ≤ 0``, a length mismatch ``len(c) ≠ 2M``, any
``c_i ∉ [0, 1]``, any sample whose computed LHS exceeds the RHS (honest refusal),
and a wholly-slack-free (all-equality) sample set (that would be the vacuous box
case — deferred to the analytic lemma, not shipped as a real inequality here).

HONESTY: this is a real, non-vacuous rational inequality — the linear-algebra /
combinatorial shadow of ``autocorr_le_of_support`` at integer shifts.  It does
NOT prove the general continuous convolution bound (the analytic lemma, whose
support geometry it instantiates).  ``conjecture1_proved = False``.
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
class AutocorrSupportCert:
    """One box-supported step-taper autocorrelation certificate.

    ``M`` is the (rational) half-support; ``coeffs`` are the unit-cell values
    ``c_i ∈ [0, 1]`` of the simple taper on ``[0, 2M)`` (so ``len(coeffs) = 2M``);
    ``samples`` is a tuple of ``(shift, lhs, rhs)`` triples with ``lhs`` the exact
    discrete autocorrelation ``Σ_i c_i c_{i+|shift|}`` and ``rhs = max 0 (2M −
    |shift|)`` the support-triangle bound.  Every triple satisfies ``lhs ≤ rhs``
    and at least one is strict (non-vacuity)."""

    M: sp.Rational
    coeffs: tuple
    samples: tuple  # ((shift: sp.Integer, lhs: sp.Rational, rhs: sp.Rational), ...)


def _discrete_autocorr(coeffs: Sequence[sp.Rational], k: int) -> sp.Rational:
    """Exact ``Σ_i c_i c_{i+|k|}`` (0 when ``|k| ≥ len``)."""
    k = abs(int(k))
    K = len(coeffs)
    if k >= K:
        return sp.Integer(0)
    return sp.Add(*(coeffs[i] * coeffs[i + k] for i in range(K - k)), evaluate=True)


def autocorr_support_certificate(M, coeffs, shifts) -> AutocorrSupportCert:
    """Build (and exactly re-check) the step-taper autocorrelation certificate.

    Refuses: ``M ≤ 0``; a coefficient vector whose length ``≠ 2M`` (the support
    width must be exactly the box width ``2M`` for the triangle to be the sharp
    bound); any ``c_i ∉ [0, 1]``; any sample whose computed autocorrelation
    exceeds the triangle bound (that would be a false claim); a sample set with
    NO strict inequality (the vacuous box/equality case — deferred to the
    analytic lemma rather than shipped as an ``X ≤ X`` tautology)."""
    M = sp.Rational(sp.nsimplify(M))
    if M <= 0:
        raise ValueError(f"autocorr_support REFUSED: need M > 0; got {M}")
    coeffs = tuple(sp.Rational(sp.nsimplify(c)) for c in coeffs)
    if len(coeffs) != 2 * M:
        raise ValueError(
            f"autocorr_support REFUSED: taper width len(coeffs)={len(coeffs)} "
            f"must equal 2M={2 * M} (box-matched support)")
    for i, c in enumerate(coeffs):
        if not (0 <= c <= 1):
            raise ValueError(
                f"autocorr_support REFUSED: coefficient c[{i}]={c} outside [0, 1]")
    samples = []
    any_strict = False
    for s in shifts:
        s = sp.Integer(int(s))
        lhs = _discrete_autocorr(coeffs, int(s))
        rhs = sp.Max(sp.Integer(0), 2 * M - abs(s))
        if lhs > rhs:
            raise ValueError(
                f"autocorr_support REFUSED: at shift {s} the computed "
                f"autocorrelation {lhs} exceeds the support-triangle bound {rhs} "
                "— a false claim")
        if lhs < rhs:
            any_strict = True
        samples.append((s, lhs, rhs))
    if not any_strict:
        raise ValueError(
            "autocorr_support REFUSED: every sample is an EQUALITY (the box case) "
            "— that is the vacuous X ≤ X tautology; supply a taper with some "
            "c_i < 1 in an overlap, or defer to the analytic autocorr_le_of_support")
    return AutocorrSupportCert(M=M, coeffs=coeffs, samples=tuple(samples))


def certify_autocorr_support_point(family, pt, name):
    """Certify one autocorr-support instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(M, coeffs, shifts) = family.special[1](pt)``.  ``n_checks`` is the
    number of samples (each an exactly-verified ``lhs ≤ rhs``)."""
    M, coeffs, shifts = family.special[1](pt)
    cert = autocorr_support_certificate(M, coeffs, shifts)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.samples)


@dataclass
class AutocorrSupportEmitter(Emitter):
    """Emit, per instance, the finite family of exact rational autocorrelation
    bounds ``a_k ≤ max 0 (2*M − |k|)`` for a box-supported step taper — the
    integer-shift shadow of ``Taper/Decay.autocorr_le_of_support``.  Each fact is
    a genuine rational inequality closed by ``norm_num`` (strict wherever the
    taper drops below the box).  Self-contained over ℚ (no Mathlib prelude)."""

    def __post_init__(self):
        self.kind = "autocorr_support"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: AutocorrSupportCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            m = rat_lean(cert.M)
            cvec = ", ".join(rat_lean(c) for c in cert.coeffs)
            # explicit (shift, autocorrelation-value) pairs
            pairs = ", ".join(
                f"({rat_lean(s)}, {rat_lean(lhs)})" for s, lhs, _ in cert.samples)
            n_strict = sum(1 for _, lhs, rhs in cert.samples if lhs < rhs)
            lines.append(
                f"-- {nm}: autocorrelation support bound (v ⋆ v)(k) ≤ (2M − |k|)₊ for a\n"
                f"-- box-supported nonneg step taper v = Σ c_i·1_[i,i+1) on [0, 2M), M={cert.M},\n"
                f"-- c=[{cvec}].  Integer-shift shadow of Taper/Decay.autocorr_le_of_support\n"
                f"-- (the analytic support-geometry lemma this instantiates); box saturates it.\n"
                f"-- {n_strict}/{len(cert.samples)} samples are STRICT (taper < box). Real rational\n"
                f"-- inequality by norm_num; NOT a proof of the general convolution bound. RH: no.\n"
                f"theorem {nm} :\n"
                f"    ∀ p ∈ ([{pairs}] : List (ℚ × ℚ)),\n"
                f"      p.2 ≤ max 0 (2 * ({m}) - |p.1|) := by\n"
                f"  intro p hp\n"
                f"  fin_cases hp <;> norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def autocorr_support_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an autocorr-support family (kind ``autocorr_support``).

    ``spec: pt -> (M, coeffs, shifts)`` — ``M`` a positive rational half-support,
    ``coeffs`` the length-``2M`` unit-cell taper values in ``[0, 1]``, ``shifts`` a
    finite list of integer sample shifts.  The theorem quantifies over the
    explicit sample list, so a single dummy symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("y", real=True),),
        grid=grid,
        lean_name=lean_name,
        special=("autocorr_support", spec),
        constants=dict(constants or {}),
    )
