"""SpacingTailBound emitter — a concrete-instance shadow of the uniform spacing
tail bound from ``anthropics/zeta-23-lean`` (``MV/Spacing.lean``, ``spacing_sq`` /
``spacing_four``).

The analytic lemma being instantiated says: for a family of well-separated
centers ``f_i`` with radii ``δ_i`` (pairwise separation ``(δ_s + δ_t)/2 ≤
|f_s − f_t|``), the *spacing tail* is uniformly controlled by the distinguished
radius,

    Σ_{t ≠ s} δ_t / (f_s − f_t)²  ≤  9 / δ_s          (``spacing_sq``)
    Σ_{t ≠ s} δ_t / (f_s − f_t)⁴  ≤  27 / δ_s³         (``spacing_four``)

The constants ``9`` and ``27`` are the *uniform* analytic content — that a
single ``δ_s``-controlled bound holds for EVERY admissible configuration.

This emitter certifies the SELF-CONTAINED CONCRETE-INSTANCE form: given a finite,
exact-rational configuration ``(s, f_i, δ_i)`` satisfying admissibility, the sum
is an exact rational and the bound is a rational inequality the Lean kernel
closes by ``norm_num``.  The emitted theorem is written with the sum spelled out
as an explicit finite sum of rational literals — no ``Finset``, no analysis.

HONESTY SEAM.  The emitted theorem is a TRUE, NON-VACUOUS, ``norm_num``-decidable
rational inequality about the CONCRETE configuration.  It does NOT prove the
general/uniform ``9/δ`` (or ``27/δ³``) bound — that uniform statement, holding
for every admissible family, is the analytic lemma this instantiates and lives
only in the provenance.  The generator's gate refuses any configuration whose
exact rational sum does NOT satisfy the bound, so a false inequality is never
emitted (honest refusal).  ``conjecture1_proved = False``.  This is a
positive-instance witness family, NOT a step toward RH.
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
class SpacingTailCert:
    """One certified concrete spacing-tail instance.

    ``s`` — index of the distinguished center in ``centers`` / ``radii``.
    ``centers`` — the ``f_i : ℚ`` (exact rationals).
    ``radii`` — the ``δ_i : ℚ``, all ``> 0``.
    ``power`` — 2 (``spacing_sq``, bound ``9/δ_s``) or 4 (``spacing_four``,
        bound ``27/δ_s³``).
    ``lhs_sum`` — the exact rational value of ``Σ_{t≠s} δ_t/(f_s−f_t)^power``.
    ``rhs`` — the exact rational bound (``9/δ_s`` or ``27/δ_s³``).
    """

    s: int
    centers: tuple[sp.Rational, ...]
    radii: tuple[sp.Rational, ...]
    power: int
    lhs_sum: sp.Rational
    rhs: sp.Rational


def spacing_tail_bound_certificate(
    s: int,
    centers: Sequence,
    radii: Sequence,
    power: int = 2,
) -> SpacingTailCert:
    """Build (and exactly re-check) a concrete spacing-tail certificate.

    Refuses, in order: a bad power; a bad distinguished index; a length
    mismatch; a non-positive radius; a repeated center (``f_s = f_t``); a
    violated admissibility separation ``(δ_s + δ_t)/2 ≤ |f_s − f_t|``; and —
    crucially — a configuration whose exact rational tail sum does NOT satisfy
    ``≤ 9/δ_s`` (power 2) / ``≤ 27/δ_s³`` (power 4).  Each refusal is a
    ``ValueError`` (the negative control), so a false inequality is never
    emitted."""
    if power not in (2, 4):
        raise ValueError(
            f"spacing_tail_bound REFUSED: power ∈ {{2, 4}} "
            f"(spacing_sq / spacing_four); got {power}")
    f = tuple(sp.Rational(sp.nsimplify(c)) for c in centers)
    d = tuple(sp.Rational(sp.nsimplify(r)) for r in radii)
    n = len(f)
    if len(d) != n:
        raise ValueError(
            f"spacing_tail_bound REFUSED: |centers|={n} ≠ |radii|={len(d)}")
    if not (0 <= s < n):
        raise ValueError(
            f"spacing_tail_bound REFUSED: distinguished index s={s} out of "
            f"range [0, {n})")
    if n < 2:
        raise ValueError(
            "spacing_tail_bound REFUSED: need at least one t ≠ s "
            "(non-vacuous tail)")
    for i, di in enumerate(d):
        if di <= 0:
            raise ValueError(
                f"spacing_tail_bound REFUSED: radius δ_{i}={di} ≤ 0 "
                "(radii must be positive)")
    ds = d[s]
    fs = f[s]
    # admissibility + coincident-center gate, and accumulate the exact tail sum
    lhs_sum = sp.Integer(0)
    for t in range(n):
        if t == s:
            continue
        gap = fs - f[t]
        if gap == 0:
            raise ValueError(
                f"spacing_tail_bound REFUSED: coincident centers f_{s}=f_{t}"
                f"={fs} (the tail term is singular)")
        sep = (ds + d[t]) / 2
        if not (sep <= abs(gap)):
            raise ValueError(
                f"spacing_tail_bound REFUSED: admissibility violated at t={t}: "
                f"(δ_{s}+δ_{t})/2 = {sep} > |f_{s}−f_{t}| = {abs(gap)}")
        lhs_sum += d[t] / gap**power
    rhs = sp.Rational(9) / ds if power == 2 else sp.Rational(27) / ds**3
    if not (lhs_sum <= rhs):
        raise ValueError(
            f"spacing_tail_bound REFUSED: exact tail sum {lhs_sum} exceeds the "
            f"bound {rhs} — the concrete inequality is FALSE (honest refusal; "
            "a false inequality is never emitted)")
    return SpacingTailCert(
        s=s, centers=f, radii=d, power=power,
        lhs_sum=sp.Rational(lhs_sum), rhs=sp.Rational(rhs),
    )


def certify_spacing_tail_bound_point(family, pt, name):
    """Certify one spacing-tail instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(s, centers, radii[, power]) = family.special[1](pt)``.  ``n_checks``
    counts the gates exercised: one per admissibility pair (t ≠ s) plus the final
    exact-sum-vs-bound comparison, all re-verified in
    ``spacing_tail_bound_certificate``."""
    spec = family.special[1](pt)
    if len(spec) == 3:
        s, centers, radii = spec
        power = 2
    else:
        s, centers, radii, power = spec
    cert = spacing_tail_bound_certificate(s, centers, radii, int(power))
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = (len(cert.centers) - 1) + 1  # one per tail pair + the bound check
    return inst, n_checks


@dataclass
class SpacingTailBoundEmitter(Emitter):
    """Emit ``theorem <name> : (Σ_{t≠s} δ_t/(f_s−f_t)^p) ≤ B := by norm_num``,
    with the sum spelled out as an explicit finite sum of rational literals and
    ``B = 9/δ_s`` (p=2) / ``27/δ_s³`` (p=4).  Self-contained over ℚ; the kernel
    closes it by ``norm_num``.  Concrete-instance shadow of the uniform spacing
    bound — NOT the uniform lemma (see module docstring)."""

    def __post_init__(self):
        self.kind = "spacing_tail_bound"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: SpacingTailCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            s = cert.s
            fs = cert.centers[s]
            p = cert.power
            terms = []
            for t in range(len(cert.centers)):
                if t == s:
                    continue
                gap = fs - cert.centers[t]
                terms.append(
                    f"{rat_lean(cert.radii[t])} / {rat_lean(gap)}^{p}")
            sum_src = " + ".join(terms)
            rhs_src = rat_lean(cert.rhs)
            const = 9 if p == 2 else 27
            denom_desc = "δ_s" if p == 2 else "δ_s^3"
            lines.append(
                f"-- {nm}: concrete instance of the spacing tail bound "
                f"(MV/Spacing {'spacing_sq' if p == 2 else 'spacing_four'}).\n"
                f"-- Distinguished index s={s}, δ_s={cert.radii[s]}; admissible "
                f"config (pairwise (δ_s+δ_t)/2 ≤ |f_s−f_t|).\n"
                f"-- Σ_{{t≠s}} δ_t/(f_s−f_t)^{p} = {cert.lhs_sum} ≤ "
                f"{const}/{denom_desc} = {cert.rhs}.  Exact-rational, norm_num.\n"
                f"-- HONESTY: this is the CONCRETE instance, not the uniform "
                f"{const}/{denom_desc} lemma it instantiates.\n"
                f"theorem {nm} : ({sum_src}) ≤ {rhs_src} := by norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def spacing_tail_bound_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a spacing-tail family (kind ``spacing_tail_bound``).

    ``spec: pt -> (s, centers, radii)`` (power defaults to 2) or
    ``(s, centers, radii, power)``.  The theorem is a closed rational
    inequality, so a single dummy symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("spacing_tail_bound", spec),
        constants=dict(constants or {}),
    )
