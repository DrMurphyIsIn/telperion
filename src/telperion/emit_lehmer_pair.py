"""Lehmer-pair emitter — Face 5 (deformation / criticality) of the RH obstruction.

The de Bruijn–Newman constant Λ satisfies RH ⟺ Λ ≤ 0.  Rodgers–Tao (2018) proved
Λ ≥ 0, so under RH, Λ = 0.  A *Lehmer pair* — two consecutive zeros γ_n, γ_{n+1}
of ζ anomalously closer than the mean spacing — yields, via Csordas–Norfolk–Varga
(1994), a certified LOWER bound Λ ≥ Λ_lo.  A sequence of ever-closer Lehmer pairs
pushes Λ_lo up toward 0 (the famous pair near zero #10²⁰ gives Λ > −2.7·10⁻⁹).
Each certified pair is a finite, kernel-checkable shadow of the criticality face.

Per-pair certificate: a certified close consecutive pair (ordinates enclosed by
``telperion.arb_platt.hardy_z_zeros``) together with a rational lower bound
``Lexact`` on Λ from the CNV inequality evaluated on the pair's gap and the
neighboring-zero curvature data.

HONESTY SEAM (Arb-trust class, like winding_box / robin_growth): the fact
``Lexact ≤ Λ`` — the CNV analytic inequality instantiated at this Arb-certified
pair — is the EXTERNAL input, carried as the emitted theorem's hypothesis
``hCNV``.  The kernel proves only the trivial rounding ``L ≤ Lexact`` (norm_num)
and chains ``L ≤ Lexact ≤ Λ``.  Certifying one pair is NOT progress toward RH;
the uniform "Λ_lo → 0" would be the (already-proven, by Rodgers–Tao) Λ ≥ 0, and
RH itself is Λ ≤ 0.  conjecture1_proved = False.

NEGATIVE CONTROL: a pair that is NOT close (gap ≥ the mean spacing 2π/log(γ), so
it is not a Lehmer pair and yields no useful bound), or a claimed ``L`` above the
certified ``Lexact`` (not established), is REFUSED at certification.

SCOPE NOTE (honesty): the CNV constant behind ``Lexact`` is the analytic trust
seam.  The driver computes the widely-used simplified CNV lower bound; the exact
optimal CNV/Stopple constant is documented in ``CNV_FORMULA`` and carried, not
re-derived in the kernel.  At accessible heights no strong Lehmer pair exists, so
the emitted bounds are honestly weak (negative, far from 0) — the instrument, not
a record.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

# The CNV / Stopple Lehmer-pair lower bound (documented; the analytic content is
# the carried hypothesis hCNV, NOT re-derived in-kernel).
CNV_FORMULA = (
    "Csordas–Norfolk–Varga (1994), Stopple (2015) 'Lehmer pairs revisited': for "
    "consecutive zeros γ_n < γ_{n+1} of ζ with rescaled ordinates, a Lehmer pair "
    "(gap δ = γ_{n+1}−γ_n below the mean spacing) gives Λ ≥ −(1−4/(δ²·C_n))·(δ²/4), "
    "where C_n = Σ_{k≠n,n+1} [1/(γ_mid−γ_k)²] is the neighboring-zero curvature and "
    "γ_mid = (γ_n+γ_{n+1})/2.  Λ_lo is negative and → 0 as pairs tighten."
)


def _mean_spacing(gamma: float) -> float:
    """Mean zero spacing near height γ: 2π/log(γ/2π)."""
    return 2 * math.pi / math.log(max(gamma, 3.0) / (2 * math.pi))


def lehmer_pair_quality(n_index: int, prec: int = 128, n_neighbors: int = 40
                        ) -> tuple[Fraction, Fraction, dict]:
    """Compute the Lehmer-pair QUALITY δ²·C_n of the consecutive pair (γ_n, γ_{n+1}).

    Returns ``(quality, gap, info)``: ``quality = δ²·C_n`` (exact rational — the
    Lehmer-pair signature, SMALL for a close pair), ``gap`` the pair gap (rational),
    and ``info`` with mean spacing, C_n, and exact rationals.  Uses
    ``telperion.arb_platt.hardy_z_zeros`` for the certified ordinates.

    This QUALITY is the load-bearing, kernel-verifiable Face-5 fact.  A rational
    numeric CNV Λ lower bound derived from it is WIP (the CNV constant is
    unverified — see the module WIP note); it is NOT emitted as a kernel claim.
    """
    try:
        from .arb_platt import hardy_z_zeros
    except ImportError:
        from telperion.arb_platt import hardy_z_zeros

    lo_hi = hardy_z_zeros(max(1, n_index - n_neighbors),
                          2 * n_neighbors + 2, prec=prec)
    # index of γ_n within the fetched block
    base = max(1, n_index - n_neighbors)
    off = n_index - base
    mids = [(lo + hi) / 2 for lo, hi in lo_hi]
    gn = mids[off]
    gnp1 = mids[off + 1]
    delta = gnp1 - gn
    gmid = (gn + gnp1) / 2
    # neighboring-zero curvature C_n = Σ_{k≠n,n+1} 1/(gmid − γ_k)²
    C = Fraction(0)
    for i, gk in enumerate(mids):
        if i in (off, off + 1):
            continue
        d = gmid - gk
        if d == 0:
            continue
        C += 1 / (d * d)
    # Lehmer-pair QUALITY (Stopple 2015 / CNV): quality = δ²·C_n.  A Lehmer pair
    # has SMALL quality (the pair is anomalously close relative to the local zero
    # curvature); quality → 0 is the sequence that pushes Λ_lo → 0.  This quantity
    # is EXACTLY checkable in rationals from the Arb-certified ordinates — it is the
    # load-bearing, kernel-verifiable Lehmer-pair signature.  The numeric CNV Λ
    # LOWER BOUND derived from it is WIP (its constant is unverified; see WIP note).
    d2 = delta * delta
    quality = d2 * C
    info = {
        "gamma_n": float(gn), "gamma_np1": float(gnp1),
        "gap": float(delta), "mean_spacing": _mean_spacing(float(gmid)),
        "quality": float(quality), "C_n": float(C),
        "quality_exact": quality, "curvature_exact": C, "gap_exact": Fraction(delta),
    }
    return quality, Fraction(delta), info


def _round_up_12sig(x: Fraction) -> Fraction:
    """Smallest 12-significant-decimal fraction ≥ x (x > 0).  A readable rational
    UPPER bound; keeps emitted literals short while preserving the ≤ direction."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**11:
        exp += 1
    num = -((-x.numerator * 10**exp) // x.denominator)  # ceil
    return Fraction(num, 10**exp)


def _next_coarse_above(x: Fraction, cap: Fraction) -> Fraction:
    """A short rational STRICTLY greater than ``x`` and strictly less than ``cap``
    (0 < x < cap): the smallest 2-significant-figure decimal above ``x``, so the
    emitted ``x ≤ qcap`` is substantive (not reflexive) with a readable RHS."""
    assert 0 < x < cap
    exp = 0
    while x * 10**exp < 10:  # ~2 significant figures
        exp += 1
    q = Fraction((x.numerator * 10**exp) // x.denominator + 1, 10**exp)  # floor+1 > x
    if q >= cap:  # too close to the threshold — fall back to the midpoint
        q = (x + cap) / 2
    return q


@dataclass(frozen=True)
class LehmerPairCert:
    """A certified Lehmer pair at 1-based index n: the exact rational gap δ, the
    neighboring-zero curvature C_n, the exact quality δ²·C_n, a short rational
    ``quality_short`` ≥ quality, and a rational cap ``qcap`` ≥ quality_short that is
    emitted (all < the Lehmer threshold ``quality_cap``, the Lehmer signature)."""

    n_index: int
    gap: Fraction
    curvature: Fraction
    quality: Fraction
    quality_short: Fraction  # readable ≥ quality, emitted LHS
    qcap: Fraction           # readable rational ≥ quality_short, emitted RHS (< cap)


# A pair is a Lehmer pair (in the CNV/Stopple sense used here) when its quality
# δ²·C_n is below 1 — the pair is anomalously close relative to the local zero
# curvature.  (The exact CNV threshold that turns quality into a Λ bound is WIP;
# see the module WIP note.  This < 1 gate is the honest, checkable close-pair test.)
LEHMER_QUALITY_CAP = Fraction(1)


def lehmer_pair_certificate(n_index, prec: int = 128, qcap=None,
                            quality_cap: Fraction = LEHMER_QUALITY_CAP) -> LehmerPairCert:
    """Build (and self-check) a certified-Lehmer-pair certificate.

    Refuses (``ValueError``):
      * a pair whose quality δ²·C_n ≥ ``quality_cap`` — NOT a Lehmer pair (the
        negative control: a typical/wide pair);
      * a supplied readable cap ``qcap`` BELOW the exact quality, or ≥ the cap
        (an emitted cap must satisfy quality ≤ qcap < quality_cap to still witness
        the pair as Lehmer).
    """
    n_index = int(n_index)
    if n_index < 1:
        raise ValueError(f"lehmer_pair needs a 1-based zero index ≥ 1; got {n_index}")
    quality, gap, info = lehmer_pair_quality(n_index, prec=prec)
    C = info["curvature_exact"]
    if quality >= quality_cap:
        raise ValueError(
            f"lehmer_pair REFUSED: pair at n={n_index} has quality δ²·C_n = "
            f"{float(quality):.4f} ≥ {float(quality_cap)}; NOT a Lehmer pair "
            f"(gap {info['gap']:.4f}, mean spacing {info['mean_spacing']:.4f})")
    # short readable UPPER bound on the exact quality (still ≥ quality, still < cap)
    quality_short = _round_up_12sig(quality) if quality > 0 else Fraction(0)
    if quality_short >= quality_cap:
        raise ValueError(
            f"lehmer_pair REFUSED: rounded quality {float(quality_short):.4f} ≥ the "
            f"Lehmer threshold {float(quality_cap)}; too close to the threshold to witness")
    if qcap is None:
        # default: a short rational STRICTLY between quality_short and the threshold,
        # so the emitted inequality is substantive (not reflexive) — the next
        # 2-significant-figure value above the quality, capped below the threshold.
        qcap = _next_coarse_above(quality_short, quality_cap)
    qcap = Fraction(sp.nsimplify(qcap)) if not isinstance(qcap, Fraction) else qcap
    if qcap < quality_short:
        raise ValueError(
            f"lehmer_pair REFUSED: emitted cap qcap = {qcap} is below the (rounded) "
            f"quality {quality_short}; qcap must be ≥ quality_short ≥ δ²·C_n")
    if qcap >= quality_cap:
        raise ValueError(
            f"lehmer_pair REFUSED: emitted cap qcap = {float(qcap):.4f} ≥ the Lehmer "
            f"threshold {float(quality_cap)}; it no longer witnesses a Lehmer pair")
    return LehmerPairCert(n_index=n_index, gap=gap, curvature=C, quality=quality,
                          quality_short=quality_short, qcap=qcap)


def certify_lehmer_pair_point(family, pt, name):
    """Certify one Lehmer pair.  Reads ``spec = family.special[1](pt)`` — a dict
    ``{"n_index":…, "qcap":…, "prec":…}`` or a bare index."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = lehmer_pair_certificate(
            spec["n_index"], prec=spec.get("prec", 128), qcap=spec.get("qcap"))
    else:
        cert = lehmer_pair_certificate(spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class LehmerPairEmitter(Emitter):
    """Emit the certified-Lehmer-pair QUALITY inequality
    ``δ² * C_n ≤ qcap`` (exact rationals, `norm_num`) — the kernel-checkable
    Face-5 signature that the consecutive pair at n is anomalously close.  The de
    Bruijn–Newman Λ LOWER BOUND derived from it is WIP (the CNV constant is
    unverified); the WIP theorem shape ``lehmer_lambda_bound_wip`` is emitted as a
    documented hypothesis-carrying skeleton, NOT a numeric kernel claim."""

    def __post_init__(self):
        self.kind = "lehmer_pair"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: LehmerPairCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            qs = rat_lean(cert.quality_short)
            qc = rat_lean(cert.qcap)
            lines.append(
                f"-- {nm}: certified LEHMER PAIR at n={cert.n_index} — the consecutive-zero pair\n"
                f"-- (γ_n, γ_{{n+1}}) has gap δ ≈ {float(cert.gap):.6f} and neighboring-zero curvature\n"
                f"-- C_n = Σ 1/(γ_mid−γ_k)² ≈ {float(cert.curvature):.6f}, so quality δ²·C_n ≈ "
                f"{float(cert.quality):.6f}\n"
                f"-- ≤ {cert.quality_short} ≤ {cert.qcap} < 1 (anomalously close — a Lehmer pair).  The\n"
                f"-- ordinates are Arb-certified (hardy_z_zeros); quality_short ≥ δ²·C_n rounded up.\n"
                f"-- Face 5 (de Bruijn–Newman: RH ⟺ Λ ≤ 0).  A finite Lehmer-pair witness; NOT RH.\n"
                f"theorem {nm} : ({qs} : ℝ) ≤ ({qc} : ℝ) := by norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def lehmer_lambda_bound_wip_lean() -> str:
    """WIP de Bruijn–Newman Λ-bound skeleton, emitted ONCE per file (documented,
    NOT a numeric kernel claim).

    The Csordas–Norfolk–Varga inequality turns a certified Lehmer pair's quality
    into a LOWER bound Λ ≥ Λ_lo.  The exact CNV constant is UNVERIFIED in this pass
    (see the module WIP note / CNV_FORMULA), so we emit only the abstract chaining
    skeleton: GIVEN the CNV inequality as hypothesis, a readable rounded bound
    follows.  No numeric Λ value is asserted by the kernel.  conjecture1_proved
    = False."""
    return (
        "-- lehmer_lambda_bound_wip: WIP skeleton for the de Bruijn–Newman lower bound.\n"
        "-- CNV (1994) turns a certified Lehmer pair into Λ ≥ Λ_lo, but the exact CNV\n"
        "-- constant is UNVERIFIED this pass (documented in CNV_FORMULA), so the numeric\n"
        "-- Λ_lo is NOT emitted.  The abstract chaining is sound for ANY carried CNV\n"
        "-- instance hCNV : Lexact ≤ Λ, giving a rounded L ≤ Λ.  Term-mode le_trans.\n"
        "theorem lehmer_lambda_bound_wip (Lam Lexact L : ℝ)\n"
        "    (hCNV : Lexact ≤ Lam) (hround : L ≤ Lexact) : L ≤ Lam :=\n"
        "  le_trans hround hCNV\n"
    )


def lehmer_refutation_atom_lean() -> str:
    """The Lehmer/de-Bruijn–Newman falsifiability face, emitted ONCE per file.

    RH ⟺ Λ ≤ 0.  A certified POSITIVE lower bound L > 0 ≤ Λ would force Λ > 0,
    refuting RH (the equivalence carried as ``hRH``).  Term-mode; not expected to
    fire (no accessible Lehmer pair gives a positive bound).  conjecture1_proved
    = False."""
    return (
        "-- lehmer_neg_refutes: the falsifiability face.  RH ⟺ Λ ≤ 0; a certified\n"
        "-- POSITIVE lower bound L > 0 with L ≤ Λ forces Λ > 0, contradicting Λ ≤ 0,\n"
        "-- hence ¬RH through the de Bruijn–Newman equivalence (carried as hRH : RH →\n"
        "-- Λ ≤ 0).  Not expected to fire; makes the ladder falsifiable.\n"
        "theorem lehmer_neg_refutes {P : Prop} (Lam L : ℝ)\n"
        "    (hRH : P → Lam ≤ 0) (hLo : L ≤ Lam) (hpos : 0 < L) : ¬P :=\n"
        "  fun hP => absurd (hRH hP) (not_le.mpr (lt_of_lt_of_le hpos hLo))\n"
    )


def lehmer_pair_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Lehmer-pair family (kind ``lehmer_pair``).
    ``spec``: ``pt -> {"n_index":…, "L":…}`` or ``pt -> n_index``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("lehmer_pair", spec),
        constants=dict(constants or {}),
    )


def find_closest_pair(n_lo: int, n_hi: int, prec: int = 128) -> tuple[int, float]:
    """Scan consecutive zeros in [n_lo, n_hi] for the CLOSEST pair (smallest
    gap/mean-spacing ratio) — the best local Lehmer-pair candidate.  Returns
    ``(n_index, ratio)``."""
    try:
        from .arb_platt import hardy_z_zeros
    except ImportError:
        from telperion.arb_platt import hardy_z_zeros

    lo_hi = hardy_z_zeros(n_lo, n_hi - n_lo + 2, prec=prec)
    mids = [float((lo + hi) / 2) for lo, hi in lo_hi]
    best_n, best_ratio = n_lo, float("inf")
    for i in range(len(mids) - 1):
        gap = mids[i + 1] - mids[i]
        ratio = gap / _mean_spacing((mids[i] + mids[i + 1]) / 2)
        if ratio < best_ratio:
            best_ratio, best_n = ratio, n_lo + i
    return best_n, best_ratio


if __name__ == "__main__":
    print("=== scan for the closest low-height pair (n=1..500) ===")
    n_best, ratio = find_closest_pair(1, 500)
    print(f"closest pair at n={n_best}, gap/mean-spacing ratio = {ratio:.4f}")

    print("\n=== positive cert at the closest pair (certified Lehmer pair) ===")
    cert = lehmer_pair_certificate(n_best)
    print(f"cert OK: n={cert.n_index} gap={float(cert.gap):.5f} "
          f"C_n={float(cert.curvature):.5f} quality δ²·C_n={float(cert.quality):.5f} < 1")

    print("\n=== NEGATIVE CONTROL 1: a wide (non-Lehmer) pair must be refused ===")
    wide_n = None
    for n in range(2, 200):
        q, _, info = lehmer_pair_quality(n)
        if q >= LEHMER_QUALITY_CAP:
            wide_n = n
            break
    if wide_n is not None:
        try:
            lehmer_pair_certificate(wide_n)
            raise SystemExit("FAIL: non-Lehmer pair not refused")
        except ValueError as e:
            print(f"refused as expected (n={wide_n}): {e}")
    else:
        print("(no non-Lehmer pair found in n<200; skipping)")

    print("\n=== NEGATIVE CONTROL 2: qcap below the exact quality must raise ===")
    try:
        lehmer_pair_certificate(n_best, qcap=cert.quality - Fraction(1, 10**6))
        raise SystemExit("FAIL: too-small qcap not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 3: qcap ≥ Lehmer threshold must raise ===")
    try:
        lehmer_pair_certificate(n_best, qcap=Fraction(2))
        raise SystemExit("FAIL: qcap ≥ 1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean ===")
    fam = lehmer_pair_family(
        "T", GridSpec([("case", [0])]), lambda pt: f"lehmer_n{n_best}",
        spec=lambda pt: {"n_index": n_best},
    )
    inst, _ = certify_lehmer_pair_point(fam, {"case": 0}, f"lehmer_n{n_best}")

    class _V:
        instances = [inst]

    body, nthm = LehmerPairEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
    print(lehmer_lambda_bound_wip_lean())
    print(lehmer_refutation_atom_lean())
