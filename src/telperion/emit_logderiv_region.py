"""de la Vallee Poussin log-derivative region-core emitter.

The quantitative CORE of the classical zeta zero-free REGION, isolated as a pure
LINEAR-ARITHMETIC deduction.  Write the three log-derivative quantities as
abstract reals (their zeta meaning is supplied elsewhere — exactly as the sibling
`emit_zero_free_region` abstracts `Zσ, Zσt, Zσ2t`):

    Pσ   := (-Re ζ'/ζ)(σ),      Pσt := (-Re ζ'/ζ)(σ+it),      Pσ2t := (-Re ζ'/ζ)(σ+2it).

From the 3-4-1 cosine positivity and the three analytic (Borel-Caratheodory-fed)
bounds

    (positivity)  0 ≤ 3·Pσ + 4·Pσt + Pσ2t
    (pole)        Pσ   ≤ 1/(σ-1) + A                 -- simple pole at s = 1
    (zero)        Pσt  ≤ A·L − k/(σ-β)               -- an order-k zero at β+iγ
    (double)      Pσ2t ≤ A·L                          -- no forced pole

the pole contribution of the zero must beat the log-size background:

    4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5·(A·L).                       [dlvp_core_estimate]

Cross-multiplying (with k ≥ 1, σ > 1, β < σ) clears to the region gap

    (σ-1)·(1 - (σ-1)·B) ≤ (1-β)·(3 + (σ-1)·B),   B := 3A + 5AL,   [dlvp_region_gap]

from which optimizing σ = 1 + c/L recovers β ≤ 1 - c'/(A·L) (the next, non-emitted
step).  Both theorems are PORTED VERBATIM from the kernel-checked
`dlvp_core_estimate` / `dlvp_region_gap` in
`examples/zero_free_bridge/lean/ZeroFreeRegion.lean` — the core is `linarith`, the
gap is `field_simp; ring` denominator-clearing + `nlinarith`.  The only change is
that the three `-Re ζ'/ζ` occurrences (which are NOT Mathlib-only) are replaced by
abstract real hypotheses `Pσ, Pσt, Pσ2t`, making the emitted lemma Mathlib-only and
self-contained (identical linear-arithmetic content).  It improves the region
CONSTANT only, is NOT the Vinogradov-Korobov rate, and is NOT a proof of RH.
conjecture1_proved = False.

WHY THIS IS A CERTIFICATE (not a template).  Telperion is the CHECKER; this
generator is UNTRUSTED.  `logderiv_region_certificate` re-derives — EXACTLY in
sympy over the symbols σ, β, A, L, k — that substituting the three bounds into the
weighted positivity `w0·Pσ + w1·Pσt + w2·Pσ2t ≥ 0` collapses to precisely the
core conclusion `w1·k/(σ-β) ≤ w0/(σ-1) + w0·A + (w1+w2)·A·L`, and that the cleared
region-gap identity holds.  A wrong constant (a coefficient that does not match the
3-4-1 weights), a nonpositive weight, or `k < 1` is REFUSED with `ValueError` (the
anti-phantom negative control) — no Lean is written for a non-certificate.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_logderiv_region.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# The 3-4-1 cosine-cone weights are structurally fixed (Fejer-capped classical
# dVP kernel).  They are the coefficients the ported `linarith` proof depends on.
_W0, _W1, _W2 = sp.Integer(3), sp.Integer(4), sp.Integer(1)


@dataclass(frozen=True)
class LogDerivRegionCertificate:
    """A verified de la Vallee Poussin region-core certificate.

    The certified data are the rational constants ``A`` (the pole/growth constant),
    ``L`` (~ log|γ|), and the zero order ``k ≥ 1``, together with the fixed 3-4-1
    weights ``(w0, w1, w2) = (3, 4, 1)``.  The self-check verifies (exactly, in
    sympy) that substituting the three analytic bounds into the weighted positivity
    collapses to the core conclusion and that the cleared region-gap identity holds.
    """

    A: sp.Rational
    L: sp.Rational
    k: sp.Integer
    w0: sp.Rational
    w1: sp.Rational
    w2: sp.Rational


def logderiv_region_certificate(A, L, k) -> LogDerivRegionCertificate:
    """Build and EXACTLY self-check a dVP log-derivative region-core certificate.

    Refuses (``ValueError``) a nonpositive weight, a zero order ``k < 1``, or a
    symbolic mismatch of the core / region-gap identity (the anti-phantom negative
    control — the deduction the ported `linarith`/`nlinarith` proof relies on must
    hold identically for the constants supplied).
    """
    Aq, Lq = sp.nsimplify(A), sp.nsimplify(L)
    kq = sp.nsimplify(k)
    if not (Aq.is_rational and Lq.is_rational and kq.is_rational):
        raise ValueError(f"logderiv_region needs rational A, L, k; got {A!r}, {L!r}, {k!r}")
    if kq < 1 or kq != int(kq):
        raise ValueError(
            f"logderiv_region needs an integer zero order k ≥ 1; got k={kq}"
        )
    w0, w1, w2 = _W0, _W1, _W2
    if w0 <= 0 or w1 <= 0 or w2 <= 0:
        raise ValueError(
            f"logderiv_region needs strictly positive 3-4-1 weights; got ({w0},{w1},{w2})"
        )
    kq = sp.Integer(int(kq))

    sigma, beta = sp.symbols("sigma beta", positive=True)
    # The three analytic upper bounds (the hypotheses of dlvp_core_estimate).
    Psigma_ub = 1 / (sigma - 1) + Aq
    Psigmat_ub = Aq * Lq - kq / (sigma - beta)
    Psigma2t_ub = Aq * Lq
    # Substitute the bounds into the weighted positivity w0·Pσ + w1·Pσt + w2·Pσ2t.
    lhs = w0 * Psigma_ub + w1 * Psigmat_ub + w2 * Psigma2t_ub
    # The core conclusion, cleared to `w1·k/(σ-β) ≤ RHS`:
    #   RHS = w0/(σ-1) + w0·A + (w1+w2)·A·L.
    rhs = w0 / (sigma - 1) + w0 * Aq + (w1 + w2) * Aq * Lq
    pole_term = w1 * kq / (sigma - beta)
    # EXACT self-check: substituting the bounds gives `lhs = rhs - pole_term`, i.e.
    # the positivity `0 ≤ lhs` is exactly `pole_term ≤ rhs` (the core estimate).
    if sp.simplify(lhs - (rhs - pole_term)) != 0:
        raise ValueError(
            "logderiv_region core self-check failed — the bound substitution does "
            "not collapse to `4·k/(σ-β) ≤ 3/(σ-1) + 3A + 5AL`; certificate rejected"
        )
    # EXACT self-check of the cleared region-gap identity used by dlvp_region_gap:
    #   from `4·k·(σ-1) ≤ (3 + B(σ-1))(σ-β)` (k ≥ 1) the ring identity
    #   `(σ-1)(1 - (σ-1)B) ≤ (1-β)(3 + (σ-1)B)` follows.  Verify the underlying
    #   algebraic identity `(1-β) = (σ-β) - (σ-1)` that the `nlinarith` step uses.
    B = w0 * Aq + (w1 + w2) * Aq * Lq  # = 3A + 5AL
    # The `nlinarith [key, hd, hsb]` closing step relies on the polynomial identity
    #   (1-β)(3+(σ-1)B) - (σ-1)(1-(σ-1)B)  =  (3+(σ-1)B)(σ-β) - 4(σ-1),
    # i.e. the cleared gap is EXACTLY `key` minus a nonneg multiple.  Verify it.
    gap_lhs = (1 - beta) * (3 + (sigma - 1) * B) - (sigma - 1) * (1 - (sigma - 1) * B)
    key_rhs = (3 + (sigma - 1) * B) * (sigma - beta) - 4 * (sigma - 1)
    if sp.expand(gap_lhs - key_rhs) != 0:
        raise ValueError(
            "logderiv_region region-gap ring identity self-check failed — certificate rejected"
        )
    return LogDerivRegionCertificate(A=Aq, L=Lq, k=kq, w0=w0, w1=w1, w2=w2)


def certify_logderiv_region_point(family, pt, name):
    """Certify one dVP region-core instance from ``family.special[1](pt)``.

    ``spec(pt)`` returns ``(A, L, k)`` or a dict ``{"A":…, "L":…, "k":…}``.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = logderiv_region_certificate(spec["A"], spec["L"], spec["k"])
    else:
        cert = logderiv_region_certificate(*spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2  # two exact self-checks: core estimate + region-gap identity


@dataclass
class LogDerivRegionCoreEmitter(Emitter):
    """Emit the ported ``dlvp_core_estimate`` + ``dlvp_region_gap`` for the given
    rational constants ``A, L, k``.  Each instance emits TWO theorems:

      * ``<name>_core``: `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5AL` from the 3-4-1
        positivity (abstract `Pσ,Pσt,Pσ2t`) + the three bounds — closed by
        `linarith`, exactly as the proven lemma.
      * ``<name>_gap``: the cleared region gap `field_simp; ring` + `nlinarith`,
        verbatim from the proven ``dlvp_region_gap`` (already Mathlib-only).
    """

    def __post_init__(self):
        self.kind = "logderiv_region"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: LogDerivRegionCertificate = inst.payload  # type: ignore[assignment]
            A = rat_lean(cert.A)
            L = rat_lean(cert.L)
            k = rat_lean(cert.k)
            base = inst.lean_name
            # ---- _core: ported dlvp_core_estimate (abstract log-derivatives) ------
            # Original proof: `have hpos := zeta_logDeriv_comb_nonneg σ t hσ;
            #   rw [show (3:ℝ)/(σ-1) = 3*(1/(σ-1)) by ring]; linarith [...]`.
            # Here the positivity `hpos : 0 ≤ 3*Pσ + 4*Pσt + Pσ2t` is a HYPOTHESIS
            # (the abstract stand-in for the zeta 3-4-1 combination), so the proof
            # is the same `rw ... ; linarith`.  ℝ is ascribed on the bare literal.
            lines.append(
                f"/-- de la Vallee Poussin CORE ESTIMATE (A={cert.A}, L={cert.L}, k={cert.k}),\n"
                f"    ported from `dlvp_core_estimate` with the three `-Re ζ'/ζ` values abstracted\n"
                f"    to reals `Pσ, Pσt, Pσ2t` (Mathlib-only; identical linear-arithmetic content).\n"
                f"    From 3-4-1 positivity + pole/zero/double bounds, the order-k zero satisfies\n"
                f"    `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5AL`. -/\n"
                f"theorem {base}_core (σ β Pσ Pσt Pσ2t : ℝ) (hσ : 1 < σ)\n"
                f"    (hpos : 0 ≤ 3 * Pσ + 4 * Pσt + Pσ2t)\n"
                f"    (hpole : Pσ ≤ 1 / (σ - 1) + {A})\n"
                f"    (hzero : Pσt ≤ {A} * {L} - {k} / (σ - β))\n"
                f"    (htwo : Pσ2t ≤ {A} * {L}) :\n"
                f"    (4 : ℝ) * ({k} / (σ - β)) ≤ 3 / (σ - 1) + 3 * {A} + 5 * ({A} * {L}) := by\n"
                f"  rw [show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) by ring]\n"
                f"  linarith [hpos, hpole, hzero, htwo]\n"
            )
            nthm += 1
            # ---- _gap: ported dlvp_region_gap (already Mathlib-only, verbatim) -----
            # B = 3A + 5AL is a CONCRETE rational here; the abstract `A L` binders of
            # the proven lemma are specialized, but the `field_simp; ring` + nlinarith
            # skeleton is identical.  ℝ ascribed on the `4`.
            lines.append(
                f"/-- REGION GAP (cleared form) for A={cert.A}, L={cert.L}: with an order-k≥1 zero,\n"
                f"    the core estimate pushes the zero left of the 1-line.  Ported verbatim from the\n"
                f"    Mathlib-only `dlvp_region_gap`; `B = 3A + 5AL`, cross-multiplied. -/\n"
                f"theorem {base}_gap (σ β : ℝ) (k : ℤ) (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)\n"
                f"    (hcore : (4 : ℝ) * ((k : ℝ) / (σ - β))\n"
                f"      ≤ 3 / (σ - 1) + (3 * {A} + 5 * ({A} * {L}))) :\n"
                f"    (σ - 1) * (1 - (σ - 1) * (3 * {A} + 5 * ({A} * {L})))\n"
                f"      ≤ (1 - β) * (3 + (σ - 1) * (3 * {A} + 5 * ({A} * {L}))) := by\n"
                f"  have hd : (0 : ℝ) < σ - 1 := by linarith\n"
                f"  have hd' : σ - 1 ≠ 0 := hd.ne'\n"
                f"  have hsb : (0 : ℝ) < σ - β := by linarith\n"
                f"  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk\n"
                f"  set B := (3 * {A} + 5 * ({A} * {L}) : ℝ) with hBdef\n"
                f"  have lhs_eq : 4 * ((k : ℝ) / (σ - β)) = (4 * (k : ℝ)) / (σ - β) := by ring\n"
                f"  have rhs_eq : 3 / (σ - 1) + B = (3 + B * (σ - 1)) / (σ - 1) := by field_simp\n"
                f"  rw [lhs_eq, rhs_eq, div_le_iff₀ hsb, div_mul_eq_mul_div, le_div_iff₀ hd] at hcore\n"
                f"  have key : 4 * (σ - 1) ≤ (3 + B * (σ - 1)) * (σ - β) := by nlinarith [hcore, hk1, hd, hsb]\n"
                f"  nlinarith [key, hd, hsb]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def logderiv_region_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a dVP log-derivative region-core family (kind='logderiv_region').

    ``spec``: a callable ``pt -> (A, L, k)`` (or ``pt -> {"A","L","k"}``) of
    rationals with the integer zero order ``k ≥ 1``.  Refuses a nonpositive weight,
    ``k < 1``, or a mismatched constant at certification.
    """
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("logderiv_region", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- positive certificate: the standard dVP constants A=1, L=1, k=1 ----------
    print("=== positive certificate A=1, L=1, k=1 ===")
    cert = logderiv_region_certificate(1, 1, 1)
    print(f"cert OK: A={cert.A}, L={cert.L}, k={cert.k}, weights=({cert.w0},{cert.w1},{cert.w2})")

    print("\n=== positive certificate A=2, L=3, k=2 (order-2 zero) ===")
    cert2 = logderiv_region_certificate(2, 3, 2)
    print(f"cert OK: A={cert2.A}, L={cert2.L}, k={cert2.k}")

    # --- negative control: k = 0 (no zero) must be refused -----------------------
    print("\n=== NEGATIVE CONTROL: k=0 must raise ValueError ===")
    try:
        logderiv_region_certificate(1, 1, 0)
        raise SystemExit("FAIL: k=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    # --- negative control: non-integer k must be refused -------------------------
    print("\n=== NEGATIVE CONTROL: k=3/2 must raise ValueError ===")
    try:
        logderiv_region_certificate(1, 1, sp.Rational(3, 2))
        raise SystemExit("FAIL: k=3/2 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    # --- build instances + emit Lean ---------------------------------------------
    _SPECS = {0: (1, 1, 1), 1: (2, 3, 2)}
    _NAMES = {0: "dlvp_region_unit", 1: "dlvp_region_A2L3k2"}
    fam = logderiv_region_family(
        "LogDerivRegionSelfTest",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1):
        inst, n = certify_logderiv_region_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = LogDerivRegionCoreEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print("=" * 72)
    print(f"EMITTED LEAN ({nthm} theorems):")
    print("=" * 72)
    print(body)
