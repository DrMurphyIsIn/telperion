"""Box-localization emitter — RH-in-a-box capstone counting step (Stage 3).

The crowning localization: if the TOTAL multiplicity-weighted zero count of a function in a box `B`
equals `n_total` (argument principle) and we already exhibit `n_line` DISTINCT zeros of `B` on the
critical line `Re = 1/2`, then WHEN `n_line == n_total` those on-line zeros EXHAUST the divisor —
every zero in `B` is one of them, hence on `Re = 1/2` and simple.

Emitted theorem `box_localization_<name>` (pure Finset counting, real-geometry — the integral is
already discharged upstream): a sub-Finset `T ⊆ s` of `n` distinct on-line points, each divisor
`≥ 1`, with `∑_{s} d = n`, forces `s = T` and every `d ρ = 1`; hence every `ρ ∈ s` has `Re = 1/2`.

Certificate: `box` (a rational rectangle), `n_line`, `n_total`.  The localization hypothesis is the
EQUALITY `n_line == n_total` (with `n_line ≥ 1`).  NEGATIVE CONTROL: `n_line > n_total` is impossible
(more on-line zeros than the total count) and is REFUSED; `n_line != n_total` is likewise REFUSED —
without equality the on-line zeros cannot be shown to exhaust the divisor, so no localization claim
may be emitted.  conjecture1_proved = False (this VERIFIES RH inside the box; it is NOT a proof of RH).
"""
from __future__ import annotations

import math
from dataclasses import dataclass
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


@dataclass(frozen=True)
class BoxLocalizationCertificate:
    """A verified box-localization certificate.

    ``re_lo, re_hi, im_lo, im_hi`` describe the rational box `B`; ``n`` is the (equal) on-line and
    total zero count.  The equality `n_line == n_total == n` is the localization hypothesis.
    """

    re_lo: sp.Rational
    re_hi: sp.Rational
    im_lo: sp.Rational
    im_hi: sp.Rational
    n: int


@dataclass(frozen=True)
class EmptyBandCertificate:
    """A verified EMPTY-BAND certificate: a box `[re_lo,re_hi] x [im_lo,im_hi]` whose boundary
    winding `N == 0`, hence (argument principle, multiplicities >= 1) contains NO zeros of zeta.

    ``n`` is the total winding count and is ALWAYS 0 (the builder refuses any other value).
    """

    re_lo: sp.Rational
    re_hi: sp.Rational
    im_lo: sp.Rational
    im_hi: sp.Rational
    n: int = 0


def _validate_localization_box(re_lo, re_hi, im_lo, im_hi, *, require_straddle: bool = True):
    """Shared box validation for the RH-in-box emitters: rational, non-degenerate, excludes the
    pole `s = 1`, and (when ``require_straddle``) straddles the critical line `1/2`.

    The straddle requirement applies to the LOCALIZATION path (an "all box zeros on Re = 1/2"
    claim over a box missing the line would be vacuous-by-construction).  A ZERO-FREE box
    (empty-band path) makes no critical-line claim, so slivers like `[0, a]` are valid there —
    pass ``require_straddle=False``.  Returns the four sympy Rationals.  Raises ValueError (with
    the words "straddle" / "pole" in the message) on the negative controls."""
    rl, rh, il, ih = (sp.nsimplify(x) for x in (re_lo, re_hi, im_lo, im_hi))
    if not all(v.is_rational for v in (rl, rh, il, ih)):
        raise ValueError("box corners must be rational")
    if not (rl < rh and il < ih):
        raise ValueError(f"needs a non-degenerate box; got [{rl},{rh}]x[{il},{ih}]")
    half = sp.Rational(1, 2)
    if require_straddle and not (rl < half < rh):
        raise ValueError(
            f"invalid box — the sigma-range [{rl},{rh}] must straddle the critical line 1/2 "
            f"(re_lo < 1/2 < re_hi); refused"
        )
    one, zero = sp.Integer(1), sp.Integer(0)
    if (rl <= one <= rh) and (il <= zero <= ih):
        raise ValueError(
            f"invalid box — the pole s = 1 lies in [{rl},{rh}]x[{il},{ih}]; the box must exclude "
            f"s = 1 (need re_hi < 1 or im_lo > 0 or im_hi < 0); refused"
        )
    return rl, rh, il, ih


def empty_band_certificate(
    re_lo, re_hi, im_lo, im_hi, *, n_total: int
) -> EmptyBandCertificate:
    """Build and EXACTLY self-check an empty-band certificate.

    The localization hypothesis is `n_total == 0` (the boundary winding is zero, so the box holds
    no zeros).  NEGATIVE CONTROL: any `n_total != 0` is REFUSED — a nonzero winding means there IS
    a zero to exhibit, which is the count-matching path (`emit_per_box_instantiation`), not the
    empty band.  The box need NOT straddle `1/2` (a zero-free claim makes no critical-line
    statement — slivers like `[0, a]` are valid) but must EXCLUDE the pole `s = 1`
    (`choose_ball` additionally guarantees a separating ball exists).
    conjecture1_proved = False."""
    if not isinstance(n_total, int):
        raise ValueError(f"empty_band n_total must be an int; got {n_total!r}")
    if n_total != 0:
        raise ValueError(
            f"empty_band_certificate: n_total ({n_total}) != 0 — a nonzero boundary winding means "
            f"the box contains a zero to exhibit (use the count-matching localization path); the "
            f"empty band requires winding N == 0; refused"
        )
    rl, rh, il, ih = _validate_localization_box(re_lo, re_hi, im_lo, im_hi,
                                                require_straddle=False)
    # Confirm a separating Blaschke ball exists (raises if the box reaches the pole).
    choose_ball(rl, rh, il, ih)
    return EmptyBandCertificate(re_lo=rl, re_hi=rh, im_lo=il, im_hi=ih, n=0)


def box_localization_certificate(
    n_line: int, n_total: int, re_lo="2/5", re_hi="3/5", im_lo="10", im_hi="35"
) -> BoxLocalizationCertificate:
    """Build and EXACTLY self-check a box-localization certificate.

    Refuses `n_line > n_total` (impossible: more on-line zeros than total count), `n_line != n_total`
    (no exhaustion without equality — cannot emit a localization claim), and `n_line < 1` (vacuous).
    Also refuses an INVALID box: the sigma-range must STRADDLE the critical line `1/2`
    (`re_lo < 1/2 < re_hi`) and the box must EXCLUDE the pole `s = 1` (either `re_hi < 1`, i.e. the
    whole box is left of `Re = 1`, or `im_lo > 0`, i.e. the box is above the real axis so `1` — with
    `im = 0` — is not in it).  These are the negative controls.
    """
    if not (isinstance(n_line, int) and isinstance(n_total, int)):
        raise ValueError(f"box_localization counts must be ints; got n_line={n_line!r}, n_total={n_total!r}")
    if n_line > n_total:
        raise ValueError(
            f"box_localization: n_line ({n_line}) exceeds n_total ({n_total}) — impossible "
            f"(cannot have more on-line zeros than the total count); refused"
        )
    if n_line != n_total:
        raise ValueError(
            f"box_localization: n_line ({n_line}) != n_total ({n_total}) — without equality the "
            f"on-line zeros do not exhaust the divisor; no localization claim may be emitted; refused"
        )
    if n_line < 1:
        raise ValueError(f"box_localization needs n_line >= 1 (non-vacuous); got n_line={n_line}")
    rl, rh, il, ih = (sp.nsimplify(x) for x in (re_lo, re_hi, im_lo, im_hi))
    if not all(v.is_rational for v in (rl, rh, il, ih)):
        raise ValueError("box_localization box corners must be rational")
    if not (rl < rh and il < ih):
        raise ValueError(f"box_localization needs a non-degenerate box; got [{rl},{rh}]x[{il},{ih}]")
    half = sp.Rational(1, 2)
    if not (rl < half < rh):
        raise ValueError(
            f"box_localization: invalid box — the sigma-range [{rl},{rh}] must straddle the critical "
            f"line 1/2 (re_lo < 1/2 < re_hi); a box whose real-range excludes 1/2 cannot localize RH; "
            f"refused"
        )
    # The box must exclude the pole s = 1 (= 1 + 0*i).  Excluded iff 1 is not in [re_lo,re_hi] OR
    # 0 is not in [im_lo,im_hi].
    one = sp.Integer(1)
    zero = sp.Integer(0)
    one_in_re = rl <= one <= rh
    zero_in_im = il <= zero <= ih
    if one_in_re and zero_in_im:
        raise ValueError(
            f"box_localization: invalid box — the pole s = 1 lies in [{rl},{rh}]x[{il},{ih}]; the box "
            f"must exclude s = 1 (need re_hi < 1 or im_lo > 0 or im_hi < 0); refused"
        )
    return BoxLocalizationCertificate(re_lo=rl, re_hi=rh, im_lo=il, im_hi=ih, n=n_line)


def certify_box_localization_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys n_line, n_total, and
    optionally the box corners)."""
    spec = family.special[1](pt)
    cert = box_localization_certificate(
        int(spec["n_line"]), int(spec["n_total"]),
        spec.get("re_lo", "2/5"), spec.get("re_hi", "3/5"),
        spec.get("im_lo", "10"), spec.get("im_hi", "35"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BoxLocalizationEmitter(Emitter):
    """Emit the box-localization counting capstone `box_localization_<name>` for a fixed count `n`."""

    def __post_init__(self):
        self.kind = "box_localization"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Finset\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: BoxLocalizationCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            rl, rh, il, ih = (rat_lean(v) for v in (cert.re_lo, cert.re_hi, cert.im_lo, cert.im_hi))
            n = cert.n
            lines.append(
                f"/-- Box-localization capstone (counting step) on `B = [{rl},{rh}] x [{il},{ih}]`,\n"
                f"    n_line = n_total = {n}.  Given a support `s` with total divisor `= {n}`, each\n"
                f"    multiplicity `>= 1`, and `{n}` DISTINCT on-line (`Re = 1/2`) elements of `s`, the\n"
                f"    on-line zeros EXHAUST the divisor: every `rho in s` has `Re rho = 1/2`.\n"
                f"    The integral is already discharged upstream; this is pure Finset counting.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} (s T : Finset ℂ) (d : ℂ → ℤ)\n"
                f"    (hTsub : T ⊆ s) (hTcard : T.card = {n})\n"
                f"    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)\n"
                f"    (hsum : (∑ ρ ∈ s, d ρ) = ({n} : ℤ))\n"
                f"    (hline : ∀ ρ ∈ T, ρ.re = 1 / 2) :\n"
                f"    ∀ ρ ∈ s, ρ.re = 1 / 2 := by\n"
                f"  -- Split the sum over `s` into `T` and `s \\ T`.\n"
                f"  have hsplit : (∑ ρ ∈ s, d ρ) = (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \\ T, d ρ) := by\n"
                f"    rw [← Finset.sum_sdiff hTsub, add_comm]\n"
                f"  have hTlb : (({n} : ℤ)) ≤ ∑ ρ ∈ T, d ρ := by\n"
                f"    calc (({n} : ℤ)) = ∑ _ρ ∈ T, (1 : ℤ) := by\n"
                f"            rw [Finset.sum_const, hTcard, nsmul_eq_mul, mul_one]; norm_num\n"
                f"      _ ≤ ∑ ρ ∈ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (hTsub hρ))\n"
                f"  have hSlb : ((s \\ T).card : ℤ) ≤ ∑ ρ ∈ s \\ T, d ρ := by\n"
                f"    calc ((s \\ T).card : ℤ) = ∑ _ρ ∈ s \\ T, (1 : ℤ) := by\n"
                f"            rw [Finset.sum_const, nsmul_eq_mul, mul_one]\n"
                f"      _ ≤ ∑ ρ ∈ s \\ T, d ρ :=\n"
                f"          Finset.sum_le_sum (fun ρ hρ => hd1 ρ (Finset.mem_sdiff.mp hρ).1)\n"
                f"  have hcard0 : (s \\ T).card = 0 := by\n"
                f"    have hchain : (({n} : ℤ)) + ((s \\ T).card : ℤ) ≤ (({n} : ℤ)) := by\n"
                f"      calc (({n} : ℤ)) + ((s \\ T).card : ℤ)\n"
                f"          ≤ (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \\ T, d ρ) := add_le_add hTlb hSlb\n"
                f"        _ = (∑ ρ ∈ s, d ρ) := hsplit.symm\n"
                f"        _ = (({n} : ℤ)) := hsum\n"
                f"    have hle : ((s \\ T).card : ℤ) ≤ 0 := by linarith\n"
                f"    exact_mod_cast le_antisymm hle (by positivity)\n"
                f"  have hsubT : s ⊆ T := by\n"
                f"    have hempty : s \\ T = ∅ := Finset.card_eq_zero.mp hcard0\n"
                f"    intro x hx\n"
                f"    by_contra hxT\n"
                f"    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)\n"
                f"      (by rw [hempty]; exact Finset.notMem_empty x)\n"
                f"  have hsT : s = T := le_antisymm hsubT hTsub\n"
                f"  intro ρ hρ\n"
                f"  rw [hsT] at hρ\n"
                f"  exact hline ρ hρ\n"
            )
            nthm += 1
        return "".join(lines), nthm


def _rat_lean(x: sp.Rational) -> str:
    """Render a rational as a Lean numeric literal (integer or `a / b`)."""
    return rat_lean(sp.Rational(x))


def choose_ball(re_lo, re_hi, im_lo, im_hi):
    """Choose a Blaschke ball (center c = cx + cy*i, radius^2 = Rsq) for the box.

    Center = box center.  Rsq is the midpoint between the corner-distance-squared `dc2`
    (max distance from center to any corner) and the pole-distance-squared `d12 = |1 - c|^2`,
    so the box is STRICTLY inside `ball c (sqrt Rsq)` and the pole `s = 1` is STRICTLY outside.
    All values are exact `sympy.Rational`.  Raises ValueError if the box's corners reach past
    the pole (no separating ball exists), which the certificate's invalid-box refusal precludes.
    """
    rl, rh, il, ih = (sp.Rational(v) for v in (re_lo, re_hi, im_lo, im_hi))
    cx = (rl + rh) / 2
    cy = (il + ih) / 2
    dc2 = ((rh - rl) / 2) ** 2 + ((ih - il) / 2) ** 2       # center->corner squared
    d12 = (1 - cx) ** 2 + cy ** 2                            # center->pole(1) squared
    if not (dc2 < d12):
        raise ValueError(
            f"choose_ball: no separating ball — corner-distance^2 ({dc2}) >= pole-distance^2 "
            f"({d12}); the box reaches the pole s = 1"
        )
    rsq = (dc2 + d12) / 2
    return cx, cy, rsq


def _arb_bundle_conjuncts(s0: str, s1: str, t0: str, t1: str) -> list[str]:
    """The 16 routine Arb boundary conjuncts of `zeta_count_eq_winding_generic`'s `hArb`,
    rendered at the box corners `[s0,s1] x [t0,t1]` (Lean literals).

    Order and form match `RHInBoxAnalytic.zeta_count_eq_winding_generic` exactly: 4 edge
    non-vanishing, 1 strict-interiority, 4 residue-inverse integrability, 4 residue-sum
    integrability, 3 E integrability (the fourth E term is the 16th).  Both the full
    localization emitter and the empty-band emitter consume this so the two hArb bundles are
    single-sourced.  Uses the free names `s` (divisor support) and `d` (divisor)."""
    return [
        f"(∀ x ∈ Set.uIcc (({s0}) : ℝ) ({s1}), riemannZeta (↑x + ((({t0}) : ℝ) : ℂ) * I) ≠ 0)",
        f"(∀ x ∈ Set.uIcc (({s0}) : ℝ) ({s1}), riemannZeta (↑x + ((({t1}) : ℝ) : ℂ) * I) ≠ 0)",
        f"(∀ y ∈ Set.uIcc (({t0}) : ℝ) ({t1}), riemannZeta (((({s1}) : ℝ) : ℂ) + ↑y * I) ≠ 0)",
        f"(∀ y ∈ Set.uIcc (({t0}) : ℝ) ({t1}), riemannZeta (((({s0}) : ℝ) : ℂ) + ↑y * I) ≠ 0)",
        f"(∀ ρ ∈ s, (({s0}) : ℝ) < ρ.re ∧ ρ.re < ({s1}) ∧ (({t0}) : ℝ) < ρ.im ∧ ρ.im < ({t1}))",
        (f"(∀ ρ ∈ s, IntervalIntegrable\n"
         f"        (fun x : ℝ => ((↑x + ((({t0}) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (({s0})) (({s1})))"),
        (f"(∀ ρ ∈ s, IntervalIntegrable\n"
         f"        (fun x : ℝ => ((↑x + ((({t1}) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (({s0})) (({s1})))"),
        (f"(∀ ρ ∈ s, IntervalIntegrable\n"
         f"        (fun y : ℝ => ((((({s1}) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (({t0})) (({t1})))"),
        (f"(∀ ρ ∈ s, IntervalIntegrable\n"
         f"        (fun y : ℝ => ((((({s0}) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (({t0})) (({t1})))"),
        (f"(IntervalIntegrable\n"
         f"        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((({t0}) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (({s0})) (({s1})))"),
        (f"(IntervalIntegrable\n"
         f"        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((({t1}) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (({s0})) (({s1})))"),
        (f"(IntervalIntegrable\n"
         f"        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((({s1}) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (({t0})) (({t1})))"),
        (f"(IntervalIntegrable\n"
         f"        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((({s0}) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (({t0})) (({t1})))"),
        f"(IntervalIntegrable (fun x : ℝ => E (↑x + ((({t0}) : ℝ) : ℂ) * I)) volume (({s0})) (({s1})))",
        f"(IntervalIntegrable (fun x : ℝ => E (↑x + ((({t1}) : ℝ) : ℂ) * I)) volume (({s0})) (({s1})))",
        f"(IntervalIntegrable (fun y : ℝ => E (((({s1}) : ℝ) : ℂ) + ↑y * I)) volume (({t0})) (({t1})))",
        f"(IntervalIntegrable (fun y : ℝ => E (((({s0}) : ℝ) : ℂ) + ↑y * I)) volume (({t0})) (({t1})))",
    ]


# ---------------------------------------------------------------------------
# Per-box instantiation emitter: INSTANTIATE `RHInBox.rh_in_box_of_certificate`.
# ---------------------------------------------------------------------------

def _build_full_instantiation(
    *, name, namespace, header, n, s0, s1, t0, t1, cx_s, cy_s, rsq_s,
    xs, hline_type, conj, winding,
):
    """Assemble the full per-box instantiation theorem (arbitrary N).  See
    emit_per_box_instantiation for the contract."""
    box_set = f"Set.Icc (({s0}) : ℝ) ({s1}) ×ℂ Set.Icc (({t0}) : ℝ) ({t1})"
    # Ball center / radius are TOP-LEVEL defs so the signature (hArb, hs1) and body reference
    # the SAME term (avoids auto-bound `c✝`/`R✝` divergence between signature and body).
    ball = "Metric.ball cPB RPB"
    # ---- hArb hypothesis type (17 conjuncts: the 16 bundle + the winding) -----------
    conj_join = " ∧\n      ".join(conj)
    harb_hyp = (
        f"    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),\n"
        f"      DifferentiableOn ℂ E ({box_set}) →\n"
        f"      (∀ z ∈ {ball}, riemannZeta z ≠ 0 →\n"
        f"        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →\n"
        f"      {conj_join} ∧\n"
        f"      {winding})"
    )
    # conclusion type
    concl = (
        f"    (∀ ρ, ((({s0}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({s1})) → ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) →\n"
        f"      riemannZeta ρ = 0 → ρ.re = 1 / 2)"
    )

    lines: list[str] = []
    A = lines.append

    A(header)
    # Top-level ball center + radius definitions (shared by signature and body).
    A(f"/-- Chosen Blaschke ball center for the box `[{s0},{s1}] x [{t0},{t1}]`. -/\n")
    A(f"noncomputable def cPB : ℂ := ⟨({cx_s}), ({cy_s})⟩\n\n")
    A(f"/-- Chosen Blaschke ball radius (squared radius `{rsq_s}`). -/\n")
    A(f"noncomputable def RPB : ℝ := Real.sqrt ({rsq_s})\n\n")
    A(f"theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)\n\n")
    A(f"/-- **RH-in-a-box on `[{s0},{s1}] x [{t0},{t1}]` with `N = {n}`.**  Instantiates the generic\n"
      f"    `RHInBox.rh_in_box_of_certificate` at this box's corners, chosen Blaschke ball\n"
      f"    `c = ({cx_s}) + ({cy_s})*I`, `R = Real.sqrt ({rsq_s})`, and count `N = {n}`.  Takes the\n"
      f"    documented Arb inputs `hLine` (the {n} on-line zeros) and `hArb` (boundary bundle +\n"
      f"    winding `= 2*pi*I*{n}`).  conjecture1_proved = False. -/\n")
    A(f"theorem {name}\n")
    A(hline_type + "\n")
    A(harb_hyp + " :\n")
    A(concl + " := by\n")

    # ---- geometry: hRpos, hsig, hT, hbox_ball, hs1 (all at the top-level cPB/RPB) -----
    A(f"  have hRpos : (0 : ℝ) < RPB := RPB_pos\n")
    A(f"  have hsig : (({s0}) : ℝ) ≤ ({s1}) := by norm_num\n")
    A(f"  have hTle : (({t0}) : ℝ) ≤ ({t1}) := by norm_num\n")
    # hbox_ball: any ρ with re,im in the box is in ball cPB RPB.
    A(f"  have hbox_ball : ∀ ρ : ℂ, ((({s0}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({s1})) →\n")
    A(f"      ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) → ρ ∈ Metric.ball cPB RPB := by\n")
    A(f"    intro ρ hre him\n")
    A(f"    rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"    unfold cPB RPB\n")
    A(f"    apply Real.sqrt_lt_sqrt (by positivity)\n")
    A(f"    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2\n")
    A(f"    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ({cx_s})), sq_nonneg (ρ.im - ({cy_s}))]\n")
    # hs1: 1 not in ball cPB RPB.  dist 1 cPB = sqrt d12 >= RPB = sqrt rsq  (rsq <= d12).
    A(f"  have hs1 : (1 : ℂ) ∉ Metric.ball cPB RPB := by\n")
    A(f"    rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"    unfold cPB RPB\n")
    A(f"    intro hlt\n")
    A(f"    simp only [Complex.one_re, Complex.one_im] at hlt\n")
    A(f"    have hle : Real.sqrt ({rsq_s}) ≤\n")
    A(f"        Real.sqrt (((1 : ℝ) - ({cx_s})) ^ 2 + ((0 : ℝ) - ({cy_s})) ^ 2) :=\n")
    A(f"      Real.sqrt_le_sqrt (by norm_num)\n")
    A(f"    linarith [hlt, hle]\n")

    # ---- bridge on-line completed zeros, build T ------------------------------------
    # order chain binder names: hlo (T0<=x1), h12, h23, ..., hhi (xn<=T1)
    ord_names = ["hlo"] + [f"hc{i}{i+1}" for i in range(1, n)] + ["hhi"]
    zero_names = [f"hΛ{i}" for i in range(1, n + 1)]
    A(f"  obtain ⟨{', '.join(xs)}, ⟨{', '.join(ord_names)}⟩, {', '.join(zero_names)}⟩ := hLine\n")
    A(f"  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by\n")
    A(f"    intro t\n")
    A(f"    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,\n")
    A(f"      Complex.ofReal_im]; norm_num\n")
    A(f"  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by\n")
    A(f"    intro t\n")
    A(f"    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,\n")
    A(f"      Complex.ofReal_im]; norm_num\n")
    A(f"  have hzeta : ∀ (t : ℝ), completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →\n")
    A(f"      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=\n")
    A(f"    fun t h => BoxLocalization.line_zeta_zero_of_completed h\n")

    # ---- O(N) on-line Finset via sorted list (RHInBox.line_toFinset_card) ------------
    # The emitted proof supplies only the O(N) consecutive chain x1 < ... < xn; the
    # hand-written lemmas in RHInBox.lean (Part A0) convert chain -> Nodup -> card.
    # This replaces the old O(N^2) pairwise-distinctness + insert-peeling block.
    A(f"  set xsL : List ℝ := [{', '.join(xs)}] with hxsdef\n")
    A(f"  have hchain : xsL.IsChain (· < ·) := by\n")
    A(f"    rw [hxsdef]\n")
    if n == 1:
        A(f"    exact List.IsChain.singleton _\n")
    else:
        chain_haves = ", ".join(f"hc{i}{i+1}" for i in range(1, n))
        A(f"    simp only [List.isChain_cons_cons]\n")
        A(f"    exact ⟨{chain_haves}, List.IsChain.singleton _⟩\n")
    A(f"  set T : Finset ℂ :=\n")
    A(f"    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef\n")
    A(f"  have hTcard : T.card = {n} := by\n")
    A(f"    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hxsdef]\n")
    A(f"    rfl\n")
    # Forward-chained per-element bounds (pure term mode -- no linarith, no rcases, no
    # membership disjunction; the N=50 band showed simp on a 50-disjunct blows the budget).
    # hb{i} : t0 <= x{i} chains left-to-right; hu{i} : x{i} <= t1 chains right-to-left.
    A(f"  have hb1 : (({t0}) : ℝ) ≤ x1 := hlo\n")
    for i in range(2, n + 1):
        A(f"  have hb{i} : (({t0}) : ℝ) ≤ x{i} := le_trans hb{i-1} (le_of_lt hc{i-1}{i})\n")
    A(f"  have hu{n} : x{n} ≤ (({t1}) : ℝ) := hhi\n")
    for i in range(n - 1, 0, -1):
        A(f"  have hu{i} : x{i} ≤ (({t1}) : ℝ) := le_trans (le_of_lt hc{i}{i+1}) hu{i+1}\n")
    A(f"  have hre_lo : (({s0}) : ℝ) ≤ 1 / 2 := by norm_num\n")
    A(f"  have hre_hi : (1 / 2 : ℝ) ≤ ({s1}) := by norm_num\n")
    A(f"  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)\n")
    # hTzero / hTbox: split `forall t in list` into a flat conjunction (List.forall_mem_cons
    # is linear-cheap, unlike the mem-disjunction normalization) and close each component
    # with an O(1) term: no substitution, so x{i}/hLambda{i} stay in scope.
    # forall_mem_cons peels every cons INCLUDING the last ([xn] = xn :: []), leaving a
    # trailing `∀ x ∈ [], P x` conjunct -- terminated by List.forall_mem_nil.  Uniform in n.
    A(f"  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    refine RHInBox.line_toFinset_forall xsL ?_\n")
    A(f"    rw [hxsdef]\n")
    A(f"    simp only [List.forall_mem_cons]\n")
    zero_terms = ", ".join(f"hzeta x{i} hΛ{i}" for i in range(1, n + 1))
    A(f"    exact ⟨{zero_terms}, List.forall_mem_nil _⟩\n")
    A(f"  have hTbox : ∀ z ∈ T, ((({s0}) : ℝ) ≤ z.re ∧ z.re ≤ ({s1})) ∧ ((({t0}) : ℝ) ≤ z.im ∧ z.im ≤ ({t1})) := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    refine RHInBox.line_toFinset_forall xsL ?_\n")
    A(f"    rw [hxsdef]\n")
    A(f"    simp only [List.forall_mem_cons]\n")
    box_terms = ", ".join(
        f"⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,"
        f" by rw [him_line]; exact hb{i}, by rw [him_line]; exact hu{i}⟩"
        for i in range(1, n + 1)
    )
    A(f"    exact ⟨{box_terms}, List.forall_mem_nil _⟩\n")

    # ---- extract hwind + reassemble harb from hArb ----------------------------------
    A(f"  set s0f : Finset ℂ := RHInBoxAnalytic.zeroFinset cPB RPB hs1 with hs0def\n")
    A(f"  set d0 : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ) with hd0def\n")
    # We need an E0 witness + kernel split so that hArb can be applied at (E0, s0f, d0).
    A(f"  obtain ⟨E0, hE0holo, hd1', hzero_in', hker0⟩ :=\n")
    A(f"    RHInBoxAnalytic.zeta_blaschke_split_ball (({s0}) : ℝ) ({s1}) ({t0}) ({t1}) cPB RPB hRpos hbox_ball hs1\n")
    A(f"  have hE0box : DifferentiableOn ℂ E0 ({box_set}) := hE0holo\n")
    A(f"  have hker0' : ∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →\n")
    A(f"      logDeriv riemannZeta z = (∑ ρ ∈ s0f, (d0 ρ : ℂ) / (z - ρ)) + E0 z := by\n")
    A(f"    intro z hz hnz\n")
    A(f"    have := hker0 z hz hnz\n")
    A(f"    rw [hs0def, hd0def]; exact this\n")
    # destructure the full bundle from hArb: 17 conjuncts + winding = 18 components.
    ncbundle = len(conj)
    dnames = [f"hA{i}" for i in range(ncbundle)] + ["hwindA"]
    dpat = ", ".join(dnames)
    A(f"  obtain ⟨{dpat}⟩ := hArb E0 s0f d0 hE0box hker0'\n")
    # winding
    A(f"  have hwind : (∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t0}) : ℝ) : ℂ) * I))\n")
    A(f"        - (∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t1}) : ℝ) : ℂ) * I))\n")
    A(f"        + I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s1}) : ℝ) : ℂ) + ↑y * I))\n")
    A(f"        - I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s0}) : ℝ) : ℂ) + ↑y * I))\n")
    A(f"      = 2 * π * I * (({n} : ℤ) : ℂ) := by\n")
    A(f"    rw [show ((({n} : ℤ) : ℂ)) = ({n} : ℂ) by norm_num]; exact hwindA\n")
    # reassemble harb: for arbitrary E s d, apply hArb and drop the last (winding) conjunct.
    A(f"  have harb : ∀ (E : ℂ → ℂ),\n")
    A(f"      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1\n")
    A(f"      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball cPB RPB) : ℂ → ℤ)\n")
    A(f"      DifferentiableOn ℂ E ({box_set}) →\n")
    A(f"      (∀ z ∈ Metric.ball cPB RPB, riemannZeta z ≠ 0 →\n")
    A(f"        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →\n")
    A(f"      {conj_join} := by\n")
    A(f"    intro E s d hEholo hkerE\n")
    A(f"    have hfull := hArb E s d hEholo hkerE\n")
    # hfull is a (ncbundle + winding)-conjunct right-nested tuple; project the first ncbundle
    # (dropping the trailing winding conjunct).
    proj = ["hfull" + ".2" * k + ".1" for k in range(ncbundle)]
    A(f"    exact ⟨{', '.join(proj)}⟩\n")

    # ---- final call -----------------------------------------------------------------
    A(f"  have hcountN : ({n} : ℤ) = (T.card : ℤ) := by rw [hTcard]; norm_num\n")
    A(f"  exact RHInBox.rh_in_box_of_certificate (({s0}) : ℝ) ({s1}) ({t0}) ({t1}) cPB RPB {n}\n")
    A(f"    hRpos hsig hTle hbox_ball hs1 T hTline hTzero hTbox hwind harb hcountN\n")
    A(f"\nend {namespace}\n")
    return "".join(lines)


def _heartbeats_for(n: int) -> int:
    """Heartbeat budget for the per-box instantiation proof.

    Since the O(N) list-based construction (RHInBox Part A0: chain -> Nodup -> card via
    `line_toFinset_card`) replaced the old O(N^2) pairwise-distinctness + insert-peeling
    block, the emitted proof's N-dependent cost is the 2N `linarith` calls in hTbox and
    the N-branch rcases in hTzero -- linear with small constants (empirically N=29 builds
    in ~30s well inside a 400000 budget).  Scale linearly with generous headroom:
    default for n <= 25, then base * ceil(n / 25)."""
    base = 200000
    if n <= 25:
        return base
    return base * math.ceil(n / 25.0)


def emit_per_box_instantiation(
    cert: BoxLocalizationCertificate,
    tag: str,
    *,
    theorem_name: str | None = None,
    namespace: str = "RHInBoxPerBox",
) -> str:
    """Emit a complete standalone Lean file instantiating `RHInBox.rh_in_box_of_certificate`.

    The emitted theorem `rh_in_box_<tag>` takes the SAME two documented inputs as the regression
    `RHInBox.rh_in_box_10_35`:

    * `hLine` — an existential of `N = cert.n` strictly-`Im`-increasing on-line completed-zeta zeros
      in `[T0, T1]` (Stage 1 / Arb non-kernel input);
    * `hArb` — the honest boundary Arb bundle + the winding value `= 2*pi*I*N` at THIS box's corners.

    It discharges the geometry (`hRpos`/`hsig`/`hT`/`hbox_ball`/`hs1`) by real `norm_num`/`sqrt`
    reasoning at the CHOSEN ball `c = cx + cy*i`, `R = Real.sqrt Rsq` (via `choose_ball`), builds the
    on-line Finset `T` with a strict-chain distinctness proof for arbitrary `N`, reassembles the
    generic `harb` (dropping the winding conjunct) and extracts `hwind`, and closes with
    `rh_in_box_of_certificate`.  conjecture1_proved = False.
    """
    n = cert.n
    if n < 1:
        raise ValueError("emit_per_box_instantiation needs n >= 1")
    name = theorem_name or f"rh_in_box_{tag}"
    s0 = _rat_lean(cert.re_lo)
    s1 = _rat_lean(cert.re_hi)
    t0 = _rat_lean(cert.im_lo)
    t1 = _rat_lean(cert.im_hi)
    cx, cy, rsq = choose_ball(cert.re_lo, cert.re_hi, cert.im_lo, cert.im_hi)
    cx_s = _rat_lean(cx)
    cy_s = _rat_lean(cy)
    rsq_s = _rat_lean(rsq)

    # ---- header + geometry-local `c`, `R` abbreviations -----------------------------
    header = (
        f"/-  Per-box instantiation of `RHInBox.rh_in_box_of_certificate` on the box\n"
        f"    `[{s0},{s1}] x [{t0},{t1}]` with `N = {n}` on-line zeros.\n\n"
        f"    Emitted by telperion `emit_per_box_instantiation` (Task 4 driver `--box`/`--height`).\n"
        f"    Geometry: ball center `c = ({cx_s}) + ({cy_s})*I`, radius `R = Real.sqrt ({rsq_s})`,\n"
        f"    chosen so the box is STRICTLY inside the ball and the pole `s = 1` is STRICTLY outside.\n"
        f"    The winding count `N` and on-line zeros are the documented Arb non-kernel inputs\n"
        f"    (supplied as the `hArb`/`hLine` hypotheses).  conjecture1_proved = False. -/\n"
        f"import Mathlib\n"
        f"import RHInBox\n"
        f"import RHInBoxAnalytic\n"
        f"import BoxLocalization\n\n"
        f"open Complex MeasureTheory Real\n"
        f"open scoped Topology\n\n"
        # The instantiation proof is O(N): the on-line Finset is built from a sorted LIST
        # via RHInBox.line_toFinset_card (chain -> Nodup -> card, proved once), so the
        # emitted N-dependent work is just the consecutive chain + 2N linarith bound
        # checks.  Budget scales linearly with generous headroom (_heartbeats_for).
        f"set_option maxHeartbeats {_heartbeats_for(n)}\n\n"
        f"namespace {namespace}\n\n"
    )

    # xs indices are 1-based.
    xs = [f"x{i}" for i in range(1, n + 1)]

    # ---- hLine existential type ------------------------------------------------------
    order_parts = [f"{t0} ≤ x1"] + [f"x{i} < x{i + 1}" for i in range(1, n)] + [f"x{n} ≤ {t1}"]
    order_chain = " ∧ ".join(order_parts)
    zero_parts = [
        f"completedRiemannZeta (1 / 2 + ({x} : ℂ) * Complex.I) = 0" for x in xs
    ]
    zeros_conj = " ∧\n       ".join(zero_parts)
    exists_binder = " ".join(xs)
    hline_type = (
        f"    (hLine : ∃ {exists_binder} : ℝ,\n"
        f"      ({order_chain}) ∧\n"
        f"      ({zeros_conj}))"
    )

    # ---- the full generic Arb bundle at these corners --------------------------------
    # 16 non-vanishing/interior/integrability conjuncts (used by rh_in_box_of_certificate's harb)
    # + the winding value (17th, `= 2*pi*I*N`).  Rendered as a list of conjunct strings so both
    # the `hArb` hypothesis type (all 17) and the reassembled `harb` (first 16) are single-sourced.
    conj = _arb_bundle_conjuncts(s0, s1, t0, t1)
    winding = (
        f"((∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t0}) : ℝ) : ℂ) * I))\n"
        f"          - (∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t1}) : ℝ) : ℂ) * I))\n"
        f"          + I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s1}) : ℝ) : ℂ) + ↑y * I))\n"
        f"          - I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s0}) : ℝ) : ℂ) + ↑y * I))\n"
        f"        = 2 * π * I * ({n} : ℂ))"
    )

    return _build_full_instantiation(
        name=name, namespace=namespace, header=header, n=n,
        s0=s0, s1=s1, t0=t0, t1=t1, cx_s=cx_s, cy_s=cy_s, rsq_s=rsq_s,
        xs=xs, hline_type=hline_type, conj=conj, winding=winding,
    )


def emit_empty_band_instantiation(
    cert: EmptyBandCertificate,
    tag: str,
    *,
    theorem_name: str | None = None,
    namespace: str = "NoZerosInBox",
) -> str:
    """Emit a standalone Lean file certifying the box `[re_lo,re_hi] x [im_lo,im_hi]` is ZERO-FREE.

    The winding-0 empty-band path: instantiate `RHInBoxAnalytic.zeta_count_eq_winding_generic` with
    `N = 0`.  Its conclusion gives a divisor support `s` with `∑_{s} d = 0` and every `d ρ ≥ 1`; a
    nonempty `s` would force `∑ ≥ 1`, so `s = ∅` — every box zero would be in `s`, hence there is
    none.  Emitted theorem `no_zeros_in_box_<tag>`:

        ∀ ρ, (re_lo ≤ ρ.re ≤ re_hi) → (im_lo ≤ ρ.im ≤ im_hi) → riemannZeta ρ ≠ 0

    Documented Arb inputs (hypotheses): `hwind` (the boundary winding integral `= 0`) and `hArb`
    (the routine boundary bundle — the SAME 16 conjuncts as the count-matching atom).  Unlike the
    localization path this exhibits NO on-line zeros: no `hLine`, no Finset, no O(N^2) pairwise
    distinctness, no heartbeat scaling.  `cPB`/`RPB`/`hs1_PB` are top-level so `hArb` forwards
    straight to the atom.  conjecture1_proved = False (VERIFIES the box is zero-free; NOT a proof
    of RH)."""
    if cert.n != 0:
        raise ValueError(f"emit_empty_band_instantiation needs n == 0; got {cert.n}")
    name = theorem_name or f"no_zeros_in_box_{tag}"
    s0 = _rat_lean(cert.re_lo)
    s1 = _rat_lean(cert.re_hi)
    t0 = _rat_lean(cert.im_lo)
    t1 = _rat_lean(cert.im_hi)
    cx, cy, rsq = choose_ball(cert.re_lo, cert.re_hi, cert.im_lo, cert.im_hi)
    cx_s = _rat_lean(cx)
    cy_s = _rat_lean(cy)
    rsq_s = _rat_lean(rsq)

    box_set = f"Set.Icc (({s0}) : ℝ) ({s1}) ×ℂ Set.Icc (({t0}) : ℝ) ({t1})"
    ball = "Metric.ball cPB RPB"
    conj = _arb_bundle_conjuncts(s0, s1, t0, t1)
    conj_join = " ∧\n      ".join(conj)
    # Boundary winding integral LHS (identical rendering to the count-matching emitter).
    wind_lhs = (
        f"(∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t0}) : ℝ) : ℂ) * I))\n"
        f"        - (∫ x in (({s0}) : ℝ)..({s1}), logDeriv riemannZeta (↑x + ((({t1}) : ℝ) : ℂ) * I))\n"
        f"        + I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s1}) : ℝ) : ℂ) + ↑y * I))\n"
        f"        - I • (∫ y in (({t0}) : ℝ)..({t1}), logDeriv riemannZeta (((({s0}) : ℝ) : ℂ) + ↑y * I))"
    )

    lines: list[str] = []
    A = lines.append

    A(
        f"/-  Empty-band (zero-free) certificate for the box `[{s0},{s1}] x [{t0},{t1}]`.\n\n"
        f"    Emitted by telperion `emit_empty_band_instantiation`.  Boundary winding `N = 0`\n"
        f"    (Arb non-kernel input `hwind`) + the routine boundary bundle `hArb` feed\n"
        f"    `RHInBoxAnalytic.zeta_count_eq_winding_generic` at `N = 0`; the resulting divisor\n"
        f"    support has `∑ d = 0` with `d ≥ 1`, forcing it EMPTY, so the box holds no zeta zero.\n"
        f"    Ball center `c = ({cx_s}) + ({cy_s})*I`, radius `R = Real.sqrt ({rsq_s})` (box strictly\n"
        f"    inside, pole `s = 1` strictly outside).  conjecture1_proved = False. -/\n"
        f"import Mathlib\n"
        f"import RHInBox\n"
        f"import RHInBoxAnalytic\n"
        f"import BoxLocalization\n\n"
        f"open Complex MeasureTheory Real\n"
        f"open scoped Topology\n\n"
        f"namespace {namespace}\n\n"
    )
    A(f"/-- Chosen Blaschke ball center for `[{s0},{s1}] x [{t0},{t1}]`. -/\n")
    A(f"noncomputable def cPB : ℂ := ⟨({cx_s}), ({cy_s})⟩\n\n")
    A(f"/-- Chosen Blaschke ball radius (squared radius `{rsq_s}`). -/\n")
    A(f"noncomputable def RPB : ℝ := Real.sqrt ({rsq_s})\n\n")
    A(f"theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)\n\n")
    # hs1 as a TOP-LEVEL theorem so the atom's `let s := zeroFinset cPB RPB hs1_PB` is nameable
    # in the `hArb` hypothesis type below.
    A(f"/-- The pole `s = 1` is strictly outside the chosen ball. -/\n")
    A(f"theorem hs1_PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by\n")
    A(f"  rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"  unfold cPB RPB\n")
    A(f"  intro hlt\n")
    A(f"  simp only [Complex.one_re, Complex.one_im] at hlt\n")
    A(f"  have hle : Real.sqrt ({rsq_s}) ≤\n")
    A(f"      Real.sqrt (((1 : ℝ) - ({cx_s})) ^ 2 + ((0 : ℝ) - ({cy_s})) ^ 2) :=\n")
    A(f"    Real.sqrt_le_sqrt (by norm_num)\n")
    A(f"  linarith [hlt, hle]\n\n")

    A(f"/-- **Zero-free box `[{s0},{s1}] x [{t0},{t1}]` via winding `N = 0`.**  Instantiates\n"
      f"    `RHInBoxAnalytic.zeta_count_eq_winding_generic` at `N = 0`; the empty divisor support\n"
      f"    means no zeta zero lies in the box.  Documented Arb inputs: `hwind` (winding `= 0`) and\n"
      f"    `hArb` (boundary bundle).  conjecture1_proved = False. -/\n")
    A(f"theorem {name}\n")
    A(f"    (hwind : {wind_lhs}\n      = 0)\n")
    A(f"    (hArb : ∀ (E : ℂ → ℂ),\n")
    A(f"      let s := RHInBoxAnalytic.zeroFinset cPB RPB hs1_PB\n")
    A(f"      let d := (MeromorphicOn.divisor riemannZeta ({ball}) : ℂ → ℤ)\n")
    A(f"      DifferentiableOn ℂ E ({box_set}) →\n")
    A(f"      (∀ z ∈ {ball}, riemannZeta z ≠ 0 →\n")
    A(f"        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →\n")
    A(f"      {conj_join}) :\n")
    A(f"    (∀ ρ : ℂ, ((({s0}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({s1})) → ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) →\n")
    A(f"      riemannZeta ρ ≠ 0) := by\n")
    A(f"  have hRpos : (0 : ℝ) < RPB := RPB_pos\n")
    A(f"  have hsig : (({s0}) : ℝ) ≤ ({s1}) := by norm_num\n")
    A(f"  have hTle : (({t0}) : ℝ) ≤ ({t1}) := by norm_num\n")
    A(f"  have hbox_ball : ∀ ρ : ℂ, ((({s0}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({s1})) →\n")
    A(f"      ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) → ρ ∈ Metric.ball cPB RPB := by\n")
    A(f"    intro ρ hre him\n")
    A(f"    rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"    unfold cPB RPB\n")
    A(f"    apply Real.sqrt_lt_sqrt (by positivity)\n")
    A(f"    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2\n")
    A(f"    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ({cx_s})), sq_nonneg (ρ.im - ({cy_s}))]\n")
    # Convert the winding `= 0` hypothesis to the atom's `= 2*π*I*((0:ℤ):ℂ)` form.
    A(f"  have hwind0 : {wind_lhs}\n")
    A(f"      = 2 * π * I * ((0 : ℤ) : ℂ) := by rw [hwind]; simp\n")
    A(f"  obtain ⟨s, d, hd1, hcap, hsum⟩ :=\n")
    A(f"    RHInBoxAnalytic.zeta_count_eq_winding_generic (({s0}) : ℝ) ({s1}) ({t0}) ({t1})\n")
    A(f"      cPB RPB 0 hRpos hsig hTle hbox_ball hs1_PB hwind0 hArb\n")
    A(f"  intro ρ hre him hzero\n")
    A(f"  have hin : ρ ∈ s := hcap ρ hre him hzero\n")
    A(f"  have hnonneg : ∀ ρ' ∈ s, (0 : ℤ) ≤ d ρ' := fun ρ' hρ' => le_trans (by norm_num) (hd1 ρ' hρ')\n")
    A(f"  have hle : d ρ ≤ ∑ ρ' ∈ s, d ρ' := Finset.single_le_sum hnonneg hin\n")
    A(f"  rw [hsum] at hle\n")
    A(f"  have h1 := hd1 ρ hin\n")
    A(f"  omega\n")
    A(f"\nend {namespace}\n")
    return "".join(lines)


def box_localization_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a box-localization family (kind='box_localization').  ``spec``: ``pt -> {"n_line",
    "n_total", ...box corners}``.  Refuses `n_line > n_total` or `n_line != n_total` at
    certification (the negative controls)."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("box_localization", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert: n_line = n_total = 5 on [2/5,3/5]x[10,35] ===")
    c = box_localization_certificate(5, 5)
    print(f"cert OK: box=[{c.re_lo},{c.re_hi}]x[{c.im_lo},{c.im_hi}] n={c.n}")
    print("\n=== NEGATIVE CONTROL: n_line > n_total must raise ===")
    try:
        box_localization_certificate(6, 5)
        raise SystemExit("FAIL: n_line>n_total not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== NEGATIVE CONTROL: n_line != n_total must raise ===")
    try:
        box_localization_certificate(4, 5)
        raise SystemExit("FAIL: n_line!=n_total not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = box_localization_family(
        "T", GridSpec([("case", [0])]), lambda pt: "box_localization_a",
        spec=lambda pt: {"n_line": 5, "n_total": 5},
    )
    inst, _ = certify_box_localization_point(fam, {"case": 0}, "box_localization_a")

    class _V:
        instances = [inst]

    body, nthm = BoxLocalizationEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:500]}\n...[truncated]")
