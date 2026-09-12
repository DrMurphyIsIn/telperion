"""T5 Turing-band emitter: per-band Lean instantiation of TuringBand.turing_band_on_line.

The RvM edge-decomposition replacement for the four-edge winding certificate
(`emit_box_localization.emit_per_box_instantiation`).  The emitted theorem takes
the SAME `hLine` on-line input, and — in place of the 17-conjunct `hArb` game +
boundary winding integral — a single `hArbT` bundle: three edge non-vanishing
facts, zero confinement, and rational interval enclosures of the five RvM edge
argument-changes (`arb_edges.enclose_band_edges`).  The kernel pins the count by
interval arithmetic + rational pi bounds (`TuringBand.band_count_eq`) and closes
with the standard exhaustion core.  Conclusion shape is IDENTICAL to the winding
route, so height-chain glue consumes T5 bands unchanged.

Trust boundary: unchanged in kind — all Arb inputs are documented hypotheses.
conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

import sympy as sp

from telperion.emit_box_localization import _rat_lean, choose_ball, _heartbeats_for

__all__ = [
    "emit_turing_band_instantiation", "choose_ball_tight",
    "TuringBandCertificate", "turing_band_certificate",
    "certify_turing_band_point", "TuringBandEmitter", "turing_band_family",
]

_EDGE_KEYS = ("av2", "aht", "ahb", "ag1", "ag2")


@dataclass(frozen=True)
class TuringBandCertificate:
    """Self-checked T5 band certificate: the exact data the emitted Lean states.

    `edges` holds the OUTWARD-ROUNDED rational literals that appear verbatim in
    the emitted `hArbT` hypothesis (not the raw Arb dyadics).  Constructed only
    through `turing_band_certificate`, whose refusal guards enforce (in exact
    rational arithmetic) everything the kernel's `hpin` side conditions need."""

    n: int
    re_lo: str
    re_hi: str
    im_lo: str
    im_hi: str
    edges: dict = field(default_factory=dict)   # key -> (Fraction lo, Fraction hi)

    def to_json_dict(self) -> dict:
        return {
            "kind": "turing_band", "n": self.n,
            "re_lo": self.re_lo, "re_hi": self.re_hi,
            "im_lo": self.im_lo, "im_hi": self.im_hi,
            "edges": {k: [str(v[0]), str(v[1])] for k, v in self.edges.items()},
        }


def turing_band_certificate(*, n, re_lo, re_hi, im_lo, im_hi, edges,
                            round_digits: int = 12) -> TuringBandCertificate:
    """Build and EXACTLY self-check a T5 band certificate.  REFUSES (ValueError):

    * `n < 1` (an empty band belongs to the empty-band route);
    * an invalid box (σ-range not straddling 1/2 inside [-1,2], or Im ≤ 0);
    * a non-interval edge enclosure (L > H);
    * edge sums that fail the kernel's `hpin` pinning conditions at `n` — the
      RvM-count == on-line-count cross-check, in exact rational arithmetic
      against the same rational π bounds (3.14 < π < 3.1416) the kernel uses."""
    if not isinstance(n, int) or n < 1:
        raise ValueError(f"turing_band_certificate: n must be an int >= 1; got {n!r}")
    rl, rh = Fraction(re_lo), Fraction(re_hi)
    il, ih = Fraction(im_lo), Fraction(im_hi)
    if not (Fraction(-1) <= rl < Fraction(1, 2) < rh <= 2):
        raise ValueError(
            f"turing_band_certificate: sigma-range [{rl},{rh}] must straddle 1/2 within [-1,2]")
    if not (0 < il < ih):
        raise ValueError(f"turing_band_certificate: need 0 < {il} < {ih}")
    lit = {}
    for k in _EDGE_KEYS:
        L, H = Fraction(edges[k][0]), Fraction(edges[k][1])
        if L > H:
            raise ValueError(f"turing_band_certificate: edge {k} enclosure inverted")
        lit[k] = (_frac_out(L, up=False, digits=round_digits),
                  _frac_out(H, up=True, digits=round_digits))
    (L1, H1), (L2, H2), (L3, H3), (L4, H4), (L5, H5) = (lit[k] for k in _EDGE_KEYS)
    lo_sum = 2 * L1 + L2 - H3 + L4 + L5
    hi_sum = 2 * H1 + H2 - L3 + H4 + H5
    if not (2 * Fraction(31416, 10000) * (n - 1) < lo_sum
            and hi_sum < 2 * Fraction(314, 100) * (n + 1)):
        raise ValueError(
            f"turing_band_certificate: edge sums [{float(lo_sum)}, {float(hi_sum)}] do not "
            f"pin N = {n} (2*pi*N = {2 * math.pi * n:.4f}) — enclosure too wide or count wrong")
    return TuringBandCertificate(
        n=n, re_lo=str(rl), re_hi=str(rh), im_lo=str(il), im_hi=str(ih), edges=lit)


def choose_ball_tight(re_lo, re_hi, im_lo, im_hi, margin=sp.Rational(1, 16)):
    """Tight Blaschke ball for the T5 rectangle: radius^2 = corner-distance^2 + margin.

    The winding route's `choose_ball` splits the difference to the pole s = 1 —
    at campaign heights that yields a radius ~T/√2 ball containing millions of
    zeros, which breaks the T5 confinement input `hins`.  Here the ball hugs the
    rectangle (poke ≈ (2.25 + margin)/height beyond the horizontal edges), and
    the pole stays strictly outside whenever `im_lo` is comfortably positive."""
    rl, rh, il, ih = (sp.Rational(v) for v in (re_lo, re_hi, im_lo, im_hi))
    cx = (rl + rh) / 2
    cy = (il + ih) / 2
    dc2 = ((rh - rl) / 2) ** 2 + ((ih - il) / 2) ** 2
    d12 = (1 - cx) ** 2 + cy ** 2
    rsq = dc2 + margin
    if not (rsq < d12):
        raise ValueError(
            f"choose_ball_tight: rsq ({rsq}) >= pole-distance^2 ({d12})")
    return cx, cy, rsq


def _frac_out(x: Fraction, up: bool, digits: int = 12) -> Fraction:
    """Outward-round a Fraction to ~`digits` decimal places (small Lean literals)."""
    scale = 10 ** digits
    n = x * scale
    n = math.ceil(n) if up else math.floor(n)
    return Fraction(n, scale)


def _fl(x: Fraction) -> str:
    return f"{x.numerator} / {x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def emit_turing_band_instantiation(
    *, n: int, re_lo, re_hi, im_lo, im_hi, edges: dict, tag: str,
    namespace: str | None = None, theorem_name: str | None = None,
    cert_sink: dict | None = None,
) -> str:
    """Emit the T5 per-band Lean file (band theorem + kernel statement-match gate).

    edges: dict from arb_edges.enclose_band_edges — keys av2/aht/ahb/ag1/ag2,
    values (L, H) Fractions enclosing the respective argChange quantities.
    All refusal guards live in `turing_band_certificate`.  If `cert_sink` is a
    dict it is filled with the certificate's JSON-able record (the `.cert.json`
    sidecar consumed by the post-hoc `statement_match_check` audit)."""
    cert = turing_band_certificate(
        n=n, re_lo=re_lo, re_hi=re_hi, im_lo=im_lo, im_hi=im_hi, edges=edges)
    if cert_sink is not None:
        cert_sink.update(cert.to_json_dict())
    return _render_turing_band(cert, tag=tag, namespace=namespace,
                               theorem_name=theorem_name)


def _render_turing_band(cert: TuringBandCertificate, *, tag: str,
                        namespace: str | None = None,
                        theorem_name: str | None = None) -> str:
    n = cert.n
    namespace = namespace or f"RHInBoxT_{tag}"
    name = theorem_name or f"rh_in_box_{tag}"
    s0 = _rat_lean(sp.Rational(cert.re_lo))
    s1 = _rat_lean(sp.Rational(cert.re_hi))
    t0 = _rat_lean(sp.Rational(cert.im_lo))
    t1 = _rat_lean(sp.Rational(cert.im_hi))
    # Tight ball covering the RvM rectangle [-1,2] x [T0,T1] (pole s=1 strictly outside).
    cx, cy, rsq = choose_ball_tight(-1, 2, cert.im_lo, cert.im_hi)
    cx_s, cy_s, rsq_s = _rat_lean(cx), _rat_lean(cy), _rat_lean(rsq)

    lit = cert.edges
    (L1, H1), (L2, H2), (L3, H3), (L4, H4), (L5, H5) = (lit[k] for k in _EDGE_KEYS)

    # LIST-FORM on-line input: O(1) destructuring (the 2N+1-component nested
    # existential of the winding route costs ~45s of `obtain` at N ~= 42 — the
    # dominant per-band elaboration cost; this form removes it entirely).
    hline_type = (
        f"    (hLine : ∃ xs : List ℝ, xs.length = {n} ∧ xs.IsChain (· < ·) ∧\n"
        f"      (∀ t ∈ xs, (({t0}) : ℝ) ≤ t ∧ t ≤ ({t1})) ∧\n"
        f"      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))")

    harbt_type = (
        f"    (hArbT :\n"
        f"      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + ((({t0}) : ℝ) : ℂ) * I) ≠ 0) ∧\n"
        f"      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + ((({t1}) : ℝ) : ℂ) * I) ≠ 0) ∧\n"
        f"      (∀ y ∈ Set.uIcc (({t0}) : ℝ) ({t1}), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧\n"
        f"      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,\n"
        f"        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ (({t0}) : ℝ) < ρ.im ∧ ρ.im < ({t1})) ∧\n"
        f"      DiffractionCore.argChangeVert riemannZeta 2 ({t0}) ({t1}) ∈ Set.Icc (({_fl(L1)}) : ℝ) ({_fl(H1)}) ∧\n"
        f"      DiffractionCore.argChangeHoriz riemannZeta ({t1}) 2 (-1) ∈ Set.Icc (({_fl(L2)}) : ℝ) ({_fl(H2)}) ∧\n"
        f"      DiffractionCore.argChangeHoriz riemannZeta ({t0}) 2 (-1) ∈ Set.Icc (({_fl(L3)}) : ℝ) ({_fl(H3)}) ∧\n"
        f"      DiffractionCore.argChangeVert Gammaℝ (-1) ({t0}) ({t1}) ∈ Set.Icc (({_fl(L4)}) : ℝ) ({_fl(H4)}) ∧\n"
        f"      DiffractionCore.argChangeVert Gammaℝ 2 ({t0}) ({t1}) ∈ Set.Icc (({_fl(L5)}) : ℝ) ({_fl(H5)}))")

    concl = (
        f"    (∀ ρ, ((({s0}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({s1})) → ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) →\n"
        f"      riemannZeta ρ = 0 → ρ.re = 1 / 2)")

    lines: list[str] = []
    A = lines.append
    A(f"/-  T5 TURING-BAND certificate for `[{s0},{s1}] x [{t0},{t1}]` with `N = {n}`:\n"
      f"    the RvM edge decomposition (no boundary winding integral, no in-strip edges).\n"
      f"    Emitted by telperion `emit_turing_band_instantiation`.\n"
      f"    Arb non-kernel inputs: `hLine` ({n} on-line zeros) + `hArbT` (edge non-vanishing,\n"
      f"    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/\n")
    A("import Mathlib\nimport RHInBox\nimport TuringBand\nimport BoxLocalization\n\n")
    A("open Complex MeasureTheory Real\nopen scoped Topology\n\n")
    A(f"set_option maxHeartbeats {_heartbeats_for(n)}\n\n")
    A(f"namespace {namespace}\n\n")
    A(f"/-- Ball center covering the RvM rectangle `[-1,2] x [{t0},{t1}]`. -/\n")
    A(f"noncomputable def cPB : ℂ := ⟨({cx_s}), ({cy_s})⟩\n\n")
    A(f"noncomputable def RPB : ℝ := Real.sqrt ({rsq_s})\n\n")
    A(f"theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)\n\n")
    A(f"theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by\n")
    A(f"  rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"  unfold cPB RPB\n")
    A(f"  intro hlt\n")
    A(f"  simp only [Complex.one_re, Complex.one_im] at hlt\n")
    A(f"  have hle : Real.sqrt ({rsq_s}) ≤\n")
    A(f"      Real.sqrt (((1 : ℝ) - ({cx_s})) ^ 2 + ((0 : ℝ) - ({cy_s})) ^ 2) :=\n")
    A(f"    Real.sqrt_le_sqrt (by norm_num)\n")
    A(f"  linarith [hlt, hle]\n\n")
    A(f"/-- **T5 band `[{s0},{s1}] x [{t0},{t1}]`, `N = {n}`** via the RvM edge decomposition.\n"
      f"    conjecture1_proved = False. -/\n")
    A(f"theorem {name}\n")
    A(hline_type + "\n")
    A(harbt_type + " :\n")
    A(concl + " := by\n")
    # geometry
    A(f"  have hRpos : (0 : ℝ) < RPB := RPB_pos\n")
    A(f"  have hT0 : (0 : ℝ) < ({t0}) := by norm_num\n")
    A(f"  have hTle : (({t0}) : ℝ) ≤ ({t1}) := by norm_num\n")
    A(f"  have hs0 : (-1 : ℝ) ≤ ({s0}) := by norm_num\n")
    A(f"  have hs2 : (({s1}) : ℝ) ≤ 2 := by norm_num\n")
    A(f"  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →\n")
    A(f"      ((({t0}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({t1})) → ρ ∈ Metric.ball cPB RPB := by\n")
    A(f"    intro ρ hre him\n")
    A(f"    rw [Metric.mem_ball, Complex.dist_eq_re_im]\n")
    A(f"    unfold cPB RPB\n")
    A(f"    apply Real.sqrt_lt_sqrt (by positivity)\n")
    A(f"    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2\n")
    A(f"    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ({cx_s})), sq_nonneg (ρ.im - ({cy_s}))]\n")
    # on-line finset — LIST FORM: constant-size proof, no per-element terms
    A(f"  obtain ⟨xsL, hlen, hchain, hbnd, hzeros⟩ := hLine\n")
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
    A(f"  set T : Finset ℂ :=\n")
    A(f"    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef\n")
    A(f"  have hTcard : T.card = {n} := by\n")
    A(f"    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]\n")
    A(f"  have hre_lo : (({s0}) : ℝ) ≤ 1 / 2 := by norm_num\n")
    A(f"  have hre_hi : (1 / 2 : ℝ) ≤ ({s1}) := by norm_num\n")
    A(f"  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)\n")
    A(f"  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))\n")
    A(f"  have hTbox : ∀ z ∈ T, ((({s0}) : ℝ) ≤ z.re ∧ z.re ≤ ({s1})) ∧ ((({t0}) : ℝ) ≤ z.im ∧ z.im ≤ ({t1})) := by\n")
    A(f"    rw [hTdef]\n")
    A(f"    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)\n")
    A(f"    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,\n")
    A(f"      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩\n")
    # unpack hArbT, pin, close
    A(f"  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT\n")
    A(f"  have hN1 : 1 ≤ {n} := by norm_num\n")
    A(f"  have hpinL : 2 * 3.1416 * (({n} : ℝ) - 1) <\n")
    A(f"      2 * (({_fl(L1)}) : ℝ) + ({_fl(L2)}) - ({_fl(H3)}) + ({_fl(L4)}) + ({_fl(L5)}) := by norm_num\n")
    A(f"  have hpinH : 2 * (({_fl(H1)}) : ℝ) + ({_fl(H2)}) - ({_fl(L3)}) + ({_fl(H4)}) + ({_fl(H5)}) <\n")
    A(f"      2 * 3.14 * (({n} : ℝ) + 1) := by norm_num\n")
    A(f"  have hcountN : (({n} : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]\n")
    A(f"  exact TuringBand.turing_band_on_line (({s0}) : ℝ) ({s1}) ({t0}) ({t1}) hT0 hTle hs0 hs2\n")
    A(f"    cPB RPB hRpos {n} hN1\n")
    A(f"    ({_fl(L1)}) ({_fl(H1)}) ({_fl(L2)}) ({_fl(H2)}) ({_fl(L3)}) ({_fl(H3)}) ({_fl(L4)}) ({_fl(H4)}) ({_fl(L5)}) ({_fl(H5)})\n")
    A(f"    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH\n")
    A(f"    T hTline hTzero hTbox hcountN\n")
    # ---- kernel statement-match gate --------------------------------------------
    # Elaborates iff the band theorem's Pi-type is DEFEQ to the canonical
    # TuringBand.BandStatement at these parameters: the statement SHAPE is pinned
    # by the hand-audited kernel definition, so an over-quantified / weakened /
    # truncated emitted statement FAILS THE BUILD (the 2026-09-12 winding-route
    # hArb bug class).  The emitter can only vary parameters, which the driver
    # cross-checks numerically.
    A(f"\n/-- Kernel statement-match gate: `{name}` states EXACTLY the canonical\n")
    A(f"    `TuringBand.BandStatement` at this band's parameters (defeq).  -/\n")
    A(f"theorem statement_match :\n")
    A(f"    TuringBand.BandStatement (({s0}) : ℝ) ({s1}) ({t0}) ({t1}) {n}\n")
    A(f"      ({_fl(L1)}) ({_fl(H1)}) ({_fl(L2)}) ({_fl(H2)}) ({_fl(L3)}) ({_fl(H3)})\n")
    A(f"      ({_fl(L4)}) ({_fl(H4)}) ({_fl(L5)}) ({_fl(H5)}) cPB RPB hs1PB :=\n")
    A(f"  {name}\n")
    A(f"\nend {namespace}\n")
    return "".join(lines)


# --------------------------------------------------------------------------- #
# First-class Telperion kind: "turing_band"                                    #
# --------------------------------------------------------------------------- #

def certify_turing_band_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys
    ``n, re_lo, re_hi, im_lo, im_hi, edges`` (edges: av2/aht/ahb/ag1/ag2 ->
    (lo, hi) rationals).  All refusals via `turing_band_certificate`."""
    from telperion.certify import CertifiedInstance

    spec = family.special[1](pt)
    cert = turing_band_certificate(
        n=int(spec["n"]), re_lo=spec["re_lo"], re_hi=spec["re_hi"],
        im_lo=spec["im_lo"], im_hi=spec["im_hi"], edges=spec["edges"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _band_tag_of(cert: TuringBandCertificate) -> str:
    def _t(v):
        v = Fraction(v)
        return (f"{v.numerator}" if v.denominator == 1
                else f"{v.numerator}d{v.denominator}").replace("-", "m")
    return f"{_t(cert.re_lo)}_{_t(cert.re_hi)}_{_t(cert.im_lo)}_{_t(cert.im_hi)}"


def _make_turing_band_emitter():
    """Deferred Emitter subclass construction (avoids a workflow import cycle
    at module load; the class is materialized once, on first use)."""
    from telperion.workflow import Emitter

    @dataclass
    class _TuringBandEmitter(Emitter):
        """Emit one T5 band certificate file per instance (kind="turing_band").

        Each unit is a standalone Lean module: the band theorem
        `rh_in_box_<tag>` (RvM edge decomposition through
        `TuringBand.turing_band_on_line`) plus the kernel `statement_match`
        gate against the canonical `TuringBand.BandStatement`.  The canonical
        gate supersedes the generic `emit_gate` example (which single-sources
        the type string and can therefore only catch post-emission drift, not
        emitter statement bugs)."""

        def __post_init__(self):
            self.kind = "turing_band"
            self.requires_prelude = ()
            self.emit_statement_gate = False  # superseded by BandStatement gate

        def emit_body(self, fam, profile=None):
            texts, nthm = [], 0
            for inst in fam.instances:
                cert: TuringBandCertificate = inst.payload
                texts.append(_render_turing_band(
                    cert, tag=_band_tag_of(cert), theorem_name=inst.lean_name))
                nthm += 2  # band theorem + statement_match gate
            return "\n".join(texts), nthm

    return _TuringBandEmitter


_EMITTER_CLS = None


def TuringBandEmitter(*args, **kwargs):
    """Factory matching the registry's `EmitterClass()` call convention."""
    global _EMITTER_CLS
    if _EMITTER_CLS is None:
        _EMITTER_CLS = _make_turing_band_emitter()
    return _EMITTER_CLS(*args, **kwargs)


def turing_band_family(name, symbols, grid, lean_name, spec, constants=None):
    """Build a turing_band family (kind='turing_band').

    ``spec``: callable ``pt -> dict`` with keys n, re_lo, re_hi, im_lo, im_hi,
    edges (dict av2/aht/ahb/ag1/ag2 -> (lo, hi) rationals).  Certification
    REFUSES (ValueError) any point failing `turing_band_certificate`'s guards
    (n < 1, invalid box, inverted enclosure, pinning failure)."""
    from telperion.family import InequalityFamily

    return InequalityFamily(
        name=name, symbols=tuple(symbols), grid=grid, lean_name=lean_name,
        special=("turing_band", spec), constants=dict(constants or {}))
