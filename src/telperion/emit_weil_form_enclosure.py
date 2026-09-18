"""Weil-form enclosure emitter -- the E8 pairing as a NAMED-HYPOTHESIS trust seam.

The registry node `RH_limit_explicit_formula` (E8, `WeilExplicit`; `E6Bridge4.lean`) proves the
unconditional Weil/Guinand explicit formula for smooth compactly supported tests: the zero side
`HasSum (fun rho => zeroMult rho * weilKernel g rho) (archSide g - primeSide g)`.  Until now
NOTHING in Telperion evaluated that right-hand side.  `bragg_floor` certifies finite Bragg
amplitudes against an archimedean floor per Li order `n`; the E8 pairing itself -- the finite
prime sum `sum_{n <= e^R} Lambda(n)/sqrt n (g(log n) + g(-log n))`, the two pole terms
`h(+- i/2)`, the `-g(0) log pi` term and the digamma integral
`(1/2pi) int h(r) Re psi(1/4 + i r/2) dr` -- had no certificate type.  This emitter is that type.

THE DISCIPLINE (identical to `BraggDefect`'s `hexp` seam and the Li ladder's `henc`)
------------------------------------------------------------------------------------
`telperion.weil_form_eval` computes an outward-rounded RATIONAL enclosure `[lo, hi]` of
`Re weilForm f` with rigorous Arb ball arithmetic (interior-cut collars, an `N`-fold
integration-by-parts archimedean tail, and an explicit `|Re psi| <= log(|y|+2) + 4.4` bound --
see that module's docstring for every step).  The EMITTED LEAN never asserts that enclosure.
It takes the enclosure as a NAMED HYPOTHESIS

    henc : (lo : R) <= (weilForm (autocorr g)).re AND (weilForm (autocorr g)).re <= hi

and the kernel proves only its CONSEQUENCE.  Two consequences are emitted:

  * `positivity` -- `0 < (weilForm (autocorr g)).re` from `0 < lo`: the concrete instance of
    Weil positivity that RH predicts for an autocorrelation, checked rather than assumed.
  * `gram_minor` -- from the three boxes of a `2 x 2` cross-correlation block,
    `0 < W_ii` and `0 < W_ii * W_jj - W_ij^2`: the leading principal minors of the Weil-Gram
    block are positive, i.e. that block is POSITIVE DEFINITE (Sylvester).  This is the datum a
    Gram-inertia consumer wants, in the only form a kernel can hold it.

Both route through two abstract helper lemmas (`box_pos`, `box_minor_pos`, emitted once in the
prelude) so that every instance's load-bearing content is exactly its rational literals inside
`norm_num` goals -- which is what makes the negative control bite.

WHAT THIS CERTIFIES, AND WHAT IT DOES NOT (read before citing it)
-----------------------------------------------------------------
Certified: a finite, kernel-checkable consequence of one Arb enclosure.  Category-(b): finite,
consistent with RH, PROVING NOTHING about RH.  A positive `weilForm (autocorr g)` is what RH
PREDICTS; observing it confirms nothing (Weil positivity over EVERY admissible test function is
RH-equivalent, and no finite family of test functions approaches "every").  The falsifiability
face is the honest direction and is emitted with it: `weil_negative_refutes_rh` says that a
certified STRICTLY NEGATIVE autocorrelation pairing refutes RH -- through the explicit,
UNDISCHARGED hypothesis `hpos : RiemannHypothesis -> 0 <= (weilForm (autocorr g)).re` (the
classical Weil direction, never proved here).  Not expected to fire; emitted so the ladder is
an experiment that could have falsified, not confirmation-only.

REFUSALS (honest, never a false theorem)
-----------------------------------------
  * a test function that is NOT compactly supported -- the PNT growth trap: for a merely
    Schwartz `g` the prime side DIVERGES (`sum_{n<=e^R} Lambda(n) n^{-1/2} ~ 2 e^{R/2}`, E8
    design memo 2.2), so no enclosure of it exists to emit;
  * an enclosure whose width exceeds the instance's declared threshold (a box too loose to
    carry its consequence is not certified, it is noise);
  * a `k x k` Gram whose `(i,j)` and `(j,i)` boxes do not overlap -- Hermitian inconsistency
    means the evaluator disagrees with itself and nothing is emitted;
  * `lo <= 0` for a positivity instance, or a non-positive worst-case minor
    `lo_ii * lo_jj - max(|c|)^2 <= 0` for a Gram block: the consequence is simply not implied
    by the box, so we refuse rather than weaken the claim.

Arb is a NON-KERNEL trust seam.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

POSITIVITY = "positivity"
GRAM_MINOR = "gram_minor"
_SHAPES = (POSITIVITY, GRAM_MINOR)


@dataclass(frozen=True)
class WeilBox:
    """One Arb-enclosed Weil-Gram entry `Re weilForm (crossCorr g_i g_j) in [lo, hi]`."""

    i: int
    j: int
    label_i: str
    label_j: str
    lo: sp.Rational
    hi: sp.Rational

    @property
    def width(self) -> sp.Rational:
        return sp.Rational(self.hi - self.lo)


@dataclass(frozen=True)
class WeilFormEnclosureData:
    """Raw (Arb-produced) input to the certificate layer.

    `support_radius` is the compact-support witness of the underlying test functions: `None`
    (or a non-positive value) marks a non-compactly-supported `g` and is REFUSED."""

    shape: str
    boxes: tuple
    max_width: sp.Rational
    support_radius: object = None
    arch_T: int = 0
    n_byparts: int = 0
    mirror_boxes: tuple = ()


@dataclass(frozen=True)
class WeilFormEnclosureCert:
    """A certified Weil-form enclosure instance: the boxes plus the shape of the kernel
    consequence they carry.  `positivity` holds one box; `gram_minor` holds exactly three,
    ordered `(i,i), (j,j), (i,j)`."""

    shape: str
    boxes: tuple
    max_width: sp.Rational
    support_radius: sp.Rational
    arch_T: int
    n_byparts: int

    @property
    def margin(self) -> sp.Rational:
        if self.shape == POSITIVITY:
            return sp.Rational(self.boxes[0].lo)
        a, b, c = self.boxes
        cmax = sp.Max(abs(sp.Rational(c.lo)), abs(sp.Rational(c.hi)))
        return sp.Rational(sp.nsimplify(sp.Rational(a.lo) * sp.Rational(b.lo) - cmax**2))


def weil_form_enclosure_certificate(data: WeilFormEnclosureData) -> WeilFormEnclosureCert:
    """Build (and exactly re-check) a Weil-form enclosure certificate.

    Every refusal listed in the module docstring is enforced here; nothing that fails is
    weakened and re-emitted."""
    if data.shape not in _SHAPES:
        raise ValueError(
            f"weil_form_enclosure REFUSED: unknown shape {data.shape!r}, expected one of {_SHAPES}")
    # --- the PNT growth trap: compact support is not optional ---------------------------
    if data.support_radius is None or sp.Rational(data.support_radius) <= 0:
        raise ValueError(
            "weil_form_enclosure REFUSED: the test function is not compactly supported "
            "(support_radius is None/non-positive) -- primeSide DIVERGES for a merely Schwartz "
            "g (sum_{n<=e^R} Lambda(n) n^{-1/2} ~ 2 e^{R/2}; E8 design memo section 2.2), so "
            "there is no pairing to enclose")
    boxes = tuple(data.boxes)
    if not boxes:
        raise ValueError("weil_form_enclosure REFUSED: no enclosure boxes supplied (phantom)")
    max_width = sp.Rational(data.max_width)
    if max_width <= 0:
        raise ValueError(
            f"weil_form_enclosure REFUSED: max_width must be > 0, got {max_width}")
    for b in boxes:
        lo, hi = sp.Rational(b.lo), sp.Rational(b.hi)
        if lo > hi:
            raise ValueError(
                f"weil_form_enclosure REFUSED: inverted box [{lo}, {hi}] at entry "
                f"({b.i},{b.j}) -- the evaluator disagrees with itself")
        if hi - lo > max_width:
            raise ValueError(
                f"weil_form_enclosure REFUSED at entry ({b.i},{b.j}): enclosure width "
                f"{sp.nsimplify(hi - lo)} exceeds the declared threshold {max_width} -- a box "
                f"too loose to carry its consequence is noise, not a certificate")
    # --- Hermitian consistency of any supplied (j,i) mirrors ------------------------------
    by_pair = {(b.i, b.j): b for b in boxes}
    for m in data.mirror_boxes:
        key = (m.j, m.i)
        if key not in by_pair:
            continue
        b = by_pair[key]
        if sp.Rational(m.hi) < sp.Rational(b.lo) or sp.Rational(m.lo) > sp.Rational(b.hi):
            raise ValueError(
                f"weil_form_enclosure REFUSED: entries ({b.i},{b.j}) and ({m.i},{m.j}) are not "
                f"Hermitian-consistent -- boxes [{b.lo}, {b.hi}] and [{m.lo}, {m.hi}] are "
                f"disjoint")
    # --- shape-specific content -----------------------------------------------------------
    if data.shape == POSITIVITY:
        if len(boxes) != 1:
            raise ValueError(
                f"weil_form_enclosure REFUSED: positivity shape takes exactly 1 box, got "
                f"{len(boxes)}")
        if sp.Rational(boxes[0].lo) <= 0:
            raise ValueError(
                f"weil_form_enclosure REFUSED: lo = {boxes[0].lo} <= 0, so the box does not "
                f"imply 0 < weilForm -- refusing rather than weakening the claim (a NEGATIVE "
                f"certified pairing belongs in weil_negative_refutes_rh, not here)")
    else:
        if len(boxes) != 3:
            raise ValueError(
                f"weil_form_enclosure REFUSED: gram_minor shape takes exactly 3 boxes "
                f"((i,i), (j,j), (i,j)), got {len(boxes)}")
        a, b, c = boxes
        if not (a.i == a.j and b.i == b.j and c.i == a.i and c.j == b.i):
            raise ValueError(
                f"weil_form_enclosure REFUSED: gram_minor boxes must be ((i,i), (j,j), (i,j)), "
                f"got ({a.i},{a.j}), ({b.i},{b.j}), ({c.i},{c.j})")
        for d in (a, b):
            if sp.Rational(d.lo) <= 0:
                raise ValueError(
                    f"weil_form_enclosure REFUSED: diagonal entry ({d.i},{d.j}) has lo = "
                    f"{d.lo} <= 0, so Sylvester's first minor is not implied")
    cert = WeilFormEnclosureCert(
        shape=data.shape,
        boxes=boxes,
        max_width=max_width,
        support_radius=sp.Rational(data.support_radius),
        arch_T=int(data.arch_T),
        n_byparts=int(data.n_byparts),
    )
    if cert.margin <= 0:
        raise ValueError(
            f"weil_form_enclosure REFUSED ({cert.shape}): margin {cert.margin} <= 0 -- the "
            f"enclosure does not imply the consequence at this width (tighten the enclosure or "
            f"this block is not finitely certifiable)")
    return cert


def certify_weil_form_enclosure_point(family, pt, name):
    """Certify one Weil-form enclosure instance: ``(CertifiedInstance, 1)``."""
    data = family.special[1](pt)
    cert = weil_form_enclosure_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# --------------------------------------------------------------------------------------
# Lean rendering.
# --------------------------------------------------------------------------------------

def _wf(var: str, other: str | None = None) -> str:
    """The Lean term `(WeilForm.weilForm (WeilForm.crossCorr g g')).re`."""
    o = other if other is not None else var
    return f"(WeilForm.weilForm (WeilForm.crossCorr {var} {o})).re"


def weil_form_prelude_lean() -> str:
    """The two abstract box lemmas plus the falsifiability atom, emitted ONCE per file.

    `box_pos` and `box_minor_pos` are pure real-arithmetic facts (no zeta content): given an
    enclosure box, the stated consequence follows.  Keeping them abstract puts every instance's
    load-bearing numerics inside `norm_num` side goals -- the corruptible, kernel-gated part.

    `weil_negative_refutes_rh` is the falsifiability face.  Its RH content sits ENTIRELY in the
    undischarged hypothesis `hpos` (the classical Weil direction RH => positivity); the emitted
    proof is `fun h => absurd (hpos h) (not_le.mpr hneg)`.  conjecture1_proved = False."""
    return (
        "/-- Enclosure box consequence: a box with a positive lower end forces positivity.  Pure\n"
        "real arithmetic -- the zeta content is entirely in what the caller instantiates. -/\n"
        "theorem box_pos {x lo hi : ℝ} (h : lo ≤ x ∧ x ≤ hi) (hlo : 0 < lo) : 0 < x :=\n"
        "  lt_of_lt_of_le hlo h.1\n"
        "\n"
        "/-- Sylvester from three enclosure boxes: if the two diagonal boxes sit strictly above\n"
        "zero and the worst-case determinant `lo_a * lo_b - max (c0^2) (c1^2)` is positive, then the\n"
        "2x2 symmetric block `!![a, c; c, b]` has both leading principal minors positive, hence is\n"
        "positive definite.  Pure real arithmetic. -/\n"
        "theorem box_minor_pos {a b c a0 a1 b0 b1 c0 c1 : ℝ}\n"
        "    (ha : a0 ≤ a ∧ a ≤ a1) (hb : b0 ≤ b ∧ b ≤ b1) (hc : c0 ≤ c ∧ c ≤ c1)\n"
        "    (ha0 : 0 < a0) (hb0 : 0 < b0)\n"
        "    (hdet : max (c0 * c0) (c1 * c1) < a0 * b0) :\n"
        "    0 < a ∧ 0 < a * b - c ^ 2 := by\n"
        "  obtain ⟨ha0', _⟩ := ha\n"
        "  obtain ⟨hb0', _⟩ := hb\n"
        "  obtain ⟨hc0', hc1'⟩ := hc\n"
        "  have hapos : 0 < a := lt_of_lt_of_le ha0 ha0'\n"
        "  have hbpos : 0 < b := lt_of_lt_of_le hb0 hb0'\n"
        "  have hab : a0 * b0 ≤ a * b :=\n"
        "    mul_le_mul ha0' hb0' (le_of_lt hb0) (le_of_lt hapos)\n"
        "  have hcsq : c ^ 2 ≤ max (c0 * c0) (c1 * c1) := by\n"
        "    rcases le_total 0 c with hcn | hcn\n"
        "    · have : c ^ 2 ≤ c1 * c1 := by nlinarith\n"
        "      exact this.trans (le_max_right _ _)\n"
        "    · have : c ^ 2 ≤ c0 * c0 := by nlinarith\n"
        "      exact this.trans (le_max_left _ _)\n"
        "  exact ⟨hapos, by linarith⟩\n"
        "\n"
        "/-- The falsifiability face of the Weil-form ladder.  A certified STRICTLY NEGATIVE\n"
        "autocorrelation pairing refutes RH -- through the explicit, UNDISCHARGED hypothesis\n"
        "`hpos`, the classical Weil direction (RH implies positivity of the form on\n"
        "autocorrelations), which is NEVER proved here.  Not expected to fire; emitted so the\n"
        "ladder is falsifiable rather than confirmation-only.  conjecture1_proved = False. -/\n"
        "theorem weil_negative_refutes_rh (g : ℝ → ℂ) (_hg : WeilExplicit.IsWeilTest g)\n"
        "    (hpos : RiemannHypothesis → 0 ≤ " + _wf("g") + ")\n"
        "    (hneg : " + _wf("g") + " < 0) : ¬ RiemannHypothesis :=\n"
        "  fun h => absurd (hpos h) (not_le.mpr hneg)\n"
    )


@dataclass
class WeilFormEnclosureEmitter(Emitter):
    """Emit the kernel CONSEQUENCE of an Arb enclosure of the E8 Weil pairing: positivity of a
    certified autocorrelation pairing, or positive-definiteness of a 2x2 Weil-Gram block.  The
    enclosure itself is the NAMED HYPOTHESIS (`henc`), never an assertion."""

    def __post_init__(self):
        self.kind = "weil_form_enclosure"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: WeilFormEnclosureCert = inst.payload  # type: ignore[assignment]
            if cert.shape == POSITIVITY:
                lines.append(self._emit_positivity(cert, inst.lean_name))
            else:
                lines.append(self._emit_gram_minor(cert, inst.lean_name))
            n_thm += 1
        return "\n".join(lines), n_thm

    # -- per-shape renderers (also the negative-control entry points) --------------------
    def _emit_positivity(self, cert: WeilFormEnclosureCert, nm: str) -> str:
        b = cert.boxes[0]
        lo, hi = rat_lean(sp.Rational(b.lo)), rat_lean(sp.Rational(b.hi))
        return (
            f"-- {nm}: the E8 Weil pairing of the autocorrelation of the test function "
            f"'{b.label_i}'\n"
            f"-- (smooth, compactly supported, support radius {cert.support_radius}) is "
            f"Arb-enclosed in\n"
            f"-- [{sp.Rational(b.lo)}, {sp.Rational(b.hi)}]; the kernel derives only the "
            f"consequence 0 < weilForm.\n"
            f"-- Arb seam: archimedean quadrature to |r| <= {cert.arch_T} with an "
            f"{cert.n_byparts}-fold integration-by-parts tail.\n"
            f"-- This is what RH PREDICTS for an autocorrelation (Weil positivity); observing it "
            f"confirms\n"
            f"-- NOTHING -- positivity over EVERY admissible test is RH-equivalent and no finite "
            f"family\n"
            f"-- approaches that.  See weil_negative_refutes_rh for the falsifiable direction.  "
            f"conjecture1_proved = False.\n"
            f"theorem {nm} (g : ℝ → ℂ) (_hg : WeilExplicit.IsWeilTest g)\n"
            f"    (henc : ({lo} : ℝ) ≤ {_wf('g')} ∧ {_wf('g')} ≤ {hi}) :\n"
            f"    0 < {_wf('g')} :=\n"
            f"  box_pos henc (by norm_num)\n"
        )

    def _emit_gram_minor(self, cert: WeilFormEnclosureCert, nm: str) -> str:
        a, b, c = cert.boxes
        alo, ahi = rat_lean(sp.Rational(a.lo)), rat_lean(sp.Rational(a.hi))
        blo, bhi = rat_lean(sp.Rational(b.lo)), rat_lean(sp.Rational(b.hi))
        clo, chi = rat_lean(sp.Rational(c.lo)), rat_lean(sp.Rational(c.hi))
        gi, gj = "g0", "g1"
        return (
            f"-- {nm}: the 2x2 Weil-Gram block of the test pair "
            f"('{a.label_i}', '{b.label_i}').  Each\n"
            f"-- cross-correlation pairing is Arb-enclosed; the kernel derives Sylvester's two "
            f"leading\n"
            f"-- principal minors, i.e. the block is POSITIVE DEFINITE.  Worst-case determinant "
            f"over the\n"
            f"-- boxes: {cert.margin} > 0.  Arb seam: |r| <= {cert.arch_T}, "
            f"{cert.n_byparts}-fold by-parts tail; widths <= {cert.max_width}.\n"
            f"-- Finite category-b: consistent with RH, PROVING NOTHING about it.  "
            f"conjecture1_proved = False.\n"
            f"theorem {nm} ({gi} {gj} : ℝ → ℂ)\n"
            f"    (_hg0 : WeilExplicit.IsWeilTest {gi}) (_hg1 : WeilExplicit.IsWeilTest {gj})\n"
            f"    (h00 : ({alo} : ℝ) ≤ {_wf(gi)} ∧ {_wf(gi)} ≤ {ahi})\n"
            f"    (h11 : ({blo} : ℝ) ≤ {_wf(gj)} ∧ {_wf(gj)} ≤ {bhi})\n"
            f"    (h01 : ({clo} : ℝ) ≤ {_wf(gi, gj)} ∧ {_wf(gi, gj)} ≤ {chi}) :\n"
            f"    0 < {_wf(gi)} ∧\n"
            f"      0 < {_wf(gi)} * {_wf(gj)} - {_wf(gi, gj)} ^ 2 :=\n"
            f"  box_minor_pos h00 h11 h01 (by norm_num) (by norm_num) (by norm_num)\n"
        )


def weil_form_enclosure_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Weil-form enclosure family (kind ``weil_form_enclosure``).
    ``spec: pt -> WeilFormEnclosureData``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("weil_form_enclosure", spec),
        constants=dict(constants or {}),
    )
