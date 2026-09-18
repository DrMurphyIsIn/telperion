"""Negative-control adapter for WeilFormEnclosureEmitter (the E8 Weil-pairing seam).

The `gram_minor` theorem states Sylvester's two leading principal minors for a 2x2 Weil-Gram
block, and delegates to the abstract `box_minor_pos`, whose two numeric side conditions are
discharged by `norm_num`:

    0 < a0            (the (i,i) box sits strictly above zero)
    max (c0*c0) (c1*c1) < a0 * b0   (the WORST-CASE determinant over the boxes is positive).

Those two goals are the emitter's entire load-bearing numeric content.  If the enclosures are
corrupted so that the worst-case determinant is NOT positive, `norm_num` fails and the TRUSTED
Lean kernel rejects the proof -- there is no route to the conclusion.

FALSE forgery: an off-diagonal box `[1/2, 6/10]` against diagonal boxes `[1/10, 1/5]`, so the
worst-case determinant is `1/100 - 36/100 = -35/100 < 0`.  (A forged off-diagonal enclosure
that EXCLUDES the true value has exactly this effect once it is inflated past the
Cauchy-Schwarz bound `|W_ij|^2 <= W_ii W_jj`, which is the concrete way "an enclosure that
excludes the true value" is caught downstream.)  Layer 1
(`weil_form_enclosure_certificate`) refuses a non-positive margin, so the adapter mints the
frozen dataclass BY HAND to bypass that guard and let the kernel be the arbiter.

TRUE twin: the REAL 2x2 block computed by `telperion.weil_form_eval` for the bump pair
(w = 1, w = 3/2) -- `W00 in [1.23957818512e-4, 1.26896128613e-4]`,
`W11 in [2.53407992378e-5, 2.62114096434e-5]`, `W01 in [4.58109961271e-5, 5.02184612773e-5]`,
worst-case determinant ~ +6.19e-10 -- a genuine positive-definite block, compiles clean.

Both twins need only the abstract `box_minor_pos` lemma and plain real arithmetic, so the
control elaborates against `import Mathlib` with the lemma supplied in the adapter prelude: it
tests the EMITTER's certificate arithmetic.  The zeta vocabulary (`WeilExplicit`, `WeilForm`)
is exercised separately by the CI job that compiles the dogfood island.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_weil_form_enclosure import (
    GRAM_MINOR,
    WeilBox,
    WeilFormEnclosureCert,
    WeilFormEnclosureEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_PRELUDE = (
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
    "namespace WeilExplicit\n"
    "def IsWeilTest (g : ℝ → ℂ) : Prop :=\n"
    "  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g\n"
    "end WeilExplicit\n"
    "\n"
    "namespace WeilForm\n"
    "/-- Stand-in for the dogfood island's `weilForm` (archSide - primeSide): the control tests\n"
    "    the emitter's certificate ARITHMETIC, so the pairing enters only as an opaque real.\n"
    "    The real definitions are CI-compiled in examples/weil_form_enclosure. -/\n"
    "noncomputable opaque weilForm : (ℝ → ℂ) → ℂ\n"
    "noncomputable opaque crossCorr : (ℝ → ℂ) → (ℝ → ℂ) → (ℝ → ℂ)\n"
    "end WeilForm\n"
)


def _box(i, j, lo, hi):
    return WeilBox(i=i, j=j, label_i=f"g{i}", label_j=f"g{j}",
                   lo=sp.Rational(lo), hi=sp.Rational(hi))


def make_false_cert():
    """Hand-forged FALSE cert: the off-diagonal box is inflated past Cauchy-Schwarz, so the
    worst-case determinant 1/100 - 36/100 is NEGATIVE (the certificate layer would refuse it)."""
    return WeilFormEnclosureCert(
        shape=GRAM_MINOR,
        boxes=(_box(0, 0, sp.Rational(1, 10), sp.Rational(1, 5)),
               _box(1, 1, sp.Rational(1, 10), sp.Rational(1, 5)),
               _box(0, 1, sp.Rational(1, 2), sp.Rational(3, 5))),
        max_width=sp.Rational(1),
        support_radius=sp.Rational(5, 2),
        arch_T=1024, n_byparts=5,
    )


def make_true_cert():
    """Paired TRUE twin: the real bump-pair Weil-Gram block (worst-case determinant ~ +6.19e-10)."""
    return WeilFormEnclosureCert(
        shape=GRAM_MINOR,
        boxes=(_box(0, 0, sp.Rational("0.000123957818512"), sp.Rational("0.000126896128613")),
               _box(1, 1, sp.Rational("0.0000253407992378"), sp.Rational("0.0000262114096434")),
               _box(0, 1, sp.Rational("0.0000458109961271"), sp.Rational("0.0000502184612773"))),
        max_width=sp.Rational(1, 100000),
        support_radius=sp.Rational(5, 2),
        arch_T=1024, n_byparts=5,
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        WeilFormEnclosureEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="WeilFormEnclosureEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=_PRELUDE,
        allow_axioms=(),
        label=(
            "forged Weil-Gram block whose off-diagonal box [1/2, 3/5] exceeds Cauchy-Schwarz "
            "against diagonals [1/10, 1/5]: the worst-case determinant max(c0^2,c1^2) < a0*b0 "
            "is FALSE (-35/100), norm_num fails and the kernel rejects; true twin (the real "
            "bump-pair block, worst-case determinant ~ +6.19e-10) compiles"
        ),
        imports_line="import Mathlib",
    )
)
