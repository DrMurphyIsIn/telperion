# Design: Analytic Certificate Structures for Telperion (5 components)

**Date:** 2026-09-05
**Status:** Design (pre-plan)
**Branch:** `telperion/analytic-cert-structures` (worktree `/Users/peterwmurphy/telperion-analytic`, off `origin/main`)
**Honesty flag:** `conjecture1_proved = False` on every artifact.

---

## 1. Motivation

The Jensen-Pólya hyperbolicity work (PR #227) surfaced five reusable certificate
*structures* that Telperion does not yet have as first-class capabilities. Building
them serves the standing order to accumulate reusable Telperion capabilities, and the
BG<->RH cross-pollination mandate: the Arb enclosure front-end and the box-robust
kernel shape are exactly the missing pieces across *both* the RH endgame (transcendental
brackets) and the BG endgame (e^2 / sqrt(2) / 621-64 rational-analytic cruxes).

Telperion today is purely algebraic/rational: `emit_bracket.py` handles only rational
Taylor enclosures of `exp`, and `emit_interlacing.py` checks real-rootedness in sympy
but never emits it as a kernel theorem. These five components add a rigorous *analytic*
front-end and the kernel shapes to consume it.

## 2. The five components as a stack

```
FOUNDATION
  #1 Arb enclosure provider  ── certified rational box for a transcendental constant
       (non-kernel INPUT: Lean cannot know a constant's value)         │
                                                                        ▼ boxes
  #2 box-robust kernel emitter ── "∀ c in rational box, P(c) ≥ 0"  (kernel theorem)
                                                                        │
APPLICATIONS (built on #2)                                              ▼
  #3 hyperbolicity emitter ── "poly.roots.card = degree" via discriminant bridge
  #5 turan-box emitter ────── 3-term log-concavity a_mid^2 ≥ a_lo·a_hi (convenience over #2)

ORTHOGONAL
  #4 statement-match gate ── kernel-enforced `example : <type> := thm`, a mixin for any emitter
```

All five follow the established first-class-emitter pattern (certificate dataclass +
exact self-check/refusal + `emit_body` + `<kind>_family` + registration in `certify.py`
`_SPECIAL_KINDS`/`_SPECIAL_DISPATCH` + `__init__` export + a `examples/<kind>/` dir with
`generate.py --check` freeze/diff + kernel-verified Lean + a CI job).

## 3. Scope (per approved decision: "reusable shapes + demos")

**In scope:** the reusable emitter/provider shapes, each demonstrated and kernel-verified.
**Documented extensions (NOT built now):**
- The general Hermite-Bezoutian signature => real-root-count theorem (all d ≤ 8). Research-grade; the natural successor to #3.
- **#3 at degree ≥ 3.** The cubic `Δ ≥ 0 ⟹ all roots real` bridge is the same
  research-hard formalization deferred in Jensen Phase 2 (Mathlib's `CubicDiscriminant`
  gives distinctness over the splitting field, not realness over ℝ). #3 ships the
  **degree-generic emitter + the d=2 bridge**; d=3 is a clean drop-in (add one prelude
  lemma) but is an extension, not a blocker.
- #1 supports the constants demonstrated (π, e, a ζ value, a Γ value) + any
  acb-evaluable expression; it is not a catalogue of every special function.

## 4. Component designs

### #1 — Arb enclosure provider  (`src/telperion/arb_enclosure.py`)

Not a kernel-theorem emitter — Lean cannot prove `lo ≤ ζ(½) ≤ hi`. It is a **certified
rational-box provider**; the box *membership* is the documented non-kernel input (exactly
the Jensen coefficient boundary).

- `enclose_constant(spec: ConstantSpec, prec_bits: int) -> tuple[Fraction, Fraction]` —
  builds the value as a python-flint `acb`/`acb_series`, extracts the real part's arb ball,
  returns exact outward-rounded `mid ± rad` rationals guaranteed to contain the true value.
- `ConstantSpec` — a small evaluable description: `pi`, `e`, `zeta(s)`, `gamma(s)`, or a
  callable `acb_ctx -> acb`. (Reuses the exact `arb.man_exp()` dyadic extraction from the
  Jensen `coefficients.py`, lifted here as the general primitive.)
- Provenance: `EnclosureRecord(spec, prec_bits, lo, hi, radius)` — serialized to a
  `witnesses.json` so a box's origin is auditable (this record IS the non-kernel-input
  disclosure).
- Refusal / guard: raises if python-flint is unavailable; the returned interval must
  contain the value (verified in tests against an mpmath oracle).
- **Trust boundary:** documented in the module docstring and every consuming example —
  Arb ball arithmetic is certified, but membership is Python-side, not kernel.

### #2 — box-robust kernel emitter  (`kind = "box_robust"`, `src/telperion/emit_box_robust.py`)

Emits `∀ c_0..c_n : ℝ, (lo_0 ≤ c_0 → c_0 ≤ hi_0 → …) → 0 ≤ P(c)` for a **separable
quadratic** target `P` — a sum of `± square(affine)` and `± (bilinear product)` terms
(the class the corner-product + `sq_nonneg` `nlinarith` method proves; it covers the
discriminant and Turán targets). General polynomial-box-minimization is out of scope.

- `BoxRobustPayload(box: tuple[(Fraction,Fraction),...], target: sp.Poly, margin: sp.Rational, corner_terms, square_terms)`.
- `certify_box_robust_point(family, pt, name)` — computes a rigorous rational lower bound
  of `P` over the box via interval evaluation (corner products for bilinear terms, endpoint-
  nearest for squares, exactly as `disc2_margin`); refuses (`ValueError`) if `margin < 0`.
- `emit_body` — renders the ∀-theorem; proof = `nlinarith` seeded with the four corner
  `mul_nonneg` products, the `sq_nonneg` affine terms, and the concrete `margin ≥ 0`
  `norm_num` fact.
- `box_robust_family(name, symbols, grid, lean_name, spec)` where `spec(pt) -> (box, target_expr)`.

### #3 — hyperbolicity emitter  (`kind = "hyperbolicity"`, `src/telperion/emit_hyperbolicity.py`)

Emits `(C a_d * X^d + … + C a_0).roots.card = d` (real-rootedness) by chaining a
`#2` box-robust discriminant-nonneg fact into a per-degree bridge lemma.

- Prelude Lean lemma (this project owns it, generalized from Jensen):
  `hyperbolic_deg2_of_discrim_nonneg (a b c : ℝ) (ha : a ≠ 0) (h : 0 ≤ b^2 - 4*a*c) : (C a*X^2 + C b*X + C c).roots.card = 2`.
- `HyperbolicityPayload(coeff_box, degree, discrim_margin, leading_sign)`.
- `certify_hyperbolicity_point` — refuses if the discriminant margin ≤ 0 or the leading-
  coefficient box straddles 0 (can't prove `a ≠ 0`). Degree-generic; currently supports d=2.
- `emit_body` — emits the box-hyperbolicity wrapper (leading-coeff `≠ 0` from box sign +
  box-robust discriminant `≥ 0` + bridge). Structured to dispatch per degree so d=3 is a
  drop-in once the cubic bridge lemma exists.
- Demonstrated on TWO families (a generic real-rooted quadratic family + a second one) to
  prove it is not ζ-specific.

### #4 — statement-match gate  (`src/telperion/statement_match.py`, wired into `workflow.Emitter`)

A reusable feature: alongside a theorem `T` with claimed type `τ`, emit
`example : τ := T`. If the emitted statement of `T` is not defeq to `τ`, the build fails —
statement-match becomes kernel-enforced (the AXLE signature-gate lesson).

- `statement_match_example(theorem_name: str, explicit_type: str) -> str`.
- Opt-in on the base `Emitter`: a flag / method `emit_gate(name, type_str)` emitters call.
- Negative control: an emitter whose theorem type is deliberately altered fails to build.
- Wired into #2 and #3 (every box/hyperbolicity theorem carries its gate).

### #5 — turan-box emitter  (`kind = "turan_box"`, thin convenience over #2)

3-term log-concavity `a_{mid}^2 ≥ a_{lo}·a_{hi}` for interval-enclosed sequence values —
a specialization of #2 with `target = a1^2 - a0*a2`. Named `turan_box` to avoid colliding
with the existing `logconcave` kind (single-point). Ships as a `turan_box_family`
convenience constructor delegating to the #2 certifier/emitter; minimal new code.

## 5. Data flow (end to end)

```
transcendental constant/sequence value
   │  #1 arb_enclosure.enclose_constant
   ▼
certified rational box  ── + EnclosureRecord (non-kernel-input provenance)
   │  #3 / #5 spec(pt) builds target (discriminant / Turán) over the box
   ▼
#2 certify_*_point → margin ≥ 0 (refuse otherwise)
   │
   ▼
emit_body → Lean ∀-theorem (+ #4 statement-match example) → freeze/diff
   │
   ▼
lake build (kernel) → sorry-free, axioms {propext, Classical.choice, Quot.sound}
```

## 6. Testing

- **#1:** interval contains an mpmath oracle value across constants; width shrinks with
  precision; outward-rounding (exact `Fraction`) verified; python-flint-absent guard.
- **#2/#3/#5:** exact self-check refusals (negative controls: margin < 0 refused; straddling
  leading coeff refused; a non-log-concave triple refused); `generate.py --check`
  freeze/diff byte-match; **kernel `lake build`** green sorry-free with clean axioms;
  statement-match example compiles (and a drifted type fails).
- **#4:** a deliberately-mis-typed gate fails to build (kernel-level negative control).
- **CI:** one `*-compiles` job per example in `telperion-lean-e2e.yml` (`pip install`
  incl. `python-flint mpmath`; `generate.py --check`; `lake exe cache get`; `lake build`).
- **SoC-safe Lean:** always `lake exe cache get` before `lake build`; never a from-scratch
  Mathlib compile locally.

## 7. Location & coordination

Built off `origin/main` in an isolated worktree to avoid colliding with the active
parallel emitter work (which merges emitters to `main`). New emitters are additive
new files + small additions to `certify.py`/`__init__.py`; land via PR against `main`.
All Lean examples are isolated `lean_lib` targets with their own lakefile/toolchain,
matching the existing example convention.

## 8. Out of scope

- The general Hermite-Bezoutian real-root-count engine (successor to #3).
- #3 at degree ≥ 3 (cubic/quartic bridges — Mathlib gap; extension).
- #1 as an exhaustive special-function catalogue.
- Any claim toward proving RH or BG. `conjecture1_proved = False`.
