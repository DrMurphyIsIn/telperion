# Analytic Cert Structures

**Branch:** `telperion/analytic-cert-structures`
**Status:** Five capabilities shipped (Tasks 1–5). conjecture1_proved = False.

---

## Five Capabilities

### #1 — Arb Transcendental-Constant Enclosure Provider

**Module:** `src/telperion/arb_enclosure.py`
**Entry point:** `enclose_constant(spec, prec_bits) -> tuple[Fraction, Fraction]`

Wraps python-flint / Arb ball arithmetic to produce a rigorous outward-rounded
rational enclosure `(lo, hi)` (exact `Fraction` endpoints, no float arithmetic)
for a transcendental constant. Supported specs: `"pi"`, `"e"`, `"zeta(q)"`,
`"gamma(q)"`, or a callable that returns an `acb`. Companion `EnclosureRecord`
dataclass serialises the enclosure with provenance metadata.

**NON-KERNEL-INPUT trust boundary (critical):**
The Arb ball arithmetic is certified by the python-flint / Arb library — its
interval arithmetic is rigorous by construction — but **Lean does NOT verify
the numerical value** of the constant. The enclosure `(lo, hi)` feeds downstream
emitters (e.g. `box_robust`) as a plain `Fraction` pair. Lean's nlinarith kernel
then verifies the *algebraic consequence* assuming those bounds hold; it does not
independently confirm that `lo ≤ pi ≤ hi`. The trust chain is therefore:
`Arb (trusted external oracle)` → `Fraction enclosure` → `Lean kernel (verified)`.
This is the system's sole non-kernel-input trust boundary. It is not an exhaustive
special-function catalogue; other transcendentals require new `enclose_constant`
spec entries.

**Dependencies:** `python-flint`, `mpmath` (fallback radius estimation).

---

### #2 — Box-Robust Emitter

**Module:** `src/telperion/emit_box_robust.py`
**Family constructor:** `box_robust_family(...)`
**Emitter class:** `BoxRobustEmitter`

Certifies and emits a Lean theorem of the form:

```
theorem <name> : forall v0 ... vn : R,
    lo0 <= v0 -> v0 <= hi0 -> ... -> (0:R) <= target := by
  intro ...; nlinarith [sq_nonneg ..., mul_nonneg ...]
```

for a **separable-quadratic** target (pure squares, bilinear cross-terms, linear
terms, constants) over a rational box. Certification is via `box_min_lower_bound`:
a monomial-wise exact rational lower bound computed sign-aware over the box corners.
Non-separable monomials (degree > 2, or `vi^2 * vj`) raise `CertificationError`
(honest refusal, not silent miscertification). Margin gate: if the computed lower
bound is ≤ 0 the family is refused.

**Example:** `examples/box_robust/lean/BoxRobust.lean` — axiom-clean
(`propext, Classical.choice, Quot.sound`), no `sorryAx`.

**CI job:** `box-robust-compiles`

---

### #3 — Hyperbolicity Emitter (d = 2)

**Module:** `src/telperion/emit_hyperbolicity.py`
**Family constructor:** `hyperbolicity_family(...)`
**Emitter class:** `HyperbolicityEmitter`

For every quadratic polynomial `a*X^2 + b*X + c` whose coefficients `(a, b, c)`
lie in a rational box, certifies and emits a Lean theorem that
`polynomial.roots.card = 2` (the polynomial has exactly 2 real roots counted with
multiplicity). The proof chain:

1. `box_min_lower_bound` certifies that `b^2 - 4*a*c >= margin > 0` over the box
   (discriminant nonnegativity, via #2).
2. A leading-coefficient sign bound certifies `a != 0` over the box.
3. The Lean bridge lemma `HyperbolicityBridge.hyperbolic_deg2_of_discrim_nonneg`
   (proven fresh in this project, sorry-free) applies these two facts to conclude
   `roots.card = 2`.

**Lean bridge lemma** (`examples/hyperbolicity/lean/HyperbolicityBridge.lean`):

```lean
theorem hyperbolic_deg2_of_discrim_nonneg (a b c : R) (ha : a != 0)
    (h : 0 <= b ^ 2 - 4 * a * c) :
    (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X
      + Polynomial.C c).roots.card = 2
```

This bridge lemma is proven via explicit root construction in `R[X]` (Vieta form),
`Polynomial.roots_C_mul_X_sub_C`, and `Finset.card_insert_of_not_mem`. It is
sorry-free and axiom-clean.

**Deferred extension — degree >= 3:** Mathlib currently lacks the
discriminant-to-real-roots bridges for cubics and quartics (degree 3 and 4). A
general Hermite–Bezoutian real-root engine (expressing `roots.card` from
signed subresultant sequences) is the correct foundation but is not yet
implemented. Hyperbolicity at degree >= 3 is therefore deferred until those
Mathlib bridges exist.

**CI job:** `hyperbolicity-compiles`

---

### #4 — Statement-Match Gate

**Module:** `src/telperion/statement_match.py` (function `statement_match_example`)
**Workflow wiring:** `src/telperion/workflow.py` (`Emitter.emit_gate`)

Emits an `example` line that ascribes the generated theorem's type back to itself:

```lean
example : <explicit_type> := <theorem_name>
```

The type ascription must be definitionally equal to the theorem's type or the Lean
kernel rejects the build. This makes statement drift (e.g. a regeneration that
silently changes the quantifier or bound direction) a **compile error** rather than
a silent divergence. The gate type string is single-sourced from the same
`thm_type` variable used in the theorem declaration, so there is no separate
re-derivation path where the gate could diverge.

**Wired into:** `BoxRobustEmitter.emit_body` (Tasks 3 and 2), and inherited by
`TuranBoxEmitter` (Task 5) via delegation to `box_robust_family`.

**Opt-in field:** `Emitter.emit_statement_gate: bool = True` (default on; set
False only for emitters whose type strings are not stable single-line expressions).

---

### #5 — Turan-Box Log-Concavity Emitter

**Module:** `src/telperion/emit_turan_box.py`
**Family constructor:** `turan_box_family(a0_box, a1_box, a2_box)`

Certifies and emits a Lean theorem of the form:

```
theorem turan_triple_<a0>_<a1>_<a2> : forall a0 a1 a2 : R,
    lo0 <= a0 -> a0 <= hi0 -> ... -> (0:R) <= a1 ^ 2 - a0 * a2 := by
  intro ...; nlinarith [sq_nonneg ..., mul_nonneg ...]
```

witnessing that `a1^2 - a0*a2 > 0` over the given rational box — i.e. the Turan
triple `(a0, a1, a2)` is **strictly log-concave** over that box.

**Design (delegation):** `turan_box_family` returns a genuine `box_robust`-kind
family with `special = ("box_robust", inner_spec)`. No new emitter class, no new
dispatch entry. All certification, refusal gate (margin ≤ 0 → `CertificationError`),
emission, and statement-match gate logic flow through the existing #2 path end to
end. The inner spec normalises box endpoints to `Fraction` (via `sp.Rational`
round-trip) and fixes the sympy target `a1**2 - a0*a2`.

**CI job:** `turan-box-compiles`

---

## Trust Boundary Summary

| Layer | Who verifies | What is trusted externally |
|---|---|---|
| Arb ball arithmetic (#1) | python-flint / Arb library | Numerical value of constants (pi, e, zeta, gamma) |
| Box-min lower bound (#2) | Python exact `Fraction` arithmetic | Nothing beyond basic Python int/Fraction correctness |
| Lean nlinarith kernel (#2, #3, #5) | Lean 4 kernel | Nothing (kernel is the root of trust) |
| HyperbolicityBridge (#3) | Lean 4 kernel | Nothing (proven fresh, no sorry) |
| Statement-match gate (#4) | Lean 4 kernel | Nothing (type ascription is kernel-checked) |

The sole non-kernel-input trust boundary is the Arb enclosure provider (#1).
Everything else reduces to the Lean 4 kernel.

---

## Deferred Extensions

- **General Hermite–Bezoutian real-root engine:** For certifying `roots.card = d`
  for degree `d >= 3`. Requires Mathlib bridges for cubic/quartic discriminant
  → real-roots; not yet available.
- **Hyperbolicity at degree >= 3:** Blocked on the above.
- **Exhaustive special-function catalogue for #1:** `enclose_constant` covers
  `pi`, `e`, `zeta(q)`, `gamma(q)`, and callables. Other transcendentals require
  new spec entries; there is no claim of completeness.
- **Multi-polynomial log-concavity:** `turan_box` handles a single triple; a grid
  emitter sweeping parameter families is a natural extension.

---

conjecture1_proved = False.
