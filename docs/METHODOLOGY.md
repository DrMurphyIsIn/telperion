# Methodology: untrusted generator, trusted kernel

The discipline behind Telperion. It is general — it governs how the tool proves
*any* certifiable family, not just the campaign it came from.

## 1. The trust model

Every theorem this tool emits is re-proved from first principles by the Lean
kernel against Mathlib. The generator therefore needs no verification: a bug in
sympy, in the certifier, or in the templates produces a file that **fails to
compile** — never a false theorem. The self-checks (decomposition identity,
all-nonneg numerators, positive-factored denominators) exist to catch errors in
seconds instead of a 20-minute CI round-trip.

Design corollary: keep the audit surface small. Pure Python + sympy, no
template engine, no CAS reimplementation in a compiled language. A referee
audits ~1,500 readable lines; the trust lands entirely on the kernel.

## 2. Numeric-first discipline

Nothing is formalized before it is validated in **exact** arithmetic
(`fractions.Fraction` / `sympy.Rational` — floats never touch a certificate
path). The workflow object enforces this: `emit()` requires a green
`ValidationReport` alongside the certification witness. In the origin campaign
this discipline is why most generated batches compiled first-try: formalization
effort was only ever spent on statements already known true, and every Lean
failure was a *spelling* problem, not a *truth* problem.

## 3. Certificate shapes

Each provable class is an *emitter* — a small, single-purpose translator from a
certified instance to Lean. The two foundational ones:

- **Pólya nonnegativity**: `0 ≤ f` shown by exhibiting `f = num/den` with `num`
  an all-nonnegative-integer-coefficient polynomial and `den` a product of
  positive-coefficient factors. `positivity` closes both.
- **Bilinear box**: `before ≤ after` on a rectangle, reduced to the four
  corners (a bilinear form's extrema on a box are at corners); each corner is a
  Pólya certificate; a ~20-line combinator lemma assembles them.

The current set (sum-of-squares, p-adic valuation, transcendental interval
brackets, `interval_cases` dispatch, subdivision glue, `∀K≥K₀` tails,
reparameterization and substitution adapters, custom assemblies) is tabulated in
the [README](../README.md#certificate-shapes-v014); adding a new class is
writing one more `Emitter`.

What the shapes cannot express is **named, not absorbed**: a target outside them
is *refused* at certification (with an exact counterexample or a remedy hint via
`diagnose`), never emitted as a plausible-but-wrong proof. This is the same
honesty rule that keeps `conjecture1_proved = False` where a proof is not yet
complete — the tool states what it cannot do rather than paper over it.

## 4. Provenance and the reviewer's protocol

Every emitted file carries the tool version and a SHA-256 hash of its complete
input (canonical `srepr` of every instance, profile, templates; timestamps
excluded — identical inputs give identical bytes). A reviewer runs three
independent one-command checks:

1. `python examples/<family>/generate.py --check` — regenerate and byte-diff
   (drift in the family, tool, or hand-edits is flagged);
2. the family's exact-numeric validation harness — every claim an assert;
3. `lake build` — the actual verification.

## 5. Origin, and why it is now general

Extracted clean-room from the Brualdi–Goldwasser (1984) Laplacian-ratio campaign
(`../proof/` in this repository), where the pattern produced 200+ CI-green
Mathlib theorems across five certificate families. That campaign hardened the
tool but did not shape it: nothing in the engine is problem-specific (the BG
research modules are quarantined in the opt-in `telperion.bg` subpackage, which
the engine never imports), and `examples/bernoulli` proves an unrelated textbook
inequality through the identical pipeline. Telperion is a general-purpose
certificate compiler; the BG campaign is simply its largest, permanently
CI-checked witness.
