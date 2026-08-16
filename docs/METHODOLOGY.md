# Methodology: untrusted generator, trusted kernel

*(v0.1 — the core argument; expands with the reparameterization/assembly
emitters in the next milestone.)*

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

- **Polya nonnegativity**: `0 ≤ f` shown by exhibiting `f = num/den` with `num`
  an all-nonnegative-integer-coefficient polynomial and `den` a product of
  positive-coefficient factors. `positivity` closes both.
- **Bilinear box**: `before ≤ after` on a rectangle, reduced to the four
  corners (a bilinear form's extrema on a box are at corners); each corner is a
  Polya certificate; a ~20-line combinator lemma assembles them.
- *(next milestone)* ℕ-reparameterization adapters and finite case-dispatch
  assemblies.

What the shapes cannot express is named, not absorbed: transcendental bounds
(log/exp interval brackets) stay on the Python validation side; genuinely
non-Polya inequalities (negative numerator coefficients that no clearing
removes) are refused at certification.

## 4. Provenance and the reviewer's protocol

Every emitted file carries the tool version and a SHA-256 hash of its complete
input (canonical `srepr` of every instance, profile, templates; timestamps
excluded — identical inputs give identical bytes). A reviewer runs three
independent one-command checks:

1. `python examples/<family>/generate.py --check` — regenerate and byte-diff
   (drift in the family, tool, or hand-edits is flagged);
2. the family's exact-numeric validation harness — every claim an assert;
3. `lake build` — the actual verification.

## 5. Origin

Extracted from the Brualdi–Goldwasser (1984) Laplacian-ratio campaign
(`../proof/` in this repository), where the pattern produced 200+ CI-green
Mathlib theorems across five certificate families. The proof repo ships its
original problem-specific generator frozen for provenance; this tool is the
clean-room generalization, with the toy example as its compiled-in-CI witness.
