# Telperion

Certify families of rational-function inequalities in sympy, validate every
identity in exact arithmetic, and batch-emit kernel-checked Lean 4.

Extracted (clean-room) from the Brualdi–Goldwasser proof campaign in
[`../proof/`](../proof/), where this pipeline produced 200+ CI-green Mathlib
theorems (36-cell bilinear certificate table, 36 dispatch adapters, 72
vee/mirror branches, 42 leg and 55 shedding certificates — most batches
first-try green).

## The trust model

**The generator is untrusted by design.** The Lean kernel is the sole trusted
component: a defective certificate manifests as a compile failure, never a
false theorem. The sympy self-checks exist to catch errors *before* a CI
round-trip, not to establish truth. Corollary: the generator stays small,
readable, and dependency-light (sympy only) — a referee can audit ~1,500 lines
of Python instead of trusting them.

## The workflow (enforced, not advisory)

```
define -> certify() -> validate -> emit() -> lake build (your CI) -> freeze()
              |            |          |
   CertificationError   loud assert   refuses without BOTH the CertifiedFamily
   names every failing  failure       witness AND a green ValidationReport
   (cell, corner)
```

There is no API path from a family definition to Lean text that skips
certification, and `emit()` refuses a red validation report. Emitted files are
stamped with the tool version and a SHA-256 input hash (canonical serialization
of every instance's expressions, the Lean profile, and the templates —
timestamps excluded), so `generate.py --check` / `diff_frozen()` detects any
drift byte-for-byte.

## Five-minute example

```python
import sympy as sp
from telperion import (GridSpec, InequalityFamily, LeanProfile,
                         DirectPolyaEmitter, ValidationReport, certify, emit)

u = sp.Symbol("u", nonnegative=True)
fam = InequalityFamily(
    name="Demo",
    symbols=(u,),
    grid=GridSpec([("a", [1, 2, 3])]),
    lean_name=lambda pt: f"demo_a{pt['a']}",
    target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
)
res = emit(certify(fam), LeanProfile(namespace=("Demo",)),
           [DirectPolyaEmitter()], ValidationReport(checks=(("spot", True),)))
print(res.files["Demo.lean"])
```

The full worked example — a 4-cell bilinear box family whose emitted Lean is
compiled against pinned Mathlib in this repo's CI — is
[`examples/toy_box/`](examples/toy_box/): family definition, exact-rational
spot-check validation, generation script with `--check` drift mode, and the
Lean project shell.

## Certificate shapes (v0.1)

| Emitter | Proves | Lean shape |
|---|---|---|
| `DirectPolyaEmitter` | `0 ≤ f(x̄)` for a rational function with an all-nonneg-numerator / positive-factored-denominator form | `hkey : f = num/den` by `field_simp`+`ring`, then `positivity` |
| `BilinearBoxEmitter` | `before ≤ after` on a box in two bound variables | bilinear decomposition theorem + 4 Polya corner certificates + assembly via a user-supplied corner combinator |

Planned (the remaining shapes from the origin campaign): ℕ-reparameterization
adapters (`Nat.cast_sub` casts) and finite case-dispatch assemblies
(`interval_cases` fan-out).

The exact Mathlib tactics the default templates assume are documented in
[`docs/TACTIC_CONTRACT.md`](docs/TACTIC_CONTRACT.md); the discipline and its
rationale in [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md).

## The spelling rule that matters

`field_simp` matches `≠ 0` hypotheses syntactically. The tool therefore renders
**every denominator in positive-factored form** (`2 * (2 + u) * (2 + v)`, never
`8 + 4*u + ...`) and emits one `have hdN : factor ≠ 0 := by positivity` per
distinct factor. Term order is owned by the tool (graded-lex), not by sympy's
print order — emitted text is byte-stable across sympy versions, which the CI
matrix enforces.

## Install

```bash
pip install -e "telperion[dev]"   # from this repo; sympy is the only core dep
```
