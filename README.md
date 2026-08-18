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

## Certificate shapes (v0.1.3)

Every shape that produced a theorem in the origin campaign now ships as an
emitter. All lower onto the same certify→validate→emit→freeze workflow.

| Emitter | Proves | Lean shape |
|---|---|---|
| `DirectPolyaEmitter` | `0 ≤ f(x̄)` for a rational function with an all-nonneg-numerator / positive-factored-denominator form | `hkey : f = num/den` by `field_simp`+`ring`, then `positivity` |
| `BilinearBoxEmitter` | `before ≤ after` on a box in two bound variables | bilinear decomposition theorem + 4 Pólya corner certificates + assembly via a user-supplied corner combinator |
| `ExactFactEmitter` / `IdentityEmitter` | exact integer/rational identities and powers (`fact_pow`) — the arithmetic cores (tie, asymptote, gate) | `norm_num` / `ring` |
| `ReparamAdapterEmitter` | ℕ-reparameterization — recast a real-variable certificate over `Nat.cast_sub` casts | cast-rewrite adapter over a Pólya body |
| `CaseDispatchAssemblyEmitter` | finite case dispatch — assemble per-cell certificates into one theorem | `interval_cases` fan-out |
| `SubdivisionGlueEmitter` | reconstruct a subdivided cell theorem from its leaf cells | `le_total` case-split glue |
| `VarMapAdapterEmitter` | substitution glue expressed in the original variables (the campaign's most-used maneuver) | `MapSpec`-driven rewrite |
| `DichotomyGlueEmitter` | classification (not surgery) over declared thresholds | `le_total` splits |
| `TailNatEmitter` | symbolic tails — a finite table plus one `∀ K ≥ K₀` certificate | ℕ-quantified induction-free tail |
| `CustomAssemblyEmitter` | escape hatch for hand-designed assemblies | user-supplied skeleton |
| `SOSEmitter` | `0 ≤ p` for a polynomial via an exact rational PSD-Gram SOS — reaches INTERIOR ties Pólya lifting cannot, and reads the tight variety off the SDP dual | `hsos : p = Σ dᵢ·(ℓᵢ)² := by ring`, then `positivity` |
| `IntervalBracketEmitter` | rigorous rational two-sided enclosure `lo ≤ exp(-θ) ≤ hi` at a rational point θ | Taylor lower bound (`Real.sum_le_exp_of_nonneg`) + convexity companion (`Real.add_one_le_exp`) |
| `PadicValuationEmitter` | p-adic valuation facts `v_p(n)=k` as decidable divisibility | `(p^k ∣ n) ∧ ¬(p^{k+1} ∣ n)` by `norm_num` |

The last three are the Tier-1 first-class emitters (2026-08-18): each promotes a
former one-off demonstrator to a pipeline-enforced `family.kind` + emitter +
convenience constructor, with honesty pins (the SOS emitter cross-checks declared
interior ties against the SDP dual's tight variety). Honest scope: `SOSEmitter`
is the certificate LAYER for the occupancy / SOS-for-trees method — aiming its
dual at the recursive matching functional's integer tie is the named research
program, not shipped; `IntervalBracketEmitter` enclosures do not close the g1
`Real.log` bridge; `PadicValuationEmitter` ships the 23-adic primitives, not the
crux. `conjecture1_proved=False`.

Still open (tracked in [`CHANGELOG.md`](CHANGELOG.md), deliberately not shipped
as stubs): `func="log"` interval brackets (no CI-verified Mathlib chain yet);
Kind-3 multi-axis grids; a generic Lean lemma for unimodal integer maxima;
generic induction emission for telescoping potentials.

The exact Mathlib tactics the default templates assume are documented in
[`docs/TACTIC_CONTRACT.md`](docs/TACTIC_CONTRACT.md); the discipline and its
rationale in [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md).

## Proven in anger: the production families

Telperion is not a toy — it carries the Brualdi–Goldwasser campaign's Lean.
Frozen families, re-certified and byte-diffed in CI, with the largest also
compiled against pinned Mathlib by the `telperion-production` gate:

| Family | Scale | Gate |
|---|---|---|
| `examples/toy_box` | 4-cell worked example (+ lift, split variants) | `telperion-lean-e2e` (regen → `lake build`) |
| `examples/r47_cells` | R47 36-cell table, 216 theorems | `telperion-casestudy` (re-cert + diff) |
| `examples/g1_floors` | 3084 bracket-quantified floor theorems (514 bisection leaves) | `telperion-production` (`lake build`) |
| `examples/r7_starofhubs` | R7 star-of-hubs, 972 witness-searched certs | `telperion-audit` |
| `examples/g34_twohub` | two-hub, 4656 theorems | `telperion-audit` |
| shed / legs / interp / h_floors | 55 / 48 / 215 / 382 theorems | `telperion-production` |

## The spelling rule that matters

`field_simp` matches `≠ 0` hypotheses syntactically. The tool therefore renders
**every denominator in positive-factored form** (`2 * (2 + u) * (2 + v)`, never
`8 + 4*u + ...`) and emits one `have hdN : factor ≠ 0 := by positivity` per
distinct factor. Term order is owned by the tool (graded-lex), not by sympy's
print order — emitted text is byte-stable across sympy versions, which the CI
matrix enforces.

## Using Telperion from LLM agents

Three surfaces, layered on the same enforced workflow:

- **CLI** — `telperion <verb>` (families addressed as
  `path/to/family.py:factory`). Scaffolding: `init` builds a complete new proof
  project (family template, pinned Lean shell, drift manifest, CI workflow).
  Pipeline: `certify`, `probe`, `diagnose` (triages any refusal into FALSE with
  an exact rational counterexample / NOT_POLYA with remedy hints / CERTIFIABLE).
  Emission is guarded by the `emit()` API and per-project generate scripts, never
  a validation-skipping CLI path; `verify` regenerates and byte-diffs the frozen
  artifacts (the project drift net, run by group: `quick`/`heavy`/`audit`).
  Analysis: `margins`, `ties`, `hunt`, `relax`, `sharpen`. Reporting:
  `latex`, `ledger`, `status`, `cilog`, `review-brief`, `package`,
  `export-certs`; cross-check with the stdlib `recheck`. All string-taking
  surfaces parse through a token whitelist — sympy's evaluating parser never
  sees raw input.
- **MCP server** — `pip install "telperion[mcp]"`, then register in Claude
  Code with `claude mcp add telperion -- telperion-mcp`. Tools: `polya_probe`,
  `certify_family`, `emit_family`, `diff_family`, `read_manifest`; resources:
  `telperion://tactic-contract`, `telperion://methodology`. The tool set
  mirrors the workflow — there is no path to emitted Lean that skips
  certification or validation. The server imports the family modules you name:
  point it only at trusted project files.
- **Claude Code plugin / skill** — [`claude-plugin/`](claude-plugin/) bundles
  the MCP server registration with a skill that teaches an agent the
  discipline (probe first, never hand-edit emitted files, never skip
  validation, compile in CI, diff on every change). To use the skill alone,
  copy `claude-plugin/skills/telperion/` into `~/.claude/skills/`.

## Install

```bash
pip install -e "telperion[dev]"   # from this repo; pulls sympy + pytest + networkx
```

`sympy` is the only **core** dependency — `import telperion` and the whole
certify→emit pipeline need nothing else. The Brualdi–Goldwasser graph-certificate
modules additionally use `networkx` (imported lazily, so they never burden the
core); install the `graph` extra for those, or `dev` (which includes it) to run
the tests. `mcp` and `flint` are further optional extras.
