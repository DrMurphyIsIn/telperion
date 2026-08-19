# Telperion

**A general-purpose tool for proving families of mathematical statements in
Lean 4 — by exact-arithmetic certificate and kernel verification.**

You describe your problem as a parameterized *family* of statements; Telperion
certifies each instance in exact rational arithmetic, then emits Lean 4 that
Mathlib's kernel re-proves from scratch. The generator is untrusted by design —
a wrong certificate is a compile error, never a false theorem — so you get
machine-checked proofs without having to trust (or read) the tool that wrote
them.

It was forged as the engine behind a hard research proof (Brualdi–Goldwasser;
see [Origin](#origin)), where it produced 200+ CI-green Mathlib theorems. But
**nothing about the engine is specific to that problem** — the same pipeline
proves an unrelated textbook inequality
([`examples/bernoulli`](examples/bernoulli/)) through identical machinery.
Telperion is now a standalone, problem-agnostic artifact: bring your own
inequality, identity, or bound, and it will try to hand you a kernel-checked
Lean proof of it.

## What you can prove with it

Telperion turns a problem into Lean when you can express it as a *certifiable
family* — a grid of instances, each reducible to one of its certificate shapes.
That covers a large slice of concrete mathematics:

- **Rational-function inequalities** — `0 ≤ f(x̄)` or `g(x̄) ≤ h(x̄)` for
  rational `f,g,h` over nonnegative variables (Pólya positivity; box-corner
  reductions in two variables).
- **Polynomial nonnegativity** — `0 ≤ p(x̄)` via an exact rational
  sum-of-squares (reaches interior equality cases Pólya lifting cannot).
- **Exact identities and arithmetic** — integer/rational identities, powers,
  and closed-form equalities (`ring`/`norm_num` cores).
- **p-adic valuation facts** — `v_p(n) = k` as decidable divisibility.
- **Two-sided transcendental enclosures** — rigorous rational brackets
  `lo ≤ exp(−θ) ≤ hi` at a rational point.
- **Finite case analysis** — dispatch over a bounded parameter (`interval_cases`),
  subdivision of a region into cells and gluing the pieces back.
- **`∀ K ≥ K₀` tails** — a finite table plus one uniform certificate.
- **Assemblies of the above**, in the original variables (substitution glue,
  dichotomies, custom skeletons).

If your statement fits one of these shapes — or a product/quantifier over a grid
of them — Telperion will certify it in exact arithmetic and emit the Lean. If it
needs a new shape, you add an emitter (see [Extending it](#extending-it)); the
trust model and the whole pipeline come for free.

### Certificate shapes (v0.1.4)

Each shape is an *emitter*; all flow through the same `certify → validate →
emit → freeze` workflow.

| Emitter | Proves | Lean it writes |
|---|---|---|
| `DirectPolyaEmitter` | `0 ≤ f(x̄)`, `f` rational with an all-nonneg-numerator / positive-factored-denominator form | `f = num/den` by `field_simp`+`ring`, then `positivity` |
| `BilinearBoxEmitter` | `before ≤ after` on a box in two bound variables | bilinear decomposition + 4 Pólya corner certificates + assembly |
| `SOSEmitter` | `0 ≤ p` for a polynomial via an exact rational PSD-Gram sum-of-squares (reaches interior ties) | `p = Σ dᵢ·ℓᵢ² := by ring`, then `positivity` |
| `ExactFactEmitter` / `IdentityEmitter` | exact integer/rational identities and powers | `norm_num` / `ring` |
| `PadicValuationEmitter` | p-adic valuation facts `v_p(n)=k` | `(p^k ∣ n) ∧ ¬(p^{k+1} ∣ n)` by `norm_num` |
| `IntervalBracketEmitter` | rigorous two-sided rational enclosure `lo ≤ exp(−θ) ≤ hi` | Taylor bound + convexity companion |
| `CaseDispatchAssemblyEmitter` | finite case dispatch over a bounded parameter | `interval_cases` fan-out |
| `SubdivisionGlueEmitter` | reconstruct a subdivided region's theorem from its leaf cells | `le_total` case-split glue |
| `TailNatEmitter` | symbolic tails — finite table + one `∀ K ≥ K₀` certificate | ℕ-quantified, induction-free |
| `ReparamAdapterEmitter` | recast a real-variable certificate over `Nat.cast_sub` casts | cast-rewrite adapter |
| `VarMapAdapterEmitter` | substitution glue expressed in the original variables | `MapSpec`-driven rewrite |
| `DichotomyGlueEmitter` | classification over declared thresholds | `le_total` splits |
| `CustomAssemblyEmitter` | escape hatch for a hand-designed assembly | your skeleton |

The Pólya engine underneath (`polya_lift`: multiply through by `(1+Σxᵢ)^N`;
recursive box subdivision; SOS for the rationalizable subset) turns "true but
not obviously in Pólya form" into a certificate automatically, and `diagnose`
tells you which case you're in (see below).

## The trust model

**The generator is untrusted by design.** The Lean kernel is the sole trusted
component: a defective certificate manifests as a compile failure, never a false
theorem. The exact-arithmetic self-checks exist to catch mistakes *before* a CI
round-trip, not to establish truth. The design corollary is that the generator
stays small, readable, and dependency-light (sympy only) — a referee can audit
the engine (~a few thousand lines) instead of trusting it.

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
of every instance's expressions, the Lean profile, the templates, and the
emitters' own code — timestamps excluded), so `--check` / `diff_frozen()`
detects any drift byte-for-byte, and a change to emission logic can never ship
under a stale hash.

Before you burn a CI round-trip, `emit()` also runs two local gates: a
structural lint (unfilled holes, unbalanced delimiters, duplicate names) and a
**soundness lint** (`telperion lint-lean`) that refuses the "green build ≠
proved" classes — `sorry`/`admit`, smuggled `axiom`, empty `:= by`, missing
type ascription, `Prop := True` trivial stubs.

## Five-minute example

```python
import sympy as sp
from telperion import (GridSpec, InequalityFamily, LeanProfile,
                        DirectPolyaEmitter, ValidationReport, certify, emit)

u = sp.Symbol("u", nonnegative=True)
fam = InequalityFamily(
    name="Demo",
    symbols=(u,),
    grid=GridSpec([("a", [1, 2, 3])]),                       # one theorem per a
    lean_name=lambda pt: f"demo_a{pt['a']}",
    target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
)
res = emit(certify(fam), LeanProfile(namespace=("Demo",)),
           [DirectPolyaEmitter()], ValidationReport(checks=(("spot", True),)))
print(res.files["Demo.lean"])          # kernel-checkable Lean, one theorem per a
```

`telperion init myproof` scaffolds a complete new project — a family template, a
pinned Lean+Mathlib shell, a drift manifest, and a CI workflow — so you can go
from an idea to a CI-checked theorem without wiring any of it by hand. The
fully worked reference is [`examples/toy_box/`](examples/toy_box/) (compiled
against pinned Mathlib in this repo's CI); [`examples/bernoulli/`](examples/bernoulli/)
is the non-BG example, Bernoulli's inequality end-to-end through the core engine.

## Extending it

New kind of statement? Write an emitter. An `Emitter` is a small class that
turns a certified instance into Lean text; it inherits the entire pipeline —
enforcement, provenance hashing, drift net, soundness lint, byte-stability, all
three agent surfaces — for free. The existing thirteen emitters are the working
examples; `docs/TACTIC_CONTRACT.md` documents the exact Mathlib tactics the
default templates assume, and `docs/METHODOLOGY.md` the discipline.

## Honest scope — what it is and isn't

Telperion is a **certificate compiler, not an autoformalizer.** It proves what
reduces to certified inequalities, identities, valuations, brackets, and finite
case analysis — a broad and growing class, but not *every* Lean theorem. It will
not invent a structural induction or a clever lemma for you; it turns "I'm
confident this concrete inequality/identity/bound holds" into machine-checked
Lean, fast and byte-reproducibly. When a target is *outside* its shapes it says
so — `diagnose` triages any refusal into `FALSE` (with an exact rational
counterexample), `NOT_POLYA` (with remedy hints), or `CERTIFIABLE` — rather than
emitting a plausible-but-wrong proof. The project's discipline is to name what
it cannot do, not to paper over it.

## Search, when you don't know the certificate yet — `telperion.evolve`

An optional AlphaEvolve/OpenEvolve-style layer that *searches* for a certificate
when you can't write one by hand: it evolves candidate certificate genomes,
scored by the same exact `hunt → certify → parsimony → lake build` cascade, with
a hybrid mutator (a local open-source LLM proposes shapes; structured operators
refine). The trust model is unchanged — the loop only *proposes*; every survivor
still passes the identical kernel gate, and nothing is auto-frozen. It runs
LLM-free out of the box (structured search); the LLM arm is an opt-in extra.

## Using it from LLM agents

Three surfaces, all on the same enforced workflow:

- **CLI** — `telperion <verb>`: `init` (scaffold a project), `certify`, `probe`,
  `diagnose`, `verify` (regenerate + byte-diff the drift net), `lint-lean` (the
  soundness gate), plus analysis (`margins`, `ties`, `hunt`, `relax`, `sharpen`)
  and reporting (`latex`, `ledger`, `status`, `package`, `export-certs`,
  `recheck`). Every string-taking surface parses through a token whitelist —
  sympy's evaluating parser never sees raw input.
- **MCP server** — `pip install "telperion[mcp]"`, then
  `claude mcp add telperion -- telperion-mcp`. Tools mirror the workflow
  (`polya_probe`, `certify_family`, `emit_family`, `diff_family`,
  `read_manifest`); there is no path to Lean that skips certification.
- **Claude Code plugin / skill** — [`claude-plugin/`](claude-plugin/) bundles
  the MCP registration with a skill that teaches an agent the discipline (probe
  first, never hand-edit emitted files, never skip validation, compile in CI,
  diff on every change).

## Install

```bash
pip install -e "telperion"        # the engine — sympy only
pip install -e "telperion[dev]"   # + pytest, to run the tests
```

`sympy` is the only core dependency; `import telperion` and the whole
certify→emit pipeline need nothing else. Optional extras: `mcp` (agent server),
`sdp` (cvxpy, for the SOS emitter), `flint` (faster arithmetic). The
`telperion.evolve` search layer needs no extra — it is pure-stdlib, and its
optional LLM arm simply talks to a local [Ollama](https://ollama.com) server if
one is running. See [Origin](#origin) for the `bg` research-lab extra.

## Origin

Telperion was extracted clean-room from the Brualdi–Goldwasser (1984)
Laplacian-ratio proof campaign in [`../proof/`](../proof/), where the pattern
produced 200+ CI-green Mathlib theorems (a 36-cell bilinear certificate table,
36 dispatch adapters, 72 vee/mirror branches, 42 leg and 55 shedding
certificates — most batches first-try green). That campaign is still the tool's
largest stress test: its frozen families are re-certified and byte-diffed in CI,
the biggest also compiled against pinned Mathlib by the `telperion-production`
gate (e.g. `g1_floors`: 3,084 theorems). Those problem-specific research modules
live in the opt-in `telperion.bg` subpackage — `import telperion` loads **zero**
of them (statically and dynamically enforced by
[`tests/test_core_boundary.py`](tests/test_core_boundary.py)), keeping the
general engine small and auditable. Install the `bg` extra (networkx, numpy)
only if you want the research lab.

The methodology — untrusted generator, trusted kernel, numeric-first discipline,
provenance-and-drift — is written up in [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md).
