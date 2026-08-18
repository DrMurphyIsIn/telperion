# Telperion Evolve — LLM-driven evolutionary certificate search

**Status:** design approved 2026-08-18. Implementation not started.
**Author:** brainstormed with Claude (Opus 4.8).
**Prototype evidence:** `prototypes/openevolve_probe.py` — a throwaway spike that proved
the `hunt → certify → emit → lake build` cascade works as a non-gameable fitness function
and that a GA over certificate *programs* discovers a kernel-green certificate the naive
shape misses. This spec graduates that probe into a reusable subsystem.

---

## 1. Problem & motivation

Telperion is a deterministic certificate compiler: a human defines an inequality/identity
*family*, `certify()` checks it in exact arithmetic, `emit()` renders Lean 4, and the Lean
**kernel is the sole trusted verifier**. The *front-end* — deciding which family/emitter/
certificate shape to try, where to subdivide, which SOS basis or Pólya multiplier to use —
is entirely human.

AlphaEvolve/OpenEvolve automate exactly that front-end: evolve programs against an automatic
evaluator. Telperion is an unusually good substrate because the hard part (a non-gameable
evaluator) *is already built and is its whole design philosophy*. The spike confirmed this
end to end.

This subsystem adds the missing loop: search over **certificate programs**, scored by the
existing exact-arithmetic + kernel cascade, mutated by a **hybrid LLM + structured** operator.

### First hard target: the generic unimodal-integer-max emitter

Telperion's README lists "a generic Lean lemma for unimodal integer maxima" as an *open,
deliberately-unshipped* shape. Many BG sub-lemmas need: *a function `f(k)` over integer
`k ≥ 0` is unimodal (rises to a crossover `k*`, then falls), so its max is at `⌊k*⌋` or
`⌈k*⌉`, and that max satisfies a bound*. Proving this today requires a human to (a) find the
crossover, (b) supply the two monotonicity certificates (rise on `k ≤ k*`, fall on `k ≥ k*`),
(c) bound the finitely-many peak candidates. Each of (a)-(c) is a search with an exact
fitness. This is the target: evolve the certificate structure for one concrete unimodal
family, and — the research payoff — generalize the discovered shape into a reusable emitter.

## 2. Goals / Non-goals

**Goals**
- A `telperion.evolve` module: pluggable mutator + the validated fitness cascade + reuse of
  the existing `parallel_map.IslandModel` / MAP-Elites archive + config + a `telperion evolve` CLI.
- Hybrid mutation: local open-source LLM (default **Qwen2.5-Coder-7B**, Apache 2.0, served via
  Ollama) proposes shapes; structured operators (`relax`/`sharpen`/subdivision/degree-bump)
  refine and repair. LLM is **optional** — absent Ollama, falls back to structured-only.
- Demonstrate on the unimodal-integer-max target: evolve a certificate that `certify()`s and
  goes **kernel-green** via `lake env lean`, where the naive shape fails.
- Measure: kernel-green-hit-rate and wall-clock vs. hand-authoring, reported honestly.

**Non-goals (firewalled out)**
- Aiming this at the BG *crux* (proven archimedean+arithmetic — outside SOS/smooth certificate
  space; a compute sink). `PROOF_STATUS.md` §"Ruled out" is the reason.
- Auto-freezing evolved certificates or auto-adding them to any CI gate.
- Any change to `certify`/`emit`/the trust model. Bundling model *weights* in the repo.

## 3. Trust-model firewall (non-negotiable)

The evolve module can only *propose*. Every candidate still passes the identical
`certify → emit → lake build` gate. Evolved certificates are **never** auto-frozen and
**never** auto-wired to CI — a human promotes a survivor exactly as today (define family →
add to `telperion.toml` → freeze). The generator stays untrusted by design; the Lean kernel
stays the sole judge. A defective evolved certificate manifests as a compile failure, never a
false theorem. **Nothing about soundness changes.**

## 4. Architecture

New package `src/telperion/evolve/`, each unit single-purpose and independently testable:

### 4.1 `genome.py` — the evolvable certificate program
- `class CertificateGenome` (frozen dataclass, JSON-serializable) — for the unimodal target:
  - `crossover: sp.Rational | ("symbolic", expr)` — the conjectured `k*`.
  - `rise_cert` / `fall_cert` — structured descriptors of the two monotonicity certificates
    (which difference expression, Pólya multiplier degree, optional subdivision points).
  - `peak_bound` — how the finitely-many peak candidates are bounded (degree/multiplier).
  - `family_ref` — which concrete family/`GridSpec` this instantiates.
- `to_family(genome) -> InequalityFamily` — lowers a genome onto a real Telperion family
  (reuses `auto_lift`/`auto_subdivide`/`sos_half_deg`/`ties`).
- `to_prompt_repr(genome) -> str` / `from_llm_text(str) -> CertificateGenome | None` — the
  LLM I/O surface; `from_llm_text` is total (returns `None` on unparseable output — a bad
  mutation is just a miss, never an exception that stops the loop).

### 4.2 `mutate.py` — hybrid mutator
- `class StructuredMutator` — deterministic perturbations reusing `relax`, `sharpen`,
  subdivision, and degree/multiplier bumps. Always available, no deps.
- `class LLMMutator` — talks to a local **OpenAI-compatible endpoint** (Ollama). Prompt =
  current genome (`to_prompt_repr`) + the **fitness artifacts** from the last evaluation
  (exact counterexample / NOT_POLYA remedy / Lean error) + a system message stating the
  hard constraints (what must stay fixed vs. what may change). Per-island temperature for
  ensemble diversity; seed-pinned for reproducibility.
- `class HybridMutator(policy)` — LLM proposes; `StructuredMutator` repairs/refines the
  proposal. Falls back to structured-only if the endpoint is unreachable. One `.mutate(genome,
  artifacts, rng) -> CertificateGenome` interface for the loop.

### 4.3 `fitness.py` — the validated cascade (cheap → expensive)
Returns `FitnessResult(score: float, tag: str, artifacts: dict)`.
1. **Tier 0 `hunt()`** — exact adversarial minimum. If disproof → `DISPROVEN`, attach exact
   witness, never emit. (Disambiguates false-claim from wrong-shape — the non-gameable core.)
2. **Tier 1 `certify()`** — exact-arithmetic. Fail → negative, scaled by failing cells,
   artifacts carry the failure reason (`diagnose`-style: FALSE / NOT_POLYA + remedy).
3. **Tier 2 parsimony** — among certifying genomes, prefer smaller emitted Lean.
4. **Tier 3 `lake env lean`** — champions only. Emit via the right emitter, drop into the
   prebuilt-Mathlib project (`examples/g1_floors/lean`, v4.32.0, ~5 s/candidate), kernel-check.
   Ground truth. Timeboxed; artifacts carry the Lean error on red.

### 4.4 `loop.py` — evolutionary driver
- Reuses `telperion.parallel_map.IslandModel` + MAP-Elites archive (keyed on certificate-kind
  × degree × #cases). N islands, per-island temperature/seed, periodic elite migration.
- Cheap tiers (0–2) run on every candidate in-process; Tier 3 runs on per-island champions on
  a cadence (kernel compiles are the expensive resource).
- Budget controls: max generations, max LLM calls, max Lean compiles, wall-clock.
- Emits a run report (archive, best-per-cell, hit-rate, evaluations, kernel results).

### 4.5 `cli.py` + config
- `telperion evolve <family:factory> [--model TAG] [--islands N] [--gens G] [--no-llm] [--budget …]`.
- `[evolve]` table in `telperion.toml`: model tag + **digest** (pinned like the Mathlib rev,
  pulled via Ollama on first run — weights never committed), temperatures, budgets, lean-project path.
- Optional extra `telperion[evolve]` (adds an OpenAI-compatible client dep only). Core stays sympy-only.

## 5. Data flow

```
seed genome ──▶ HybridMutator.mutate(genome, artifacts) ──▶ candidate genome
                     ▲                                            │
        artifacts (counterexample / NOT_POLYA / Lean error)      ▼
                     └──────────── fitness cascade ◀── to_family() ─┐
                          hunt → certify → parsimony → [lake env lean]
                                        │
                            MAP-Elites archive + island migration
                                        │
                              run report → human promotes a survivor (manual, unchanged)
```

## 6. Testing strategy (TDD)

The kernel gives ground truth, so tests are strong and mostly deterministic (LLM tier is
mocked in unit tests; a single opt-in integration test hits a live Ollama).

- **`genome`**: round-trip `to_prompt_repr`/`from_llm_text`; `from_llm_text` returns `None`
  (never raises) on garbage; `to_family` lowers to a certifiable family for a known-good genome.
- **`fitness`**: on the *validated toy* landscape (from the spike) — naive shape scores as
  fail, false control returns `DISPROVEN` with the exact `u=0` witness, a good genome certifies;
  artifacts are populated on each tier. Golden-tests the cascade ordering.
- **`mutate`**: `StructuredMutator` moves along known axes; `LLMMutator` against a **stubbed**
  endpoint (fixture responses incl. malformed → `None`); `HybridMutator` falls back to
  structured when the endpoint raises.
- **`loop`**: on the toy landscape, a no-LLM run reaches a certifying champion within a budget;
  archive fills expected cells; determinism under fixed seed.
- **kernel integration** (opt-in, slow marker): champion emits + `lake env lean` green — reuses
  the g1_floors prebuilt Mathlib; skipped if `.lake` absent.
- **live-LLM integration** (opt-in): one end-to-end run against local Qwen2.5-Coder via Ollama
  on the unimodal target; asserts *a* kernel-green certificate is found (not a fixed one).

## 7. Build sequence (milestones)

1. **M0 skeleton + config** — package, `[evolve]` config, CLI stub, Ollama client wrapper
   (behind the optional extra), no logic. Tests: config parse, `--no-llm` path importable.
2. **M1 fitness cascade** — port the spike's cascade into `fitness.py` with artifacts; full
   unit tests on the toy landscape (the spike is the oracle).
3. **M2 genome + `to_family`** — the unimodal-integer-max genome; lower to a real family;
   pick one concrete unimodal family from the BG toolkit as the first instance.
4. **M3 structured mutator + loop (no LLM)** — reuse `IslandModel`; prove a no-LLM run evolves
   a certifying champion on the concrete unimodal family; kernel-green a survivor.
5. **M4 LLM mutator + hybrid** — Ollama-backed `LLMMutator`, artifact-fed prompts, `HybridMutator`
   fallback; stubbed unit tests + one live integration.
6. **M5 measure + write-up** — hit-rate & wall-clock vs. hand-authoring on the unimodal target;
   honest report; if it wins, sketch generalizing the discovered shape into a real emitter.

Each milestone is independently valuable and independently reversible; M3 already delivers a
working (LLM-free) evolutionary certificate search.

## 8. Open questions (resolve during implementation, not blocking)

- Exact concrete unimodal family to seed M2/M3 (candidate: a `B(L,j)`-style boost family from
  the arm-extremality work, where the per-`j` max sits at a rational crossover).
- Whether `LLMMutator` emits full-genome JSON or structured diffs — start with full-genome JSON
  (total parser, simplest), revisit if hit-rate is low.
- Migration/temperature schedule for islands — start with `parallel_map` defaults.
