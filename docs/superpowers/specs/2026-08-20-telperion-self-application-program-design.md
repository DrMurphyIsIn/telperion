# Telperion self-application program — design (2026-08-20)

**Status:** approved design, in implementation.
**Origin:** the "point Telperion at Telperion" differentiator. The Lean kernel
rejects a *false* theorem but is blind to the meaning-level failures that live in
the *statement*: vacuity, unfaithful models, circular reductions, and finite
samples masquerading as proofs. Telperion already has four reflexive checks for
these (`nonvacuity`, `faithfulness`, `circularity`, `upgradability`) — the
"faithfulness discipline aimed at the generator itself." This program expands
that reflexive / meta-soundness layer along three vectors (outward, inward,
forward) plus a front-door firewall and an explicit trusted-floor study.

## Design principle (applies to every workstream)

Each new capability is a **thin, deterministic, sympy-only module that composes
existing primitives** (`verdict`, `faithfulness`, `circularity`,
`upgradability`, `nonvacuity`, `lean_lint`, `prove_goal`). **No new trusted
surface.** Local verification = structural checks + soundness-lint + pytest;
**cloud CI (`lake build`) is the kernel gate** and the definition of "done" for
any Lean-carrying piece. TDD throughout (test first, red, green).

**Honesty guardrail (`conjecture1_proved=False` discipline).** A research piece
claims done only on CI-green. If it obstructs, it closes with an explicit
`OBSTRUCTED_AND_LOCATED` verdict (a witness / located cell), never a fabricated
success. Floats never decide a verdict (`require_exact` / `decide`).

## Landing posture

Work proceeds on `feat/prove-goal-backend` and follow-on branches against the
public repo `DrMurphyIsIn/Arda`. Branches are pushed and **merged autonomously
when cloud CI is green** (operator-approved posture). The already-built Phase 0–2
foundation (`prove.py`, `backend_lift.py`, `benchmark.py`) is committed first
because every workstream depends on the atomic `prove_goal` primitive.

---

## Sub-project A — the reflexive layer (buildable now, local-verifiable)

### A1 · `telperion audit <file.lean>` (Vector 1 / roadmap Phase 3)

The empty-niche referee: audit *anyone's* Lean, not just Telperion's own
emissions.

- **New module** `audit.py`: `audit_lean_text(text: str) -> AuditReport`.
  Composes:
  - `lean_lint.lint_lean_text` — `sorry`/`admit`, smuggled `axiom`,
    `Prop := True` stubs, missing type ascription, empty tactic block.
  - **Generalized `nonvacuity`** — extract each `theorem NAME … : CONCLUSION :=`
    and run `check_nonvacuous` on the conclusion. Requires generalizing
    `nonvacuity.check_nonvacuous` to accept an arbitrary theorem statement string
    (today it reads Telperion's own emitted bodies).
  - **Unused-hypothesis heuristic** — binder names declared in the signature but
    never referenced in the proof term (coarse, WARN).
- **`AuditReport`** dataclass: `findings: tuple[Finding, ...]`, `clean: bool`,
  `render()`. `Finding` = (line, code, severity, message).
- **Surfaces:** CLI verb `audit <file.lean>` (exit code encodes
  clean / warn / error), MCP tool `audit_lean(text)`.
- **Honest scope:** `circularity` / `upgradability` are *semantic* (need
  `pt → margin`), so they engage only when a conclusion parses as a certifiable
  inequality; otherwise the audit reports the structural subset and says so.
- **Tests:** a seeded vacuity defect (`theorem t : (0:ℝ) ≤ 0 := …`) is flagged;
  a known-good inequality proof is clean; `sorry`/`axiom` flagged.

### A2 · emitter-wide certificate-sensitivity (Vector 2a)

Generalize `nonvacuity.assert_certificate_sensitive` (today: wz / putinar / cone)
to a contract every certificate-carrying emitter satisfies.

- **Emitter base contract:** optional `_claim_expr(cert) -> sp.Expr` (0 for a
  true certificate) and `_corrupt_certificate(cert) -> cert'`. An emitter that is
  structurally identity-free (e.g. `DirectPolya` positivity, already covered by
  the reflexive `check_nonvacuous`) opts out with a stated reason.
- **Meta-test** `test_certificate_sensitivity.py`: iterate every registered
  emitter; assert each is either sensitivity-checked (true→0, corrupted→non-0) or
  in the explicit opt-out set with a reason. Telperion certifying a meta-property
  of its own emitters; new emitters must declare their stance or fail CI.

### A3 · meta-drift net (Vector 2c)

`test_meta_invariants.py` — invariants *about the pipeline*, run in CI:

1. `emit()` refuses a reflexive statement for every `LeanProfile` without
   `allow_reflexive=True`.
2. Every CLI verb parser constructs (argparse smoke over the subcommand table).
3. The trusted boundary holds — `import telperion` loads **zero** `telperion.bg`
   (re-asserts `test_core_boundary`'s guarantee as a standing invariant).
4. No emitter regresses on the certifiable-fragment benchmark: `benchmark.py`
   solve-count ≥ a frozen baseline floor.

### A4 · formalization firewall — LLM-free core (roadmap Phase 5, defensive half)

The statement-level defect the kernel cannot see is *misformalization*. Point the
reflex at the proposed statement *before* any proof.

- **New module** `formalize.py`:
  `firewall_statement(statement, symbols, oracle, *, seed, n) -> ProbeVerdict`
  composing:
  - `nonvacuity.check_nonvacuous(statement)` — does it say anything;
  - `faithfulness.faithfulness_check` — statement truth-value vs the informal
    intent's numeric instances at seeded exact points (caller supplies
    `oracle: pt → bool | margin`);
  - `circularity.circularity_check` — does the formalization smuggle the goal
    into its hypotheses.
  Returns a single four-state verdict.
- **Surfaces:** CLI verb `firewall`; optional pre-gate inside `prove_goal`
  (a statement failing the firewall is refused before certify).
- **LLM arm:** `formalize "<informal>"` (Ollama candidate generation) ships as a
  documented **opt-in stub** (`--llm`); the deterministic firewall runs on a
  supplied candidate and is the default path.

---

## Sub-project B — research / cloud-gated (attempt to CI-green; else located)

### B1 · self-hosting lemma certification (Vector 2b)

The reusable Lean lemmas the emitters depend on (`unimodal_peak`,
`RTree.telescope`, `wz_row_invariant`) are hand-written and *trusted*. Close the
loop.

- **`examples/self_hosting/`:** per lemma, a Telperion family that certifies the
  concrete instances the lemma discharges, plus a Lean file proving each instance
  is load-bearing and non-vacuous (via the A2 sensitivity contract).
- Frozen via the standard `certify → validate → emit → freeze` pipeline; **cloud
  CI compiles against pinned Mathlib** = done. Local = structural + lint only.

### B2 · self-profiled discovery → evolve→frozen + one combinatorics emitter (Vectors 3, roadmap Phases 4+6)

1. **Self-profiling** — `coverage.py`: run `diagnose` over the
   certifiable-fragment benchmark, aggregate the `NOT_POLYA` triage distribution
   into a coverage report naming the largest out-of-shape clusters
   (deterministic; buildable now).
2. **Evolve → frozen** — drive `telperion.evolve` (structured, LLM-free) on the
   concrete open **near-star `phi11` window** payload already in the repo
   (`examples/cg_round/NearStarWindow.lean`) until a champion passes the certify
   tier → emit → freeze → CI kernel-gate. This is the missing `EVOLVE_RESULTS`
   milestone: a kernel-frozen evolve-discovered certificate.
3. **New combinatorics emitter** — the most tractable gap the coverage report
   surfaces (candidate: a tangent-line / SOS-Schur symmetric-inequality
   certificate reducing to existing SOS/Handelman machinery); ship ≥1 new family
   end-to-end, CI-green.

Research risk is real on (2)/(3): if evolve or the emitter does not close, the
piece reports `OBSTRUCTED_AND_LOCATED` with the located obstruction.

### B3 · meta-circular fixed-point / trusted-floor study (Vector 4)

Point the audit calculus at the audit checks themselves.

- **`metacircular.py`:** adversarial reflexive/near-reflexive statements probing
  `nonvacuity` for a vacuity hole it green-lights; `circularity_check` run on the
  meta-checkers (does a checker assume what it verifies).
- **`docs/TRUSTED_FLOOR.md`:** enumerate and *locate* the irreducible trusted
  base — Lean kernel + exact-arithmetic decision primitives (`require_exact` /
  `decide`) + the statement-intent match — and state the Löb/Gödel floor plainly:
  self-application shrinks and *locates* the trusted base monotonically; it does
  not reach zero.

---

## Sub-project C — landing (autonomous on green)

Commit Phase 0–2 first, then land A/B on branches, push, and merge autonomously
when cloud CI is green, reporting each merge. CI is the kernel verifier.

## Execution shape

1. Commit + push Phase 0–2 (foundation).
2. Build the independent, local-verifiable pieces in parallel — **A1, A2, A3,
   A4, B2-coverage, B3-probes** — each TDD, dispatched as parallel subagents (no
   shared state).
3. Build the cloud-gated pieces — **B1, B2-evolve + emitter** — on top of the
   coverage output and the A2 contract.
4. C runs continuously.

## Module inventory (new/changed)

| Path | Kind | Workstream |
|---|---|---|
| `src/telperion/audit.py` | new | A1 |
| `src/telperion/nonvacuity.py` | changed (generalize) | A1, A2 |
| `src/telperion/emit.py` (+ emitter base) | changed | A2 |
| `src/telperion/formalize.py` | new | A4 |
| `src/telperion/coverage.py` | new | B2 |
| `src/telperion/metacircular.py` | new | B3 |
| `src/telperion/cli.py`, `mcp_server.py` | changed (verbs/tools) | A1, A4 |
| `tests/test_audit.py`, `test_certificate_sensitivity.py`, `test_meta_invariants.py`, `test_formalize.py`, `test_coverage.py`, `test_metacircular.py` | new | A/B |
| `examples/self_hosting/` | new | B1 |
| `docs/TRUSTED_FLOOR.md` | new | B3 |
