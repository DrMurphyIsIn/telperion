# Telperion as a standalone repository: design

Date: 2026-10-27. Status: design approved section by section in conversation (sections 1-6). This written spec awaits the
owner's review. No repository is created and nothing is pushed until the owner approves this spec and then the
implementation plans.

## 1. Purpose

Telperion lives today in `telperion/` inside the public repository `DrMurphyIsIn/Arda`. It is mixed in with the
Brualdi-Goldwasser (BG) and Riemann-hypothesis (RH) work. Those streams show what Telperion can do, but they blur what
Telperion itself is. Full copies are also vendored, all at version 0.1.6 with no record of their source commit, into three
public repositories:
- `tenth-discriminant`;
- `brualdi-goldwasser`;
- `riemann-hypothesis-lean`.

**Goal:** a standalone repository, `DrMurphyIsIn/telperion`, that is the single source of truth. Every vendored copy draws
from a tagged release of it. The repackaging also carries the following:
- the Lean kernel soundness policy;
- four checks inspired by Axiom's AXLE, plus lean-metrics;
- registered external Lean libraries (RiemannJensen, ZetaZerosV2);
- a statement-first process modelled on Axiom's AreaLaw2D.

**Success criteria:**
1. `pip install` of the new repository passes its full test suite with no BG or RH code present.
2. Arda, with its labs installed as plugins, passes every test it passes today. The before and after counts are reported.
3. Every consumer carries a `VENDORED.json` pinned to a tag, and its CI runs `telperion vendor --check`, which fails on any
   drift.
4. Every judge runs nanoda, pinned, as a second kernel. Every proved node that was once judged by the Lean kernel alone has
   been re-judged.

## 2. Decisions (owner, 2026-10-27)

| Question | Decision |
|---|---|
| Boundary | Engine plus framework. The labs and domain data move out. |
| Vendoring | A pinned vendor copy plus a manifest (`telperion vendor`, `VENDORED.json`). |
| History | Filtered history from Arda (`git filter-repo`), with Claude-Session trailers stripped and Co-Authored-By kept. |
| Kernel | A second kernel everywhere. New projects need Lean v4.34.1 or later. v4.32.0 projects stay, with nanoda required. |
| Schedule | Spec and plans now. The build follows Wednesday 2026-10-28's queued work, except step 0 (the re-judge). |
| RH destination | RH examples and missions stay in Arda, where they live today. Moving them is a separate later decision. |
| Visibility and licence | Public. The current split stays: engine BSL 1.1 (with CLA); mathematics, examples and emitted certificates Apache-2.0 / CC-BY-4.0. |
| Name | "Telperion" is kept. The trademark caveat applies only to commercial use; a rename can come later at low cost. |

## 3. Repository layout and boundary

```
telperion/                  (new repo)
  src/telperion/            engine: certify, emit_*, verify, comparator, judge, CLI, MCP
  src/telperion/missions/   framework only (schema, judge, provenance, registry), no RH/BG data
  src/telperion/checks/     negation probe, statement fingerprint, closure audit, kernel floor (section 5)
  islands/                  registered external Lean libraries (section 6)
  examples/canonical/       about 10 small, domain-neutral examples, each built in CI
  docs/process/             statement layer, audit files, deviation ledger (section 7)
  VENDORING.md  LICENSING.md  CLA.md  CHANGELOG.md
```

**What moves out:**
- **To the BG repository:** `src/telperion/bg/` (the BG lab), `bg_upper_bound.py`, `bg_bulk_discharge.py`, `missions/bg`,
  and the BG examples.
- **Stays in Arda, as the RH lab:**
  - `rh_jensen/`;
  - `missions/rh`, `missions/mirrormere` and `missions/anduril`;
  - `research/`;
  - the RH examples, including `zeta_zero_localization` (about 87k files).

**Emitters stay in the engine.** That includes the RH-flavoured ones, such as Li positivity and the Weil-form enclosure,
because they are reusable certificate shapes.

**The plugin seam.** On origin/main at af4fde897, eight engine source files import `rh_jensen` and two import
`weil_form_eval`. Labs therefore register their emitters and negative-control adapters through a Python entry-point group,
`telperion.plugins`, and the engine never imports a lab.
- Each importer is classified. If it is generic, the dependency is inverted and the lab supplies it through the plugin. If
  it is RH-specific, it moves out with the lab.
- The current boundary test (`tests/test_core_boundary.py`, BG only) is generalised: no engine module imports any lab,
  checked statically (by AST) and dynamically (by what `import telperion` loads).

## 4. Vendoring

- **Copying in.** `telperion vendor --tag vX.Y.Z` copies a release into the consumer's `telperion/` and writes
  `telperion/VENDORED.json`. The manifest records:
  - the source repository, tag and commit;
  - a sha256 for every file;
  - the plugins the consumer installs.
- **Checking.** `telperion vendor --check` fails in any of these cases:
  - a vendored file has been edited, added or deleted;
  - the tag does not resolve to the recorded commit;
  - the manifest is missing.
  Every consumer's CI runs it. Engine fixes therefore have to land in the telperion repository, be released, and then be
  re-vendored.
- **Moving the consumers over.** Arda goes first. Then tenth-discriminant, brualdi-goldwasser and riemann-hypothesis-lean,
  one PR each. The owner approves every PR to a public repository. Published releases and Zenodo records are not touched; the
  change appears in each repository's next release.
- **Arda's labs (owner decision, 2026-10-27): separate lab packages.** After vendoring, Arda's `telperion/` is byte-identical to
  the release. The labs move out into Arda packages, with imports rewritten from `telperion.<lab>` to `telperion_<lab>.<...>`:
  - the RH lab goes to `labs/rh/` as package `telperion_rh` (rh_jensen, li_coeff, weil_form_eval, missions/rh, mirrormere,
    anduril, RH examples, research/);
  - the BG lab (`telperion/bg`, bg_* modules, missions/bg, BG examples) moves to the brualdi-goldwasser repo, per the spec.
  Rollout step 7 is split:
  - **7a:** the release, the `telperion vendor` tool, and the three public repos;
  - **7b:** the Arda lab-package refactor, planned after step 2 fixes the final classification.
  The rejected alternative was consumer-owned overlay paths inside `telperion/`.
- **Arda worktrees** (about 60) are not edited. Branches re-vendor when they rebase, and CI flags any branch that still
  carries the old copy.

## 5. Kernel policy and the new checks

### 5.1 Kernel policy

**Background.** Lean v4.33.1 fixed kernel soundness bugs, merged 2026-08-12 to 08-20. Two of them could derive `False` from
crafted input:
- #14806, a definitional-equality cache whose answers depended on query order;
- #14807, a proposition check that accepted a stuck type.

The other fixes are #14808 (type-checking generated recursors), #14582 (non-uniform inductive occurrences) and #14849 (a cap
on numeral size). On Arda main, 133 Lean projects are pinned to v4.32.0, which predates these fixes. The heavy missions judge
(`missions-comparator-heavy.yml`) is Lean-kernel-only. The other judges clone nanoda's HEAD unpinned.

**Policy, enforced in CI:**
- **Toolchain floor.** A check fails any Lean project below v4.34.1 unless it appears on a named exception list (today's
  v4.32.0 projects, plus external islands such as zeta-zeros-v2). The list can only shrink.
- **nanoda required.** Every judge runs nanoda, pinned to a reviewed commit (currently `37cb87b7`), with
  `unpermitted_axiom_hard_error: true`. A judge config with nanoda off fails validation, the heavy judge included.
- **Upgrades.** nanoda changes only through a PR that bumps the pinned commit and re-runs every negative control.
- **Re-judge (step 0).** Every proved mission node that passed with the Lean kernel alone is re-judged with nanoda, and the
  verdict is recorded in that node's provenance. A rejection sends the node back to unproved and is reported to the owner
  immediately.

### 5.2 Checks (`src/telperion/checks/`)

These are native implementations. Nothing is sent to Axiom's AXLE service. Each check is a small Lean meta-program plus a
Python wrapper. Each writes a verdict into the node's provenance, and each ships with a must-fail and a must-pass test.

1. **Negation probe** (inspired by AXLE's `verify_negation`).
   - **What it does.** For a frozen statement, it tries, within a time budget, to derive `False` from the hypotheses alone,
     and separately to prove the negation of the conclusion. Either success is a hard fail: VACUOUS or REFUTED.
   - **Its limit.** The probe is one-sided: failing to find `False` does not prove the hypotheses consistent.
   - **Witnesses.** Where it is practical, a hypothesis structure must come with a satisfying witness. If there is none, the
     node is labelled `probe-only` and needs a reviewer's sign-off.
   - **Must-fail control:** a contradictory hypothesis set.
2. **Statement fingerprint** (inspired by AXLE's `unfolded_type_hash`).
   - **What it does.** Hashes the statement's type after unfolding every project-local definition down to Mathlib and core
     constants, and stores the hash in `[grant]` next to `statement_sha256`.
   - **What it catches.** A shadowed or silently changed local definition. This complements Comparator's literal comparison
     of statements.
   - **Must-fail control:** a shadowed definition.
3. **Kernel-rejection verdict.** `verify.py` reports KERNEL_REJECTED separately from elaboration errors. **Must-fail
   control:** a declaration the kernel rejects.
4. **Closure audit.**
   - **What it does.** A short Lean script of our own dumps the transitive constant closure of the main theorem. The check
     then compares it against a deny-list and a namespace allow-list (the KC-1 A1 audit, made generic). The script runs on
     every toolchain we use.
   - **lean-metrics** (AxiomMath/lean-metrics, pinned) is an optional add-on for size, tactic and import reports on
     toolchains v4.34 or later. It is never a gate.
   - **Must-fail control:** a denied constant.

**Grant rule.** No node is granted unless the negation probe passes (or is `probe-only` with sign-off) and the closure audit
is clean. The fingerprint is recorded at grant time.

## 6. Library islands (`islands/`)

An island is an external Lean library that Telperion has verified and pinned. The core repository holds only each island's
registration:

```
islands/<name>/island.toml      source repo + pinned commit, toolchain, licence, challenge file, theorem names, intended use
islands/<name>/challenge.lean   copy of the library's Mathlib-only statement file (sha256 recorded)
islands/<name>/comparator.json  our config: the 3 standard axioms, nanoda on
islands/<name>/REPLAY.md        our replay record: date, machine, verdicts, sha256s
```

**Registering an island.** `telperion island add`:
1. fetches the library at its pinned commit;
2. builds it in an isolated packages directory, through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`, never touching a
   shared `.lake`;
3. runs Comparator against the library's own challenge file, with nanoda on;
4. runs the section 5.2 checks on every statement we intend to use.

**Status.** An island is either `verified` (our replay passed) or `self-reported`. Labs may rely only on `verified`
islands. A replay is a full Mathlib-scale build taking hours, so registration runs once per pinned commit, not on every PR.

**The first two islands:**
- **riemann-jensen.** AxiomMath/RiemannJensen, Lean v4.35.0. It covers the Jensen polynomials of Riemann's Ξ and the
  continuation of Dedekind ζ. RH Track 1 and Arda's `rh_jensen` lab would use it.
- **zeta-zeros-v2.** AxiomMath/ZetaZerosV2, Lean v4.34.0-rc2. It covers Lamzouri's result that more than 2/3 of zeros are
  simple and on the critical line.
  - **Toolchain.** v4.34.0-rc2 is below the floor, and whether it carries the kernel fixes is unconfirmed. It is therefore
    on the exception list, with nanoda required.
  - **Dependency.** It relies on Axiom's PrimeNumberTheoremAnd fork, some files of which still contain `sorry`.
    Comparator's axiom whitelist catches any `sorryAx` in the theorems we use, and registration fails if one appears.

Islands are a generic mechanism, and these two are its reference entries. RH-specific use of them stays in the labs.

## 7. Statement-first process (`docs/process/`, missions templates)

1. **Frozen statement layer.**
   - `telperion mission init` creates `Statements.lean`, containing only `def … : Prop` statements and their supporting
     definitions, before any proof exists.
   - `telperion mission freeze` records its sha256 and its statement fingerprints in `[grant]`.
   - From then on CI fails if the file changes, unless the change carries a version bump and a recorded read-back by the
     owner.
2. **Audit files.** Each mission gets a generated `Audit.lean` that runs `#print axioms` on every proved result. The judge
   cross-checks that output against Comparator's axiom list, because `#print axioms` can read a stale cache.
3. **Deviation ledger.**
   - `DEVIATIONS.md` records every departure of the formal statement from its source: conventions, strengthened or weakened
     hypotheses, change of field or parameters. Each entry has a reason and a date.
   - A grant requires the ledger to be present and read back. An empty ledger must say "none" explicitly.
4. **Provenance headers.** Every ported file names its source repository, file and commit. A lint check enforces this,
   islands included.

**Scope.** These rules apply to new missions only. Existing proved nodes are recorded as `pre-process`. KC-1's F0
(`KC1Statement_F0_FROZEN_558248cd.lean`) already conforms and becomes the first mission to use the full flow.

## 8. Rollout

Each step gets its own implementation plan and PR. Only step 0 runs before Wednesday's queued work is finished.

| Step | Work | Gate |
|---|---|---|
| 0 | Pin nanoda; re-judge every Lean-kernel-only proved node, on Arda as it stands | Result reported to the owner; any rejection reported immediately |
| 1 | Plugin seam and the generalised boundary test, inside Arda | Arda tests green with no loss of coverage |
| 2 | Extraction: filtered history into the new repo, built locally first | Full suite green with no labs; owner approval before any push or publication |
| 3 | Kernel policy and judge-config validation | Must-fail: a nanoda-off config, and a v4.32.0 project not on the exception list |
| 4 | The section 5.2 checks | Each check's must-fail test fails and its must-pass test passes |
| 5 | Process templates (section 7) | A dry-run mission completes init, freeze and grant |
| 6 | Register the islands riemann-jensen and zeta-zeros-v2 | Our own Comparator replay passes |
| 7 | Release v0.2.0; vendor into Arda, then into the three public repos one PR at a time | `vendor --check` green in each; owner approves each public PR |

## 9. Testing

- Every new check and policy has a must-fail and a must-pass test, in the style of the existing negative-control harness.
  Rejection must happen for the intended reason; the harness's `okay = kernel_rejects AND true_compiles` invariant is reused.
- **Extraction is checked by test equivalence.** Every test that passes in Arda before extraction either passes in the new
  repository or moves with its lab and passes there. The before and after test counts are reported per module, and nothing
  disappears silently.
- Lean builds run through leanlock, with BLAS threads pinned to 1 and no `lake` command run on a shared packages directory.

## 10. Risks

- **The plugin seam** is the most likely source of regressions, because of the eight `rh_jensen` importers. Step 1 does it
  inside Arda before any extraction.
- **History hygiene.** Before anything is pushed, the filtered history is scanned for credentials, for Claude-Session
  trailers, and for paths that should not move. Arda is already public, but the new repository is a new public artifact.
- **Replay cost.** Island replays and the step 0 re-judge are CI- and CPU-heavy. They are scheduled so they do not compete
  with Wednesday's queue, apart from step 0.
- **Name.** The Tolkien-estate trademark caveat applies only to commercial use. A later rename costs a repository rename plus
  a re-vendor.

## 11. Out of scope

- Migrating the v4.32.0 projects to a newer Mathlib.
- Moving the RH material into riemann-hypothesis-lean.
- Using Axiom's hosted AXLE service or its MCP server.
- Any change to already-published releases or Zenodo records.
