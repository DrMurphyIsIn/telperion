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

**Amendment (2026-10-30; step 3 Ruling 3, the owner's rule).** "A judge config with nanoda off fails validation, the
heavy judge included" is replaced by: nanoda may be off ONLY for a heavy node, meaning one with `heavy_certificates` or
`judge_via = "heavy"`. Those are exactly the nodes for which a local nanoda re-judge is mandatory (a proved heavy node
stays proved only with a passing local re-judge on its current artifact), so the second kernel is still applied to them,
locally rather than in the Comparator run. `kernel_policy.judge_config_problems` enforces this: nanoda off on any other
node is a validation failure.

**Amendment (2026-10-30; step 4 Ruling 1).**
- `unpermitted_axiom_hard_error` is not a field of the Comparator config (`comparator.challenge_config` has no such
  key), so it is not checked as one. The axiom whitelist is checked instead: `permitted_axioms` must be exactly the
  three standard axioms. Whether a hard-error setting is needed is left as a note for steps 5 and 6.
- "The list can only shrink" is enforced mechanically: `telperion kernel-policy check --base REF` fails if a project is
  ADDED to the exception list or an entry's toolchain is LOWERED relative to REF, and the CI `kernel-policy` job passes
  `--base origin/<base branch>` on every pull request.

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

**Amendment (2026-10-30; owner decision "Replay-isolate" of 2026-10-29, step 4 Rulings 7, 9 and 10). How the probe and
the fingerprint load the statement.** Both checks work on the theorem's ELABORATED constant, never on re-rendered text
(Ruling 7), and neither imports the untrusted module. Importing it runs its `initialize` blocks and lets its
`command_elab`, `tactic` and macro registrations elaborate the check's own commands; a re-review used exactly that to
forge verdicts. Instead (`src/telperion/checks/lean_replay.py`, the Comparator / lean4checker approach):
- the Lean process imports trusted modules only, from a pinned env whose files are verified against a sha256 manifest
  stored OUTSIDE the env (`telperion trusted-manifest build/verify`; `build` refuses to overwrite without `--force`);
- the untrusted module and its untrusted import closure are read as data, from private copies, and every constant is
  added through the kernel (`addDeclCore` with the kernel check on), so no initializer, elaborator, attribute or other
  extension of theirs is loaded, and no untrusted code with effects runs in the check's process;
- the check runs as a callback in that replayed environment;
- any `axiom` declared in the untrusted closure is refused (Ruling 10): the probe reports ERROR, and the fingerprint
  refuses;
- both checks report `olean_sha256`, the digest of the replayed closure's [module, part, sha256] list, and
  `mission checks-record` refuses a probe and a fingerprint that ran on different closures (Ruling 9).

**Amendment (2026-10-30; step 4 Rulings 5, 7 and 9). The negation probe as built.** "Prove the negation of the
conclusion" became a counterexample search: plausible's `Testable.checkIO` with a fixed seed (271828), and REFUTED is
read from the `TestResult` VALUE it returns (its `failure` constructor), never from printed text. The verdicts are
VACUOUS, REFUTED, PROBE_ONLY, WITNESSED and ERROR. A heartbeat timeout in a probe is PROBE_ONLY, never a verdict
(Ruling 5). WITNESSED needs a caller-supplied term proving the existential closure of the type's full, non-reducing
forall-telescope (every antecedent, the conclusion's arrows included, satisfiable at once). The `probe-only` label of
the text above is the PROBE_ONLY verdict, and the sign-off is a `signoff: <who>` in the `[checks]` note.

**Amendment (2026-10-30; step 4 plan Task 4, Rulings 2, 11, 12 and 13). Where the record lives and when it is
required.** The fingerprint is not stored in `[grant]`. The probe verdict, the closure verdict, the fingerprint, the
`olean_sha256` and the artifact's source sha256 are stored together in one `[checks]` record, written by
`mission checks-record` from the checks' own JSON output; a `[checks]` table with an unknown key is a schema error
(Ruling 12).
The probe and fingerprint JSONs also name the `theorem` they checked and the `source_sha256` of the `--file` they were
given, and `checks-record` refuses a probe of another theorem or a source that is absent or not the artifact's current
sha256 (Ruling 12; the final review removed the `--allow-missing-source` waiver). The final review also requires the
target to be the node's registered theorem (`guard_anchors.resolve_theorem`), and the probe and fingerprint JSONs to
carry the replay's axiom list, equal, standard, and including the closure audit's axioms for the target. That
cross-check is the interim guard for a known gap: `audit-closure` still imports the submission, so its output can be
forged by an imported module. The owner accepted the gap for this merge (2026-10-30), and porting the closure audit to
a replay callback is a step-5 follow-up. The grant rule applies to nodes
created on or after 2026-10-28; a node whose `created` is empty or is not, as a whole, an ISO date is treated as created
after it (Rulings 2 and 12, fail-closed). A grant that required checks records `checks_required = true` in `[grant]`,
and from then on the node requires them whatever its `created` says (Ruling 13: the decision is recorded, not read off
`gate_version`, because every new grant carries the new version, pre-cutoff nodes included). `mission verify` re-checks
the record on every proved node the rule covers, and `GATE_VERSION` is `2026-10-29.1` (Ruling 11). Known limitations
recorded by Rulings 11 and 12: the sign-off is free text; the closure audit, which imports rather than replays, is tied
to the other two checks by the theorem name only; and a `created` back-dated before a node's first grant is not caught.

**Amendment (2026-10-30; step 4 Ruling 9 and the caveat recorded with the fingerprint re-review). These checks are NOT A
SANDBOX.** Replay isolation keeps the submission's code out of the check's process, and nothing more. Building the
submission (`lake build`, or compiling a submitted text for the fingerprint) runs its code with the caller's
permissions, and so does `audit-closure`, which imports it. The `.olean` reader trusts its input bytes (a crafted file
is a memory-safety attack on the reading process), the memory bound is Lean's own best-effort `--memory`, and a
same-user process can still reach the private copies during a run. Untrusted submissions must therefore be built and
checked inside a sandbox, for example Comparator's sandbox on Linux CI. Providing that sandbox is the owner's separate
decision.

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
