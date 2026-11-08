# Step 6: Library Islands (riemann-jensen, zeta-zeros-v2), Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A generic island mechanism. An island is an external Lean library that Telperion has replayed itself: Comparator
with nanoda on, plus the step 4 statement checks. Its pinned registration lives in `islands/<name>/`. The first two islands
are AxiomMath/RiemannJensen and AxiomMath/ZetaZerosV2.

**Architecture:**
- `src/telperion/islands.py` holds the registry model, validation, the replay runner and `require_verified`.
- The CLI command is `telperion island add|replay|list|check`.
- The core repo holds only the registration: `island.toml`, a byte copy of the challenge file, our `comparator.json`, and
  `REPLAY.md`. It never holds library source.
- Builds happen in `~/telperion-tools/islands/<name>/`. That directory is isolated, has its own `.lake`, and every build
  goes through leanlock.
- The kernel policy (step 3) also reads each island's toolchain.

**Tech Stack:** Python 3.11+, tomllib, Comparator and lean4export (tag = island toolchain), nanoda (`NANODA_REV`), pytest.
Repo: `~/telperion-repo`.

**Spec:** `docs/superpowers/specs/2026-10-27-telperion-standalone-design.md`, section 6 and rollout step 6.

## Pinned facts (2026-10-27, from GitHub)

| island | source | commit | toolchain | licence | Comparator theorems |
|---|---|---|---|---|---|
| riemann-jensen | github.com/AxiomMath/RiemannJensen | `c1e023fa3ae7161219dde3dcb73f0c28ff972be2` (2026-10-23) | `leanprover/lean4:v4.35.0` | Apache-2.0 | 4 (`RiemannJensen.Challenge.*`) |
| zeta-zeros-v2 | github.com/AxiomMath/ZetaZerosV2 | `1d7edeb4e67096f9da1b37cd4b763e8b73886655` (2026-10-03) | `leanprover/lean4:v4.34.0-rc2` | Apache-2.0 | 12 (`ZetaZeros.Challenge.*`) |

- Both ship `Challenge/Basic.lean`, `Solution/Basic.lean` and `Comparator/comparator.json`. Each config has
  `enable_nanoda: true` and the three standard axioms.
- zeta-zeros-v2 depends on AxiomMath/PrimeNumberTheoremAnd @ `c19697c736`, which has `sorry` in some IEANTN files. The
  replay's axiom whitelist catches any `sorryAx` reaching the 12 theorems.
- Comparator tags exist for v4.35.0 and v4.34.0-rc2.

**Open item for the owner (raised here; it does not block this step):** Comparator has NO `v4.34.1` tag. The tags run
v4.34.0, then v4.35.0-rc1 and later. The step 3 floor is v4.34.1. A project pinned at exactly v4.34.1 therefore cannot be
judged by a matching Comparator build.
- **Recommended:** new projects default to v4.35.0, which has a tag and carries the kernel fixes. v4.34.1 then has no
  practical users.
- **Alternative:** build Comparator from source at a commit compatible with v4.34.1.

## Global Constraints

- **Isolation:**
  - Clone each island to `~/telperion-tools/islands/<name>/src` at the pinned commit. Verify that
    `git rev-parse HEAD` equals the pin.
  - Never run lake with a shared packagesDir. Never run `lake update`.
  - Every lake and lean command goes through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`.
  - Run one replay at a time.
- **Statement integrity:** the registered `challenge.lean` is a byte copy, and its sha256 is recorded. The replay refuses
  to run if the clone's `Challenge/Basic.lean` sha256 differs.
- **Our `comparator.json`** must have exactly the three standard axioms and `enable_nanoda: true`, and must list exactly
  the island's theorem names. If Axiom's config differs in any of these, ours wins, and the difference is recorded in
  `REPLAY.md`.
- **Status:**
  - `verified` iff `REPLAY.md` records a PASS that satisfies all of these:
    - the Comparator log has the three accept lines (`parse_comparator_log`) and a header
      `ISLAND-HEADER island=<name> commit=<pin> challenge_sha256=<sha>`;
    - nanoda ran at the pinned `NANODA_REV`;
    - every intended theorem has a negation-probe verdict of PROBE_ONLY or WITNESSED and a recorded fingerprint.
  - Otherwise the status is `self-reported`.
- **Kernel policy:** zeta-zeros-v2 (v4.34.0-rc2) is on the exception list as `islands/zeta-zeros-v2`, with reason
  `"external island pinned before the v4.33.1 kernel fixes; judged with nanoda"`.
- **Git:** run as peterwmurphy in `~/telperion-repo`. Commits carry the standard trailer and no Claude-Session trailer.
  Nothing is pushed.

## Review Focus

1. **The pin moves.** A registry whose `commit` changes must drop to `self-reported` until it is re-replayed (Task 1
   `test_commit_change_invalidates`).
2. **The upstream challenge changes under the same commit.** This is impossible, but a local edit to the registered copy is
   possible. `check` must compare the copy with its recorded sha (Task 1 `test_challenge_copy_tamper`).
3. **A replay that hits `sorryAx`** through the PNT fork must record FAIL, not PASS (Task 2 `test_sorry_axiom_fails`, which
   feeds a log containing the unpermitted-axiom line).
4. **`require_verified` on an unknown island name.** It should give a clear error, not a KeyError (Task 1).
5. **Island toolchains invisible to the kernel policy.** Without wiring, the island's toolchain would bypass the floor
   (Task 1 `test_policy_sees_island_toolchain`).

---

### Task 1: The registry model, validation, the `check`/`list` CLI, and kernel-policy wiring

**Files:**
- Create: `src/telperion/islands.py`
- Modify: `src/telperion/checks/kernel_policy.py`. `find_projects` also yields `("islands/<name>", toolchain)` for every
  `islands/*/island.toml`.
- Modify: `src/telperion/cli.py`, adding `telperion island list` and `telperion island check [NAME]`.
- Test: `tests/test_islands.py`

**Interfaces:**
- `island.toml` schema:
  ```toml
  name = "riemann-jensen"
  source = "https://github.com/AxiomMath/RiemannJensen"
  commit = "<40-hex>"
  toolchain = "leanprover/lean4:v4.35.0"
  licence = "Apache-2.0"
  challenge_module = "Challenge.Basic"
  solution_module = "Solution.Basic"
  challenge_sha256 = "<64-hex of challenge.lean>"
  theorems = ["RiemannJensen.Challenge.riemannJensen_main", "..."]
  intended_use = "RH Track 1 (Jensen-Polya) and Arda's rh_jensen lab: ..."
  [replay]            # absent until a replay passes
  date = "..."
  commit = "<the pin the replay ran>"
  challenge_sha256 = "..."
  nanoda_rev = "<40-hex>"
  comparator_tag = "v4.35.0"
  log_sha256 = "..."
  verdict = "pass"
  [replay.checks]
  "<theorem>" = { probe = "PROBE_ONLY", fingerprint = "<64-hex>" }
  ```
- `load_island(root, name) -> Island` (a frozen dataclass).
- `island_problems(root, name) -> list[str]` checks:
  - the schema and the hex lengths;
  - the challenge copy's sha256;
  - a replay pin that differs from `commit`, or a replay challenge sha that differs;
  - verdict, probes and fingerprints present for every theorem.
- `status(root, name) -> "verified" | "self-reported"`.
- `require_verified(root, name)` raises `IslandError(f"island {name!r}: ...")` unless the island is verified. That includes
  an unknown name.

- [ ] **Step 1: Write the failing tests** on a tmp `islands/demo/` built by a helper `_island(tmp, **overrides)`. Cases:
  - `test_valid_unreplayed_is_self_reported`;
  - `test_valid_replayed_is_verified`;
  - `test_commit_change_invalidates`, where the replay commit no longer matches the pin;
  - `test_challenge_copy_tamper`;
  - `test_missing_theorem_check`;
  - `test_require_verified_unknown_name`;
  - `test_policy_sees_island_toolchain`: `find_projects` includes `islands/demo` with its toolchain, and a below-floor one
    without an exception is a policy problem;
  - `test_cli_list_and_check_exit_codes`.
- [ ] **Steps 2-4:** RED, then implement, then GREEN. Also run `tests/test_kernel_policy.py`.
- [ ] **Step 5: Commit** with the message `islands: registry model, validation, list/check CLI; kernel policy reads island toolchains`.

---

### Task 2: `telperion island add` and `telperion island replay`

**Files:**
- Modify: `src/telperion/islands.py`
- Modify: `src/telperion/cli.py`
- Test: `tests/test_islands.py` (append; replay is tested with injected runners, no Lean)

**Interfaces:**
- **`add_island(root, name, source, commit, intended_use, *, fetch)`.** It:
  - clones at the commit into the tools directory, via the injected `fetch`;
  - copies `Challenge/Basic.lean` to `islands/<name>/challenge.lean`;
  - reads the toolchain and theorem names from the clone (`lean-toolchain`, `Comparator/comparator.json`);
  - writes `island.toml` without `[replay]`;
  - writes our `comparator.json` (three axioms, nanoda on, the same theorem names, the same modules);
  - writes `REPLAY.md` with a "not yet replayed" note.
- **`replay_island(root, name, *, run)`.** It:
  - re-verifies the clone's HEAD and the challenge sha;
  - computes `comparator_tag(toolchain)`, adding v4.35.0 to `COMPARATOR_TAG_FOR_TOOLCHAIN` if missing;
  - writes the ISLAND-HEADER as the first line of the log;
  - runs, through the injected `run`:
    1. `lake exe cache get` and `lake build` (leanlock);
    2. `lake env comparator islands/<name>/comparator.json`, with the landrun shim and the pinned nanoda;
    3. `probe-negation` per theorem against the challenge;
    4. `fingerprint` for all theorems.
  - parses the results and writes `[replay]` and `[replay.checks]` only on overall PASS;
  - appends a dated section to `REPLAY.md` in every case, with commands, wall time, peak memory and the log sha256.
- **The real `run`** uses `subprocess` with the PATH and `COMPARATOR_*` environment pattern from
  `missions/judge/rejudge_queue.sh` in Arda, at the same Comparator tag and nanoda pin. Reuse that script's landrun shim
  verbatim.

- [ ] **Step 1: Write the failing tests** with fake `fetch` and `run` callables that return canned outputs. Cases:
  - `test_add_writes_registration`;
  - `test_add_rejects_config_with_extra_axiom`: Axiom's config permits `sorryAx`, so ours is written with three axioms and
    REPLAY.md records the difference;
  - `test_replay_pass_writes_replay_table`;
  - `test_sorry_axiom_fails`: the Comparator log contains `unpermitted axiom "sorryAx"`, so the verdict is FAIL and there is
    no `[replay]`;
  - `test_probe_vacuous_fails`;
  - `test_head_mismatch_refuses`.
- [ ] **Steps 2-4:** RED, then implement, then GREEN.
- [ ] **Step 5: Commit** with the message `islands: add and replay (Comparator + nanoda + negation probe + fingerprint), injected runners`.

---

### Task 3: Register and replay riemann-jensen

- [ ] **Step 1:** `telperion island add riemann-jensen --source https://github.com/AxiomMath/RiemannJensen --commit c1e023fa3ae7161219dde3dcb73f0c28ff972be2 --use "RH Track 1 (Jensen-Polya hyperbolicity); upstream for Arda's rh_jensen lab"`.
- [ ] **Step 2:** Build the Comparator, lean4export and nanoda tools if they are absent. Reuse `~/telperion-tools/` from
  step 0: `comparator-v4.35.0` is new, so build it as in step 0's queue Step 1. Then run
  `telperion island replay riemann-jensen` in the background, and log to `~/telperion-tools/islands/riemann-jensen/replay.out`.
  Expect hours.
- [ ] **Step 3:** On PASS, `telperion island check riemann-jensen` must report `verified`.
- [ ] **Step 4:** Commit `islands/riemann-jensen/` with the message
  `islands: riemann-jensen @c1e023fa registered and replayed (verified)`. On FAIL, commit the registration as
  `self-reported`, with REPLAY.md showing the failure, and report to the owner.

---

### Task 4: Register and replay zeta-zeros-v2

- [ ] **Step 1:** `telperion island add zeta-zeros-v2 --source https://github.com/AxiomMath/ZetaZerosV2 --commit 1d7edeb4e67096f9da1b37cd4b763e8b73886655 --use "positive-proportion results (Lamzouri 67.25%); reference for RH emitter work"`.
- [ ] **Step 2:** Add the kernel-policy exception for `islands/zeta-zeros-v2`. Run `telperion kernel-policy check`, which
  must be OK.
- [ ] **Step 3:** Replay as in Task 3, using the `comparator-v4.34.0-rc2` tools. Watch the log for `sorryAx` from the PNT
  fork. If it appears, the island stays `self-reported`, and the exact theorems and axiom path go in REPLAY.md and to the
  owner.
- [ ] **Step 4:** Commit with the message `islands: zeta-zeros-v2 @1d7edeb4 registered (<verified|self-reported>)`.

---

### Task 5: Documentation

- [ ] Write `docs/ISLANDS.md` covering:
  - what an island is;
  - the registration layout;
  - the add, replay and check commands;
  - the rule that labs may only `require_verified` islands;
  - the kernel-policy interplay;
  - the two current islands, with status and dates;
  - the Comparator-tag open item.

  Link it from `README.md`. Commit with the message `docs: ISLANDS.md`.

---

## Amendment, 2026-10-31: owner decisions and the C2 witness (Task 0)

**Owner decisions (2026-10-31):**
1. **Comparator tag gap: default to v4.35.0.** New projects default to `leanprover/lean4:v4.35.0`. v4.34.1 is
   documented as having no matching Comparator tag; no Comparator is built from source.
2. **Island replays run in the contrarian's sandbox** (the remote Linux container with the cap-drop bwrap wrapper), not
   on the owner's Mac. External library code is never built locally.
   - Tasks 3-4 change accordingly:
     - `telperion island add` runs locally, since it only records the registration and copies the challenge by
       byte;
     - the replay itself is run by the contrarian at the pinned commit;
     - bb verifies the logs;
     - Telperion ingests the result with a new `telperion island record-replay <name> --log <comparator log>
       --probe-json <...> --fingerprint-json <...>`, which applies exactly the `verified` rules above to the supplied
       files.
   - `telperion island replay` stays, for operators who do have a sandbox. Its docs say it must run inside one.
3. **C2 witness:** the first step-6 item, as Task 0 below.

### Task 0: Downgrade-only reducing-telescope check on the negation probe's witness

**Why.** Step 4's C2 residual is still open. A vacuous sub-proposition sitting under a conclusion head that the probe
does not expand can reach WITNESSED with a satisfiable pad. Examples of such heads: `id`, a local structure, `∧`, `↔`,
`¬`, a beta-redex, `let`. A concrete case is `∀ m, m = m → id (∀ n, n < 0 → n = 7)`. WITNESSED skips the human
sign-off, so a false WITNESSED is the unsound direction.

**Change** (`src/telperion/checks/negation_probe.py`). WITNESSED now additionally requires the witness to close the
∃-closure built over the REDUCING telescope as well:
- use `forallTelescopeReducing` at default transparency, after the existing non-library head unfolding;
- Prop binders exposed only by reduction must also be witnessed.

If the second check fails, or exposes Prop binders the witness does not cover, the verdict drops to PROBE_ONLY with the
reason "witness does not survive reduction". The check NEVER upgrades a verdict, and it never changes the false probe,
which keeps Ruling 8's non-reducing premise split.

**Tests** (Lean env, must-fail controls):
- the example above is not WITNESSED;
- the same with `∧` / `↔` / `¬` / let / beta-redex heads is not WITNESSED;
- an honest witnessed statement stays WITNESSED;
- a timeout in the reducing step gives PROBE_ONLY (fail closed).

**Commit:** `checks: WITNESSED also requires the witness to survive the reducing telescope (downgrade-only)`
