# Step 5: Statement-First Process (AreaLaw2D Discipline), Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** New missions follow the AreaLaw2D discipline mechanically:
- a statement layer frozen at campaign level, which can change only through a recorded unfreeze;
- a generated `Audit.lean` (`#print axioms`), cross-checked against the closure audit;
- a `DEVIATIONS.md` ledger the grant requires;
- a provenance-header lint for ported files.

**Architecture:** What exists already:
- Per-node statement files under `<campaign>/lean/Statements/`, with hashed provenance headers.
- `regen_diff`, which detects hand edits.
- Grants that record `statement_sha256`.

This step adds:
- **The freeze file.** A campaign-level `FREEZE.toml`, written by `mission freeze`. It lists each node's statement sha256
  and, when available, its step 4 fingerprint. `verify_campaign` fails on any drift unless a matching `[[unfreeze]]`
  entry exists.
- **A new module, `missions/process.py`,** holding:
  - the Audit.lean renderer and parser;
  - the deviation-ledger parser;
  - the provenance lint.
- **Two grant gates for nodes created on or after 2026-10-28** (the step 4 cutoff): a frozen campaign, and a valid
  deviation ledger. Older nodes and campaigns show `pre-process`.

**Tech Stack:** Python 3.11+, tomllib, pytest, Lean `#print axioms`. Repo: `~/telperion-repo`.

**Spec:** `docs/superpowers/specs/2026-10-27-telperion-standalone-design.md`, section 7 and rollout step 5.

## Global Constraints

- **Cutoff:** `2026-10-28`, the same constant as step 4. Import it from one place: `telperion.missions.process.CUTOFF`.
  Step 4's grant check reads it too, so move step 4's literal there in this step.
- **Unfreezing:** an unfreeze needs all of these:
  - a version bump (`version` in FREEZE.toml increases by 1);
  - a reason;
  - a read-back identity that differs from the unfreezing author, matching the missions independence rule
    (`docs/AUDIT_INDEPENDENCE_2026-09-23.md`).
- **The deviation ledger:**
  - Its format is the line `none`, or entries of the form `- YYYY-MM-DD | <what deviates> | <why>`.
  - An empty file or a missing file is an error. Spec 7 says an empty ledger must SAY none.
- **Provenance header:** `-- Provenance: repo=<url> file=<path> commit=<40-hex>`. A Lean file is "ported" if its leading
  comment block, meaning its first 30 lines, matches `(?i)\b(ported|adapted|copied) from\b`. Files listed in a campaign's
  `PORTED.toml` count as ported too.
- **Git:** run as peterwmurphy in `~/telperion-repo`. The trailer is `Co-Authored-By: Claude Opus 5.5
  <noreply@anthropic.com>`, with no Claude-Session trailer. Nothing is pushed.
- **Tests:** `PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest <files> -q -p no:cacheprovider`.

## Review Focus

1. **A statement edited and FREEZE.toml re-written in the same commit** to hide it. `verify` compares against the git-tracked
   freeze history: the version must increase, and every version must have its `[[unfreeze]]` entry (Task 1
   `test_rewritten_freeze_without_unfreeze_fails`).
2. **A self-read-back.** An `[[unfreeze]]` read back by its own author must fail (Task 1 `test_self_readback_rejected`).
3. **A ledger saying `None.` or `N/A`.** It must be exactly `none` after stripping whitespace, case-insensitive, so a
   reasonable person is not tripped by `None`. `N/A` is rejected with a message saying to write `none` (Task 3
   `test_none_spellings`).
4. **A `#print axioms` line that wraps over multiple lines.** Long axiom lists are printed one per line. The parser must
   accept both shapes (Task 2 `test_wrapped_axioms`).
5. **"Adapted from" appearing inside a docstring deep in a file.** Only the leading block counts (Task 4
   `test_late_mention_not_ported`).

---

### Task 1: `mission freeze`, `mission unfreeze`, and the drift check

**Files:**
- Create: `src/telperion/missions/process.py`, holding `CUTOFF`, the freeze functions, and later tasks' functions.
- Modify: `src/telperion/cli.py`, adding `mission freeze` and `mission unfreeze`.
- Modify: `src/telperion/missions/verify.py`. `verify_campaign` calls `freeze_problems`, and `grant_status` calls
  `freeze_grant_problem` for post-cutoff nodes.
- Test: `tests/test_missions_process.py`

**Interfaces:**
- `freeze(root: Path, *, identity: str, session: str, date: str) -> dict`. It writes `<root>/FREEZE.toml`:
  ```toml
  version = 1
  frozen = "2026-10-28"
  identity = "..."
  session = "..."
  [statements]
  "Node_A" = "<sha256 of statement body>"
  [[unfreeze]]          # one per version > 1
  version = 2
  date = "..."
  author = "..."
  reason = "..."
  readback_identity = "..."
  ```
  Hashes use `statements.statement_body(root, node)`.
- `unfreeze(root, *, author, reason, readback_identity, date) -> dict` refuses when `readback_identity == author`. It bumps
  `version`, appends the entry, and re-hashes all statements.
- `freeze_problems(root: Path) -> list[str]` reports:
  - "statement drift" for any statement whose current hash differs from FREEZE.toml;
  - any node added since the freeze that is not in `[statements]`;
  - any `version > 1` without matching `[[unfreeze]]` entries for 2..version;
  - any self-read-back.
  - A missing FREEZE.toml is not an error for a pre-cutoff campaign.
- `freeze_grant_problem(root, node) -> str`: "" unless the node is post-cutoff and either no FREEZE.toml exists or the node
  is not in it.

- [ ] **Step 1: Write the failing tests.** Use `tests/missions_fixtures.py` plus a tmp campaign with two nodes written via
  `statements.write_statement`. Cases:
  - `test_freeze_records_hashes`;
  - `test_statement_drift_detected`: edit a statement body, and `freeze_problems` mentions "statement drift" and the node;
  - `test_unfreeze_bumps_and_clears_drift`;
  - `test_self_readback_rejected`, where `unfreeze` raises `ValueError`;
  - `test_rewritten_freeze_without_unfreeze_fails`: hand-edit FREEZE.toml to `version = 2` with new hashes and no
    `[[unfreeze]]`, and `freeze_problems` reports the missing unfreeze;
  - `test_post_cutoff_node_needs_freeze_to_grant`: `grant_status` raises `GateError` mentioning "frozen";
  - `test_pre_cutoff_campaign_without_freeze_ok`.

  Write each as a short pytest function against the interfaces above.
- [ ] **Step 2:** RED (ModuleNotFoundError).
- [ ] **Step 3:** Implement the interfaces in `process.py`. Add the CLI subcommands. Mirror `ci-record`'s campaign loading
  and the identity and session requirements `mission grant` uses. In `verify.py`:
  - extend `verify_campaign`'s errors with `freeze_problems(root)`;
  - in `grant_status`, when `new_status == "proved"`, raise `GateError` on a non-empty `freeze_grant_problem`.
- [ ] **Step 4:** GREEN. Also run `tests/test_missions_*.py`.
- [ ] **Step 5: Commit** with the message `missions: campaign statement freeze with recorded, read-back unfreezes`.

---

### Task 2: `Audit.lean` generation and its cross-check

**Files:**
- Modify: `src/telperion/missions/process.py`
- Modify: `src/telperion/cli.py`, adding `mission audit-file` (writes `<root>/lean/Audit.lean`) and
  `mission audit-crosscheck --print-axioms-out F --closure-json F`
- Test: `tests/test_missions_process.py` (append)

**Interfaces:**
- `render_audit_file(root) -> str`. It imports every proved node's artifact module, with one `#print axioms <theorem>` per
  proved node, sorted by slug. The header comment says the file is generated.
- `parse_print_axioms(output: str) -> dict[str, set[str]]` accepts both shapes:
  - one line: `'T' depends on axioms: [propext, Classical.choice, Quot.sound]`;
  - wrapped, one axiom per line;
  - and `'T' does not depend on any axioms` maps to an empty set.
- `crosscheck_axioms(print_axioms: dict, closure_axioms: dict) -> list[str]`. Its input is the closure audit JSON's
  per-target axiom lists; read `closure_audit.AuditResult.to_json` for the key. It reports every theorem whose sets differ,
  naming the side each extra axiom is on. A theorem missing from either side is a problem.

- [ ] **Step 1: Write the failing tests:**
  - `test_render_lists_proved_only`;
  - `test_parse_single_line`;
  - `test_wrapped_axioms`, which feeds a wrapped block, for example:
    ```
    'T' depends on axioms: [propext,
     Classical.choice,
     Quot.sound]
    ```
  - `test_no_axioms`;
  - `test_crosscheck_flags_stale_cache_case`: `#print axioms` says `{propext}` while the closure says
    `{propext, sorryAx}`, so it is reported;
  - `test_crosscheck_equal_ok`.
- [ ] **Steps 2-4:** RED, then implement, then GREEN.
- [ ] **Step 5: Commit** with the message `missions: generated Audit.lean and a #print-axioms vs closure-audit cross-check`.

---

### Task 3: The deviation ledger

**Files:**
- Modify: `src/telperion/missions/process.py`, adding `DEVIATIONS_TEMPLATE` and `parse_deviations(text) -> list[dict]`,
  which raises `ValueError` on any malformed content.
- Modify: `src/telperion/missions/verify.py`. `grant_status` requires a valid `<root>/DEVIATIONS.md` for post-cutoff nodes.
- Modify: `src/telperion/cli.py`. `mission freeze` also writes the template if `DEVIATIONS.md` is missing. The template's
  body is the single line `none`, under a header comment that explains the format.
- Test: append.

**Rules:**
- After stripping the header comment block, which consists of lines starting with `<!--` through `-->`, plus blank lines,
  the content is either exactly one line equal to `none` (case-insensitive, trailing `.` allowed), or one or more lines
  matching `^- (\d{4}-\d{2}-\d{2}) \| (.+?) \| (.+)$`.
- Anything else raises `ValueError` with the offending line number. `N/A` or an empty body gets the hint "write `none`".

- [ ] **Step 1: Write the failing tests:**
  - `test_none_spellings`: `none`, `None`, `NONE.` are OK; `N/A` and an empty body raise with the hint;
  - `test_entries_parse`;
  - `test_bad_entry_line_number`;
  - `test_post_cutoff_grant_requires_ledger`: no file means `GateError` mentioning "DEVIATIONS.md", and the template means
    the grant passes;
  - `test_template_parses_as_none`.
- [ ] **Steps 2-4:** RED, then implement, then GREEN.
- [ ] **Step 5: Commit** with the message `missions: DEVIATIONS.md ledger ('none' or dated entries) required for new grants`.

---

### Task 4: The provenance-header lint

**Files:**
- Modify: `src/telperion/missions/process.py`, adding `ported_files(root) -> list[Path]` and
  `provenance_problems(root) -> list[str]`.
- Modify: `src/telperion/cli.py`, adding `telperion lint-provenance [DIR]`, which exits 1 on problems.
- Modify: `src/telperion/missions/verify.py`. `verify_campaign` includes `provenance_problems(root)` for post-cutoff
  campaigns, meaning those whose FREEZE.toml `frozen` date is on or after the cutoff.
- Test: append.

**Rules:**
- A file is "ported" if it is a `.lean` file whose first 30 lines match `(?i)\b(ported|adapted|copied) from\b` inside
  `--` or `/- -/` comments, or if it is listed in `<root>/PORTED.toml` (`files = [...]`).
- Each ported file must contain, in its first 30 lines, a line matching
  `^-- Provenance: repo=(\S+) file=(\S+) commit=([0-9a-f]{40})$`.
- A `PORTED.toml` entry that does not exist on disk is also a problem.

- [ ] **Step 1: Write the failing tests:**
  - `test_ported_without_header_flagged`;
  - `test_header_ok`;
  - `test_short_commit_rejected`, a 7-hex commit;
  - `test_late_mention_not_ported`, where line 200 says "adapted from" and the file is not flagged;
  - `test_ported_toml_listed_file_needs_header`;
  - `test_ported_toml_missing_file`;
  - `test_cli_exit_codes`.
- [ ] **Steps 2-4:** RED, then implement, then GREEN.
- [ ] **Step 5: Commit** with the message `lint: provenance headers on ported files (repo/file/commit)`.

---

### Task 5: An end-to-end dry-run mission, and the docs

**Files:**
- Create: `tests/test_process_e2e.py`
- Modify: `docs/MISSIONS_HOWTO.md`, adding a "Statement-first process" section covering init, freeze, the deviation
  ledger, the checks (step 4), grant, unfreeze, Audit.lean and the provenance lint. It notes that pre-cutoff campaigns are
  `pre-process`.

- [ ] **Step 1: Write the e2e test** on a tmp campaign, created through the CLI wherever a CLI exists:
  1. `mission add` a node created on 2026-10-29 with a trivial statement.
  2. Grant must fail with "frozen".
  3. Run `mission freeze`.
  4. Grant must fail on `[checks]` (step 4). Then write a passing `[checks]` record directly via the schema, with a
     PROBE_ONLY verdict carrying a `signoff:` note.
  5. Grant must now succeed, because `DEVIATIONS.md` is the template, `none`.
  6. Edit the statement. `verify` must fail with "statement drift".
  7. Run `mission unfreeze` with a distinct read-back. `verify` now passes on the freeze check.

  The test needs no Lean. Artifacts are text, and the gate's text checks apply.
- [ ] **Step 2:** Run it (GREEN, since every piece already exists from Tasks 1-4 and step 4).
- [ ] **Step 3:** Write the docs section.
- [ ] **Step 4: Commit** with the message `process: end-to-end dry-run mission test; MISSIONS_HOWTO statement-first section`.

---

## Amendment, 2026-10-30: step 4 carry-overs (Tasks 6 and 7)

The step 4 final review (ledger `.superpowers/sdd/2026-10-27-step4-checks/progress.md`, Rulings 16-18) left two
security items for this step. Both tie into the freeze, so they belong here. The owner accepted the closure-audit gap
for the step 4 merge only "until step 5" (decision of 2026-10-30).

### Task 6: The semantic statement tie (frozen statement fingerprints)

**Why.** Step 4 ties a `[checks]` record to the node's theorem by NAME, through the gate's syntactic resolver
(`guard_anchors.resolve_theorem`). Five known evasions predate step 4: `s!`-interpolated strings, a quote inside a
`«»` name, declaration text inside `«»`, `#exit`, and `(command| ...)` quotations. The sound fix is semantic. The
fingerprint of the checked theorem's TYPE must equal the frozen fingerprint of the node's `def … : Prop` statement,
which spec 7 already asks `mission freeze` to record.

**Files:**
- Modify: `src/telperion/checks/fingerprint.py`. Add a `value` mode that fingerprints a `def`'s VALUE instead of its
  type, with the same unfolding and the same library roots. A `theorem foo : Stmt` then fingerprints (type mode) to the
  same string as `Stmt` (value mode), because `Stmt` is a non-library constant and is unfolded.
- Modify: `src/telperion/missions/process.py`, adding `freeze --fingerprints`. When a Lean env is available, `freeze`
  and `unfreeze` record `[fingerprints] "<node>" = "<fp>"` beside `[statements]`, computed from the replayed statement
  module in value mode. Without one they record nothing, and the gate then refuses post-cutoff grants with "statement
  fingerprint not frozen".
- Modify: `src/telperion/missions/provenance.py` (`checks_problem`) and `cli.py` (`checks-record`). For post-cutoff
  nodes, the fingerprint JSON's fingerprint for the target must equal the frozen fingerprint. The name tie stays as a
  readable cross-check, but the fingerprint equality is what makes it sound. Update the `checks_problem` docstring and
  the HOWTO "theorem tie is syntactic" bullet: post-freeze, the tie is semantic.

**Interfaces:**
- `run_fingerprint(..., mode: Literal["type", "value"] = "type")`
- `process.frozen_fingerprint(root, node) -> str | None`

**Tests:**
- pure: the gate refuses a mismatched fingerprint, refuses a missing frozen fingerprint for a post-cutoff node, and
  passes on equality;
- Lean env:
  - `def S : Prop := ∀ n : ℕ, n + 0 = n` with `theorem t : S` gives equal fingerprints;
  - `theorem t' : ∀ n : ℕ, n + 0 = n` (the statement inlined) gives equal fingerprints too;
  - a helper with a different type gives a different fingerprint;
  - each of the five evasion artifacts from step 4's final re-review (`final-rereview.md`), with a decoy helper, is
    REFUSED at checks-record, because the fingerprints differ.

**Commit:** `missions: [checks] tied to the frozen statement fingerprint (semantic theorem tie)`

### Task 7: The closure audit as a replay callback

**Why.** `audit-closure` runs `lake env lean` on a script that imports the submission. That executes the submission's
initializers and elaborators, and also its `lakefile`. Its PASS can therefore be forged. This contradicts the owner's
"Replay-isolate" rule, and it is the gap the owner accepted until step 5.

**Files:**
- Modify: `src/telperion/closure_audit.py`. Add `render_audit_callback(spec, nonce) -> str`: the same closure walk
  (`closureOf`, scan patterns, absent constants and module prefixes, allowed axioms, recursors) written as a
  `TelperionReplay.callback`, emitting the same nonce-tagged lines. Add
  `run_closure_audit_replayed(spec, project, *, trusted_env, manifest, wrapper, timeout, memory_mb) -> AuditResult`.
  It goes through `lean_replay`, so it gets the trusted imports only, the private closure copies, the kernel replay,
  refused untrusted axioms, the olean sha binding and no lake.
- Modify: `cli.py`. `audit-closure` uses the replayed path by default. The old import path stays only behind
  `--legacy-import`, which prints a NOT-ISOLATED warning and is refused by `checks-record` for post-cutoff nodes.
- Modify: `checks-record` and `checks_problem`. The closure JSON must carry `olean_sha256` equal to the probe's and the
  fingerprint's. The three checks then run on ONE replayed closure. The interim I3 axiom cross-check stays, as a second
  line.
- Docs: remove the "closure audit imports the submission" limitation, the owner-accepted gap, from the HOWTO and the spec
  amendment, and record that it was closed in step 5.

**Tests:**
- pure: render, parse and gate wiring;
- Lean env:
  - parity: on a clean module, the replayed audit agrees with the legacy audit, with the same closure and axioms;
  - the step 4 evil modules (initialize / command_elab / tactic override) cannot change the replayed audit's verdict;
  - a module whose PASS the legacy path could forge is caught by the replayed path, so it must FAIL;
  - `sorryAx` and an untrusted axiom are refused.

**Commit:** `closure audit: run as a kernel-replay callback (no import of the submission)`

**Ordering.** Do Tasks 1-5 as written, then Task 7, then Task 6. Task 6 needs the freeze, and it is easiest to test
once all three checks run on one replayed closure. The owner's open step 5 decision on witnessing over a reducing
telescope (step 4's C2 residual) is NOT in this plan. Raise it at the final review.
