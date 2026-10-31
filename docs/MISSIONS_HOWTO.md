# Telperion Missions Registry — Quick Start

The missions registry tracks proof campaigns (BG, RH) as directed graphs of nodes with status, artifact links, claims, and work history. This HOWTO covers the essentials for picking up work in an active campaign.

## Status Machine

Every node flows through statuses enforced by the kernel:

```
draft ──(read-back recorded)──────────────> open
open ──(verified artifact linked)─────────> proved | refuted
any ──(with deprecated_reason)────────────> deprecated
```

**Key rule:** `proved` and `refuted` are **granted only by the kernel** via `mission grant` (which checks artifact existence and normalized statement containment — a syntactic, local gate). A node may link an artifact, but until the gate verifies the statement match, the status stays unchanged. The KERNEL authority for whether the artifact's Lean proof actually elaborates is the artifact's home package's own CI (e.g. proof-lean for BG; the home island for RH cross-island nodes); `mission grant` does not re-run that build. Pass `--deep-lean` to `mission verify` to lake-build the campaign's statement package (statements elaborate; proofs are not re-checked here). For reductions (proofs that import sorry-statements of other open nodes), the flag `closure_clean: false` until the entire import closure is sorry-free.

## Claims & the Claim Protocol

A claim reserves a node for one session for a TTL (default: 24 hours). Claims are **advisory, not locks** — they coordinate work but don't block other sessions. An expired claim can be claimed-over; the new claim records that it superseded the old one.

- **Claim:** `telperion mission claim <node-slug> --session <your-session-name> [--ttl 24] [--note "intent"]`
- **Release:** `telperion mission release <node-slug> --session <your-session-name>`
- **Check status:** `telperion mission open-leaves` (hides claimed nodes by default; use `--all` to show them)

## The Verbs

| Verb | Purpose |
|------|---------|
| `status [campaign]` | Print one-glance tree: all nodes with status, closure_clean flags, who claimed them |
| `open-leaves [campaign] [--all]` | List nodes ready to work on: open, all dependencies proved, not freshly claimed (or include them with `--all`) |
| `claim <slug> --session S` | Claim a node; TTL default 24h |
| `release <slug> --session S` | Release a claim |
| `add <campaign> <name> --session S` | Scaffold a new node (creates both .toml and statement file in draft status) and record you as its author (`[author]`: git email + session; both required) |
| `audit <slug> --text "..." --session S` | Record an INDEPENDENT read-back and promote draft → open. Refused if your session or git identity is the node's author, if the text is under 120 characters, or if it only repeats the title. `--auditor` is a display label only |
| `link <slug> --artifact P --kind K --via V` | Attach a proof/disproof artifact (K: `lean_module` or `frozen_cert`; V: `direct` or `reduction`) |
| `attempt <slug> --session S --route R --verdict V --detail D` | Log a work attempt; verdict: `Proved`, `Refuted`, `NoGo`, `Stalled` |
| `grant <slug> --session S` | **Gate verb:** run the verify gate and flip `proved`/`refuted` (only verb that changes status); writes `[grant]` with the artifact/statement digests, gate version and who ran it |
| `provenance-report [campaign]` | Proved nodes whose read-back is not known-independent and that no passing Comparator run covers |
| `comparator-record <slug> --run-id N --theorem T` | Record a PASSING `missions-comparator` run on a proved node (sidecar; never a status change) |
| `checks-record <slug> --campaign C --probe-json F --closure-json F --fingerprint-json F` | Record the negation probe, closure audit and statement fingerprint for the node's artifact, read from the checks' own JSON output. A node created on or after 2026-10-28 (or with no `created` date) cannot be granted `proved` without a passing record; see [Checks before grant](#checks-before-grant) |
| `ci-record <slug> --workflow W --job J --run-id N` | Record a run of a named non-required CI job on the node's CURRENT artifact (head sha + conclusion from `gh run view`, or `--head-sha`/`--conclusion`). A node with `requires_ci_job = "W:J"` cannot be granted, and fails `verify` once proved, without a `success` record on the current artifact digest |
| `freeze <campaign> [--fingerprints]` | Record a campaign-level statement freeze (`FREEZE.toml`) and write the `DEVIATIONS.md` template if there isn't one yet. With `--fingerprints` (needs the pinned Lean env) it also records every node's statement fingerprint, which a post-cutoff `[checks]` record must match. A post-cutoff node cannot be granted until its campaign is frozen AND the freeze is committed; see [Statement-first process](#statement-first-process) |
| `unfreeze <campaign> --author A --reason R --readback-identity I [--fingerprints]` | Bump a frozen campaign's hashes to the current statements, with a recorded, independently read-back reason (`--readback-identity` must differ from `--author`); `--fingerprints` re-records the statement fingerprints for the new version (none are carried forward) |
| `deviations-readback <campaign>` | Record an independent read-back of `DEVIATIONS.md` (the ledger's sha256 plus who read it and when); required, from an identity/session distinct from a node's own `[author]`, before that node can be granted post-cutoff |
| `audit-file <campaign>` | Write `<campaign>/lean/Audit.lean`: one `import` per proved node's artifact module, then one `#print axioms <theorem>` per proved node |
| `audit-crosscheck --print-axioms-out F --closure-json F` | Cross-check a captured `lake env lean Audit.lean` transcript against a closure audit's per-target axiom lists |
| `verify [campaign]` | Run the shallow coherence battery locally (node schema, DAG acyclicity, artifact existence, normalized statement containment, the campaign freeze and its git history) — read-only; add `--deep-lean` to also lake-build the campaign's statement package |
| `graph [campaign]` | Emit DOT export of the dependency DAG with node statuses |

One more verb lives outside `mission` (it operates on a campaign directory directly, not through `--missions-root`):
`telperion lint-provenance <campaign-root>`, the provenance header lint (spec 7.4). See
[Statement-first process](#statement-first-process).

## Five-Minute Quickstart

1. **Check the frontier:**
   ```bash
   telperion mission status demo
   telperion mission open-leaves demo
   ```

2. **Claim work:**
   ```bash
   telperion mission claim node_slug --session your-session-id
   ```

3. **Do the math.** Edit your local branch, write Lean, build, verify kernel checks.

4. **Log the attempt (always):**
   ```bash
   telperion mission attempt node_slug --session your-session-id \
     --route "emitter_name or tactic_approach" \
     --verdict Proved --detail "artifact path or summary"
   ```

5. **Link the artifact (if proved/refuted):**
   ```bash
   telperion mission link node_slug --artifact path/to/proof.lean \
     --kind lean_module --via direct
   ```

6. **Grant the status (invoke the gate):**
   ```bash
   telperion mission grant node_slug
   ```
   The gate checks: artifact exists and its normalized content contains the registry statement (syntactic, local — no Lean build). If both pass, status flips to `proved` (or `refuted` for disproofs). The KERNEL authority for the proof's elaboration is the artifact's home package CI, not this gate. If closure_clean was false (reduction), it's recomputed.
   For a node created on or after 2026-10-28, run the checks and `mission checks-record` first (next section); without a passing `[checks]` record the gate refuses `proved`.

7. **Release the claim:**
   ```bash
   telperion mission release node_slug --session your-session-id
   ```

## Checks before grant

Since 2026-10-28, a node does not become `proved` just because its artifact contains the statement and its home package
builds. It also needs a `[checks]` record: the output of three Lean checks, run on the artifact as it is now, written
into the node by `mission checks-record`. This section explains what those checks are, what they can and cannot tell
you, how to run them, and where their protection stops. It is long because the limits matter as much as the checks do.

### Why these checks exist

The grant gate has always been a containment test: does the artifact contain the statement the registry holds? That says
nothing about whether the statement means what everyone thinks it means. A node can pass that test and still be
worthless in a few ways:
- its hypotheses contradict each other, so it proves something about nothing;
- its conclusion is simply false, and the proof only "works" because of a `sorry` somewhere upstream;
- a definition it mentions was quietly shadowed or changed, so the same text now says something else;
- its proof leans on a constant or an axiom that it should never touch.

The checks are cheap, mechanical attempts to catch each of those before a node is granted. None of them is proof that a
statement is right. They are tripwires, and the verdict names below are chosen so that none of them claims more than it
saw.

### The four checks

Spec 5.2 names four checks. Three of them feed the `[checks]` record; the fourth is a classification in the Lean
verifier.

1. **The negation probe** (`telperion probe-negation`, `src/telperion/checks/negation_probe.py`). The target must be a
   THEOREM (a `def` or anything else is ERROR). The probe opens its elaborated type, first unfolding every NON-library
   definition at the head of the statement and of each ∀-body (so `theorem foo : Stmt` with `def Stmt : Prop := ...`
   is probed as what `Stmt` says), and tries three things, each with its own budget of 200000 heartbeats:
   - `false`: prove `False` from the premises alone, with a fixed tactic battery. A closed, kernel-checked proof with
     only the standard axioms means the hypotheses contradict each other: **VACUOUS**.
   - `negation`: ask plausible for a counterexample (`Plausible.Testable.checkIO`, seed 271828). A counterexample means
     the statement is false: **REFUTED**.
   - `witness`: only if you pass `--witness`. Your term must prove that every antecedent of the statement can hold at
     once (the ∃-closure of the full ∀-telescope of the unfolded type, conclusion arrows included). If it elaborates,
     the KERNEL accepts it (checked before the result is printed) and it uses only the standard axioms:
     **WITNESSED**. A statement with no Prop-typed antecedent at all (`True`, a bare conjunction) has nothing to
     witness, and gives PROBE_ONLY with a note instead. A vacuous part nested under any other conclusion head (`id`,
     `∧`, `¬`, a local structure, ...) is NOT seen by the witness; see the limitations below.
   - The witness is TRUSTED input: it is elaborated with the full elaborator inside the check process, so a term like
     `by run_tac ...` can do arbitrary IO there and forge result lines. Write it yourself, and never paste one from a
     submission unread.
2. **The statement fingerprint** (`telperion fingerprint`, `src/telperion/checks/fingerprint.py`). A sha256 of what the
   theorem's type says after every non-library definition has been unfolded (`deltaExpand`). It is serialized
   structurally, so renaming a bound variable or a universe parameter keeps the hash, while a shadowed or edited local
   definition changes it. It refuses (exit 2) whenever it would otherwise have to hash something by its name alone:
   for example a local inductive, structure, opaque or axiom left after unfolding, or a `sorryAx` in the statement.
3. **The closure audit** (`telperion audit-closure`, `src/telperion/closure_audit.py`). A Lean metaprogram that walks
   the theorem's whole constant closure, run on the kernel-replayed module like the other two checks. It fails on a
   forbidden constant (by default `sorryAx`), on a forbidden module prefix, on an axiom outside `propext`,
   `Quot.sound` and `Classical.choice`, or on a missing target.
4. **The kernel-rejection verdict** (`telperion.verify`). When the verifier runs Lean, an error block whose first line
   starts with the `(kernel)` prefix is reported as `KERNEL_REJECTED`, separately from an ordinary elaboration failure
   (`VerifyResult.kernel_rejected` and the `KERNEL_REJECTED` tag in `VerifyResult.summary()`). It goes by that prefix
   only: an error that merely sounds like a kernel error is not counted as one, on purpose. This check is not part of
   the `[checks]` record and is not a grant condition; it makes kernel rejections visible wherever `verify_lean` is
   used.

### The threat model: replay isolation

The obvious way to probe a theorem is to write a small Lean file that says `import TheirModule` and then poke at the
theorem. That turned out to be unsafe, and the reason shapes everything else here. Importing a module runs its code:
its `initialize` blocks run at import time, and its `@[command_elab]`, `@[tactic]` and macro registrations then
elaborate the check's own commands. A security re-review wrote a module that read the check's secret per-run tag out of
the check's own source and printed forged result lines, turning a vacuous theorem into WITNESSED and a true one into
REFUTED. No output filter helps against code that runs in the same process.

So the owner's decision ("Replay-isolate") is that **no check imports the untrusted module**: not the probe, not the
fingerprint, and (since step 5) not the closure audit. Instead, `src/telperion/checks/lean_replay.py` does what
Comparator and lean4checker do:
- the Lean process imports TRUSTED modules only (Mathlib and the toolchain's own libraries, from a pinned env), with a
  `LEAN_PATH` of trusted directories only, so no `import` can reach a submitted `.olean`;
- it reads the untrusted module and its untrusted imports as DATA, from private copies, without running anything;
- it adds their constants one by one through the kernel (`Lean.Environment.addDeclCore` with the kernel check on), so
  every declaration is type-checked again, and refuses the whole run on any rejection;
- only then does the check itself run, as a callback, in that replayed environment.

What does not come across is just as important. Replay transfers constants only: no initializers, elaborators, macros,
syntax, attributes, instances, simp lemmas or notation from the untrusted modules. So no untrusted code with effects
runs in the check's process. The price is that a probe can only get WEAKER (a tactic that needed the module's own
instance or simp lemma simply fails), which shows up as PROBE_ONLY, never as a false verdict. The fingerprint hashes the
kernel's terms, so it is not affected at all.

The negation probe still has to evaluate the statement to test it. It does that only through compiled TRUSTED code
(plausible's, inside Mathlib). A replayed definition has no compiled code at all, and a statement that would need it
is reported as PROBE_ONLY with a note, never REFUTED.

Until step 5, one check was NOT isolated this way: the closure audit. `audit-closure` ran `lake env lean` in the
submission's project on a script that imported its modules, so the project's lakefile and the modules' initializers
and elaborators ran inside the audit. A module that replaces `#eval` can read the audit's per-run tag out of the
script and print a forged PASS for a theorem proved by `sorry` (`tests/test_closure_audit_replay.py` builds exactly
that module and shows it). The owner accepted that gap for the step 4 merge (2026-10-30), and **it was closed in
step 5**: the closure audit's walk now runs as a replay callback, so the submission's code never runs in the audit
process (its `.olean` bytes are still read there; see the limitations), an `axiom` in its closure is refused by the
replay (an audit FAIL that names it), and the audit's JSON says `"isolated": true` and carries the same
`olean_sha256` as the other two checks.

The old path is still there as `audit-closure --legacy-import`, for comparing against old records and for projects
outside a pinned env. It is NOT isolated: it prints a warning saying so, its JSON says `"isolated": false`, and
`checks-record` refuses it for any node created on or after the cutoff.

### The trusted manifest

Replay isolation moves all the trust onto the pinned env: its `lean` binary, the toolchain's `lib/lean`, and the built
packages under `<env>/.lake/packages/*/.lake/build/lib/lean`. If someone could swap one of those files, they would be
back inside the check. So before every run the checks compare those files against a sha256 manifest, and any changed,
added or removed file (or a different toolchain, binary or prefix list) refuses the run: ERROR from the probe, exit 2
from the fingerprint.

You build the manifest once, on the env as pinned:

```bash
telperion trusted-manifest build --env ~/telperion-tools/lean-env
telperion trusted-manifest verify --env ~/telperion-tools/lean-env
```

- **Where it lives.** By default `$TELPERION_TRUSTED_MANIFEST`, else
  `~/telperion-tools/trusted-manifests/<sha256 of the env's lean-toolchain and lake-manifest.json>.json`. That is
  deliberately OUTSIDE the env, so that building in the env does not touch it. But it is protected only as far as the
  file system protects it: a build of a submission running as YOU can write `~/telperion-tools` like anything else of
  yours. The location is safe only under a sandbox, or when the checks run as a different user from the builds.
  `--out FILE` picks another path for both `build` and `verify`.
- **`--force`.** `build` refuses to overwrite an existing manifest (exit 2) unless you pass `--force`. Rebuilding is a
  statement that the env as it is now is the trusted one, so it is meant to be a deliberate act, not a side effect.
- **When to rebuild.** Only when you deliberately change the env (a new toolchain or Mathlib). If `verify` fails and you
  did not change anything, find out why before rebuilding.
- The probe, the fingerprint and the closure audit take `--trusted-env DIR` (default `$TELPERION_LEAN_ENV`) and
  `--trusted-manifest FILE` if you need to point at a non-default env or manifest. Nothing from `--project` is ever
  trusted.

### One closure, bound across all three checks

The probe, the fingerprint and the closure audit each report an `olean_sha256` in their JSON output, along with
`olean_closure`, the sorted list of `[module, part, sha256]` for every untrusted `.olean` file the replay read (the
whole untrusted import closure, every part of a `module` file). `olean_sha256` is the digest of that list. The replay
reads only private copies of those files and checks afterwards that it read exactly the copies and that they did not
change, so the digest names exactly the bytes the check saw.

`mission checks-record` refuses (exit 2) unless the probe JSON, the fingerprint JSON and the closure JSON carry the
SAME `olean_sha256`. That is how you know all three checks ran on the same build. Rebuild between the runs and the
record is refused; run them all again. The record stores `closure_isolated = true` to say the closure audit was one
of them, and the gate refuses a record without it.

The olean digest says which BUILD the checks saw. Both `--json` outputs also name the `module` and `theorem` they
checked (the fingerprint names them only when it was given exactly one `--import` and one `--target`), and
`source_sha256`, the sha256 of the file you passed as `--file` (or `null` with no `--file`). Be clear about what that
last one is: it is YOUR ASSERTION that this file is the source of the build, not a proof. Nothing shows that the
`.olean` was compiled from it, or even that it is the file for `--module`. The realistic failure is an honest one:
you edit the artifact, forget to rebuild, and run the checks on the old build with the new file. To catch that, the
probe and the fingerprint compare the `--file` with the module's built `.olean` (the one an import resolves in
`<project>/.lake/build/lib/lean` and the `--olean-dir` dirs): when the file is NEWER than the olean, the probe is
ERROR and the fingerprint exits 2 ("a stale build; rebuild"), and the JSON records both times (`source_mtime`,
`olean_mtime`, `stale`). That catches a forgotten rebuild, not an adversary (mtimes can be set). **Rebuild immediately
before running the checks.**

`checks-record` then insists on all of these, and refuses (exit 2) otherwise:
- the target is the node's REGISTERED theorem: the artifact declaration the grant gate matches against the node's
  statement (`guard_anchors.resolve_theorem`). A record for a helper lemma in the same file, or one copied from a
  sibling node, is refused, and so is a `--target` naming anything else. The grant gate and `mission verify` check the
  same thing, and also that the record's theorem is the Comparator record's, once there is one;
- the probe's `theorem` is that theorem, it is one of the closure audit's targets, and the fingerprint's `theorem`,
  when it names one, is the same;
- the closure JSON says `"isolated": true` (the kernel-replayed audit) and its `olean_sha256` is the probe's and the
  fingerprint's. For a node created on or after 2026-10-28, `audit-closure --legacy-import` output, or a closure JSON
  from before step 5 with no `isolated` key, is refused with a message saying why. For an older node it is recorded
  with `closure_isolated = false`;
- each `source_sha256` is PRESENT and equals the sha256 of the node's artifact as it is on disk NOW. There is no
  waiver: a JSON without one (a run without `--file`) is refused, so re-run the check with `--file`. (`--file` stays
  optional for interactive runs of the probe and the fingerprint.) A JSON that says `stale` is refused too;
- both JSONs carry the replay's axiom list (`axioms`, `collectAxioms` over every constant of the target module, which
  an imported module cannot forge, since the replay imports nothing untrusted). The two lists must be equal and a
  subset of `propext`, `Quot.sound` and `Classical.choice`, and they must include the closure audit's axioms for the
  target. The list is recorded, and the gate checks it again. This was the interim cross-check on the closure audit
  while it imported the submission; now that the audit is replayed too, it stays as a second line.

So **always run `probe-negation` and `fingerprint` with `--file` pointing at the node's artifact**, on a fresh build.

### What the verdicts mean

| Verdict | What happened | Effect on the grant |
|---|---|---|
| `WITNESSED` | Your `--witness` proved the antecedents jointly satisfiable (kernel-checked, standard axioms), and no counterexample was found | Passes |
| `PROBE_ONLY` | Nothing was found: no contradiction derived, no counterexample, no witness given (or it did not count). Notes say if a probe could not run, timed out, or hit the memory bound | Passes ONLY with a reviewer's `signoff: <who>` in the `--note` |
| `VACUOUS` | The premises alone prove `False` | Blocks |
| `REFUTED` | plausible found a counterexample | Blocks |
| `ERROR` | No verdict could be read: an unbuilt module ("build <module> first"), an unknown constant, a refused replay, a manifest mismatch, a witness that does not elaborate, a refused axiom | Blocks |

A few of these deserve a longer word.

**PROBE_ONLY is one-sided, and that is why it needs a sign-off.** The probe can show that something is wrong. It cannot
show that something is right. Failing to derive `False` with a tactic battery does not mean the hypotheses are
consistent, and plausible failing to find a counterexample does not mean the statement is true. So PROBE_ONLY is not a
pass on its own: a person has to look at the statement and say so, by putting `signoff: <who>` in the record's note.
The other way through is to give a witness, which turns "we found nothing" into positive evidence (WITNESSED). A
heartbeat timeout in any probe is also PROBE_ONLY with a note: it is inconclusive, never a verdict either way.

**Why REFUTED is value-based.** An earlier version decided REFUTED by looking for plausible's
`Found a counter-example!` in the printed output. Printed text can be forged by anything that can print. Now the probe
calls plausible's API directly and reads the `TestResult` VALUE it returns: REFUTED is the `failure` constructor of that
value, whose type carries a proof that the statement fails. Nothing a module prints can produce it. plausible's random
seed is fixed at 271828, and the REFUTED detail names it, so anyone can re-run the probe and get the same
counterexample.

**Untrusted axioms are refused (Ruling 10).** If any module in the untrusted closure declares an `axiom`, the replay
refuses it. The probe then reports ERROR naming the axiom, and the fingerprint refuses (exit 2). The point is that no
untrusted axiom ever enters an environment that tactics run in: an `axiom bad : False` in the submission would
otherwise be one `exact` away from a VACUOUS or a WITNESSED. A `sorry` is different. The probe accepts a theorem proved
by `sorry`, so you can probe a statement before you prove it, but the closure audit fails on `sorryAx` by default, so
such a record cannot pass.

**The closure verdict** is recorded as PASS only when the audit JSON says `"verdict": "PASS"` AND `"ok": true` (Lean
exited cleanly). Anything else, including no verdict at all, is recorded as FAIL, and FAIL blocks.

### The grant rule, the cutoff and the gate version

- **Who needs `[checks]`.** Every node whose `created` date is 2026-10-28 or later. A node with an EMPTY `created`, or
  one that does not parse as a date, is treated as needing them too (Ruling 2): otherwise a new node could skip every
  check just by leaving the field out. The WHOLE value must be a plain ISO date (Ruling 12): `2026-10-01junk` or a
  timestamp does not parse, so it requires checks. Only an explicit `created` before 2026-10-28 makes a node
  pre-process, and `mission provenance-report` counts those rather than listing them. If an old node has no `created`,
  add the real date before granting it.
- **Once required, always required.** When the gate grants a node that needs checks, it writes
  `checks_required = true` into the `[grant]` (Rulings 12 and 13). From then on the node needs checks whatever its
  `created` says, in `mission verify` and on any re-grant, so editing `created` to an earlier date after the grant
  does not drop the requirement. (The flag is written only when it is true, so older grants read back unchanged.)
- **What passes.** Probe `WITNESSED`, or `PROBE_ONLY` with `signoff:` in the note; closure `PASS`; and a record made on
  the artifact that is on disk NOW. The record stores the artifact's source sha256, and any edit to the artifact makes
  the record stale until you re-run the checks. (The `olean_sha256` is recorded for the reader but cannot be
  recomputed without a build, so it is not re-checked at grant time.)
- **Where it is enforced.** `mission grant` refuses `proved` without a passing record. `mission verify` re-checks the
  record on every `proved` node the rule covers, so a node that was granted and then had its artifact edited fails
  verify (Ruling 11). The rule applies to `proved` only: a refutation does not prove the statement, so the probe and the
  fingerprint have nothing to say about it.
- **`GATE_VERSION` is `2026-10-31.1`.** Every grant records the gate version that granted it, and grants made under
  an earlier version keep the version they were granted with, so you can always tell which rules a grant was held to.
  `2026-10-29.1` was the first that required `[checks]`. `2026-10-31.1` is step 5's single bump (Ruling 16), and for
  the same post-cutoff nodes it adds everything in [Statement-first process](#statement-first-process): a committed
  campaign freeze with a clean history, a `DEVIATIONS.md` ledger read back by someone other than the node's author, an
  `[author]` block, an isolated (kernel-replayed) closure audit, and a `[checks]` fingerprint equal to the node's
  frozen statement fingerprint. `checks_required = true` in `[grant]` means exactly what it did before.

### Running the checks, step by step

You need the pinned env (`TELPERION_LEAN_ENV`, built as in the step 4 plan: a bare Lake project requiring Mathlib
v4.35.0 on Lean v4.35.0, then `lake exe cache get`) and its trusted manifest. The submission's module must be BUILT in
its own project first (`lake build <Module>`), because the probe and the fingerprint read its `.olean`; neither one
builds it for you. The example uses a node `my_node` in campaign `demo` whose artifact module is `Demo.MyNode`,
declaring theorem `Demo.my_thm`.

1. **Negation probe.** `--module` is the theorem's own module; `--theorem` is its full name (or a short name, which
   `--file` qualifies with its namespace). Pass the node's artifact as `--file`: it is used to find the namespace and to
   compute `source_sha256`, never to read the statement. Add `--witness` if you can:
   ```bash
   telperion probe-negation --project path/to/project --module Demo.MyNode \
     --file path/to/project/Demo/MyNode.lean \
     --theorem Demo.my_thm --witness "⟨2, by norm_num, trivial⟩" --json > probe.json
   ```
   Exit 0 means PROBE_ONLY or WITNESSED, 1 means VACUOUS or REFUTED, 2 means ERROR. With `--json`, stdout is one object
   with `verdict`, `detail`, `module`, `theorem` and `source_sha256`, plus `olean_sha256`, `olean_closure` and
   `axioms` when the module was replayed and `source_mtime`, `olean_mtime` and `stale` when `--file` and a built
   olean were found, and it is written whatever the exit code. The theorem name must be a plain dotted identifier: a
   name qualified from `--file` is read with comments and string literals blanked, and anything that is not a plain
   identifier is ERROR, never spliced into the check. Other options: `--import MODULE` adds a trusted
   tactic module (default `Mathlib`), `--olean-dir DIR` adds another untrusted olean dir, `--memory-mb MB` sets
   Lean's `--memory` bound (default 8192, 0 for none), `--timeout` (default 1800 s), and `--wrapper` sets the command
   prefix before the pinned `lean` (default: leanlock with one slot when `~/hodge-engine/leanlock.sh` exists, nothing
   otherwise; `''` for none).
2. **Statement fingerprint**, on the same build:
   ```bash
   telperion fingerprint --project path/to/project --import Demo.MyNode \
     --target Demo.my_thm --file path/to/project/Demo/MyNode.lean --json > fingerprint.json
   ```
   Exit 0 when every target was fingerprinted, 2 otherwise. With `--json`, stdout is
   `{"fingerprints": {...}, "olean_sha256": ..., "olean_closure": [...], "module": ..., "theorem": ...,
   "source_sha256": ..., "axioms": [...]}` (plus `source_mtime`, `olean_mtime` and `stale` as for the probe), or
   `{"error": ...}`, and it also carries `"mode"`. Here `--file` is only hashed, into `source_sha256`. The default
   `--mode type` hashes the target's TYPE, which is what you want for the artifact's theorem; `--mode value` hashes a
   `def … : Prop`'s VALUE instead (what the freeze records for a statement written as a definition), and
   `checks-record` refuses a value-mode JSON. It takes the same
   `--trusted-env`, `--trusted-manifest`, `--olean-dir`, `--memory-mb`, `--wrapper` and `--timeout` options. The project
   (outside `.lake` and `.git`) must contain no symlink and no directory or `.lean` file named after a library root.
3. **Closure audit**, on the same build. Note that `--json` takes a FILE here, unlike the other two:
   ```bash
   telperion audit-closure --project path/to/project --import Demo.MyNode \
     --target Demo.my_thm --json closure.json
   ```
   Exit 0 PASS, 1 FAIL, 2 when the audit could not run (an unbuilt module, no trusted env or manifest, a Lean crash).
   It replays `--import` like the probe does (an import that resolves to a trusted `.olean` of the pinned env is
   imported instead), so pass the node's OWN module, the one the probe and the fingerprint replayed: a different set
   of modules is a different `olean_sha256`, and `checks-record` refuses the mismatch. It takes the same
   `--trusted-env`, `--trusted-manifest`, `--olean-dir`, `--memory-mb`, `--wrapper` and `--timeout` options. The JSON
   is the old shape plus `isolated`, `olean_sha256` and `olean_closure`. An untrusted axiom in the closure is a FAIL
   naming it. `--legacy-import` runs the old import-based script instead (NOT isolated, see above).
4. **Record them:**
   ```bash
   telperion mission checks-record my_node --campaign demo \
     --probe-json probe.json --closure-json closure.json --fingerprint-json fingerprint.json \
     --note "signoff: <reviewer> read the statement; hypotheses are satisfiable by inspection"
   ```
   Every verdict is read from those JSON files, never from a flag. They are unsigned files you produced: reading the
   verdicts from them guards against mistakes, not against an operator who writes them by hand. It refuses (exit 2,
   nothing written) on an unreadable or malformed JSON, an unknown probe verdict, a missing or mismatched
   `olean_sha256` (the closure JSON's included), a closure JSON that is not isolated for a node that needs checks, a
   target that is not the node's registered theorem, a fingerprint that is not the node's frozen statement
   fingerprint (or no frozen fingerprint at all) for a node that needs checks, a value-mode fingerprint JSON, a
   fingerprinted theorem that the closure audit did not audit, a probe of a different theorem, a `source_sha256` that is absent or not the artifact's current
   sha256, a stale build, missing, unequal or non-standard replay `axioms`, a missing artifact, or a node that is
   `deprecated` or `refuted`. Otherwise it writes
   the record and exits 0 if it passes, 1 if it does not (VACUOUS, or PROBE_ONLY with no sign-off, for example). It
   never changes the node's status; `mission grant` does that.

### Limitations, stated plainly

These are real, and you should know them before you rely on a `[checks]` record.

- **The checks are NOT A SANDBOX.** Replay isolation keeps the submission's code out of the CHECK process. It does
  nothing about building the submission, which you must do first: `lake build` runs the project's lakefile and the
  modules' compile-time code (`#eval`, `initialize`, macros) with YOUR permissions. That code can read or rewrite any
  file you can, including the trusted env (the manifest only catches tampering done before the check starts), open
  network connections, or start a daemon. The same goes for `audit-closure --legacy-import`, which imports the
  submission, and for fingerprinting submitted text (`run_fingerprint_on_text` compiles it). **Untrusted submissions must be built and
  checked inside a sandbox**, for example Comparator's sandbox on Linux CI (whose bwrap shim must pass
  `--cap-drop ALL`; see `docs/COMPARATOR.md`). Outside one, run these checks only on code you would be willing to run
  anyway.
- **The `.olean` reader trusts bytes.** Lean maps an `.olean` into memory as an image of its data structures. The
  replay re-checks every declaration in the kernel, but a deliberately malformed file is an attack on the memory
  safety of the reading process itself, which no kernel check comes after. Another reason for the sandbox.
- **The memory limit is best-effort.** The checks pass `--memory=<MB>` to Lean (default 8192), Lean's own allocation
  bound. It is not an operating-system limit. Inside a probe, hitting it is a probe failure (PROBE_ONLY with a note, or
  ERROR for the witness probe); in the replay itself it is ERROR.
- **The sign-off is free text.** `signoff: <who>` is a string in the note, written by whoever runs `checks-record`.
  Nothing checks that the reviewer is a different person or session from the author. Treat it as an honest
  declaration, and keep the read-back discipline below in mind: a self sign-off is no better than a self-audit.
- **The closure audit's import gap is closed (step 5).** Through step 4, `audit-closure` imported the submission, so an
  imported module could forge its output; the owner accepted that gap for the step 4 merge (2026-10-30). It now runs
  as a kernel-replay callback on the same replayed closure as the probe and the fingerprint (same `olean_sha256`), and
  the gate requires `closure_isolated`. What is left is what is left for every replayed check: the build itself and
  the `.olean` reader (the two bullets above). `audit-closure --legacy-import` keeps the old, NOT isolated path; its
  output is refused for nodes created on or after the cutoff. The replay axiom cross-check (the probe's and the
  fingerprint's `axioms` must be standard and include the closure audit's) stays as a second line.
- **The theorem tie is semantic for frozen campaigns (frozen statement fingerprint); the name resolver remains a
  readable cross-check.** For a node that needs checks, `checks-record` and the gate require the checked theorem's
  fingerprint to EQUAL the node's frozen statement fingerprint, the one `mission freeze --fingerprints` recorded in
  `FREEZE.toml`, and they refuse a node that has none ("statement fingerprint not frozen"). The gate's syntactic
  resolver (`guard_anchors.resolve_theorem`) still has to name the theorem too, and it still has known blind spots,
  all of which predate step 4: `s!`-interpolated strings, quotes inside `«»` names, declaration text inside `«»`,
  `#exit`, and `(command| ...)` quotations. Each of them makes the resolver name a decoy, and the decoy's statement
  is not the frozen one, so its fingerprint differs and the record is refused (`tests/test_statement_tie_lean.py`
  builds all five). What is left is what the fingerprint itself cannot see: two declarations that state the same
  thing are interchangeable here, by design, and the frozen fingerprint is only as trustworthy as whoever froze the
  campaign (see [Statement fingerprints in the freeze](#statement-fingerprints-in-the-freeze)).
- **The node file can be hand-edited.** The cutoff keys on `created`, and nothing guards that field while a node is
  still unproved: a node back-dated to before 2026-10-28 before its first grant is granted without checks. Deleting
  `checks_required` from a `[grant]` together with back-dating `created` is the same class of hand edit, with the same
  effect on a re-grant. Once a grant has recorded `checks_required = true` and the file is left alone, the
  requirement holds whatever `created` says. Review any diff that changes an existing `created` or removes
  `checks_required`; a CI check for both is planned for step 5.
- **A conclusion with NAMED ∀ binders reads as premises.** `theorem t : ∀ (m : ℕ) (h : m < 0), False` is probed as if
  `m` and `h` were hypotheses, so the false probe proves `False` from `h` and reports VACUOUS for what is really a
  true statement about the conclusion. That fails closed (VACUOUS blocks the grant), but it blocks a good node. The
  workaround: write the conclusion with arrows (`∀ m : ℕ, m < 0 → False`). The premise split then stops at the arrow,
  so `m < 0` stays in the conclusion. (Restating the binders as hypotheses, `(m : ℕ) (h : m < 0) : False`, does NOT
  help: they are then premises by construction, and the probe reads exactly the same thing. Use that form only for
  binders that really are meant as hypotheses.)
- **Vacuity nested under a closed head is not seen by the witness.** The probe unfolds only NON-library definitions,
  and only at the head of the statement and of each ∀-body. Under any other conclusion head, the ∃-closure the
  witness must prove stops: a library definition such as `id`, a local `structure`, `∧`, `↔`, `¬`, a beta-redex or a
  `let`. So `∀ m : ℕ, m = m → id (∀ n : ℕ, n < 0 → n = 7)` is vacuously true, yet the witness `⟨0, rfl, trivial⟩`
  satisfies the pad `m = m` and gives WITNESSED, without a sign-off. Read the conclusion of any WITNESSED statement
  for a hidden vacuous part. Witnessing over a reducing telescope instead is a step-5 decision.

### In CI

The `lean-checks` job, in its own workflow `.github/workflows/lean-checks.yml`, builds the same pinned env on a Linux
runner (Lean v4.35.0, Mathlib v4.35.0 at `56a005855ea17e0b0958f73ec801ae140b0a1679`, `lake exe cache get`), builds its
trusted manifest with `trusted-manifest build` into a path outside the env, checks that `verify` accepts it and that a
second `build` without `--force` refuses, and then runs `tests/test_negation_probe.py`, `tests/test_fingerprint.py`,
`tests/test_lean_replay.py`, `tests/test_closure_audit_replay.py` and `tests/test_statement_tie_lean.py` with
`TELPERION_LEAN_ENV` set, one step per file. Those files hold the must-fail controls (the evil-module cases, a shadowed
definition, a vacuous and a refuted statement, a declared axiom, a lemma the kernel never checked, the five resolver
evasions and the freeze-side attack chain), and they skip without an env, so a step fails if any of its tests is
skipped. It first checks that the runner has at least
10 GB free, so a full disk fails in seconds rather than an hour in. There is no leanlock on the runner and none is
needed: the default wrapper is used only when `~/hodge-engine/leanlock.sh` exists. The CI runner is still not a sandbox
for third-party submissions; it runs only this repository's own test modules.

A full run builds Mathlib's env and takes a long time, so it does not run on every push. It runs when you start it by
hand (workflow_dispatch), once a week on a schedule, and on a push or pull request that touches `src/telperion/checks/`,
`src/telperion/missions/`, `src/telperion/closure_audit.py` or `src/telperion/comparator.py` (both imported by the
checks), the three test files above, `tests/test_missions_checks.py`, the test helpers `tests/lean_env.py` and
`tests/fake_lean_cli.py`, or the workflow file itself. The weekly run is the backstop: a new runner image, or anything
else outside those paths, can break the controls without touching them, and a path filter would never notice.

## Statement-first process

Spec 7 adds a second layer on top of "checks before grant": the campaign's statements themselves are frozen, and any
departure from an informal source is written down and read back, before a post-cutoff node can be granted. Where the
checks above ask "does this artifact actually prove what it claims?", this section asks "is the claim itself the one
everyone agreed to, and did anyone sanity-check the paper trail?" Both layers gate the same thing (`grant`), and both
are scoped by the same predicate, `provenance.checks_required`: a node is in scope once its `created` date is on or
after 2026-10-28, or has no `created` date at all (fail-closed). A campaign that predates all of this — every node in
it created before the cutoff — is `pre-process`: `mission verify`'s freeze check, the deviation ledger, and the
provenance lint simply have nothing to say about it, and `mission provenance-report` prints that label for it rather
than silently passing it off as compliant.

The whole shape, end to end, on one node: `add` (writes `[author]`) → `audit` (independent read-back, draft → open) →
`freeze --fingerprints` the campaign and commit it → `link` (attach the artifact) → `checks-record` (the step-4
checks, which for a post-cutoff node must match the frozen statement fingerprint, so the freeze comes first) → write
and read back `DEVIATIONS.md` → `grant`. `tests/test_process_e2e.py` runs exactly this on a synthetic campaign and is the
easiest way to see every message the gate actually raises, in the order it actually raises them.

### Freezing a campaign, and committing it

`telperion mission freeze <campaign> [--identity I] [--session S]` writes `<campaign>/FREEZE.toml`: a version number
(1, the first time), who froze it, and the sha256 of every node's current statement body. From then on, a post-cutoff
node cannot be granted `proved` unless its statement's hash still matches what FREEZE.toml recorded — the freeze is
what makes a later edit to a statement *visible* as drift, rather than just a silent change nobody has to answer for.
`freeze` also writes `DEVIATIONS.md` from a template if the campaign does not have one yet (see below), so a freshly
frozen campaign is never one file short of being grantable.

**Commit it.** `mission freeze` only writes the file; it does not commit it, and a post-cutoff grant needs the freeze
to be committed. The reason is `freeze_history_problems` (`process.py`): on every grant and on every `verify`, the
campaign's git history for `FREEZE.toml` is walked and checked for the shape a legitimate `freeze`/`unfreeze` sequence
always has — version numbers that only go up, one `[[unfreeze]]` entry per version bump, no self-read-back
`[[unfreeze]]` entry, the file never deleted or symlinked along the way. An uncommitted `FREEZE.toml` has no history to
check at all, so inside a git repository it is refused outright for a post-cutoff campaign; outside one it is refused
too (there is nothing to anchor the freeze to). Commit with an explicit identity rather than depending on whatever the
ambient git config happens to be:

```bash
telperion mission freeze demo
git -C missions/demo add FREEZE.toml DEVIATIONS.md
git -C missions/demo commit -m "freeze demo campaign"
```

If a statement changes after the freeze, `mission freeze` itself refuses to run again (it would silently throw away
the unfreeze history) — use `unfreeze` instead:

```bash
telperion mission unfreeze demo --author you@example.com --reason "why the statement moved" \
    --readback-identity someone-else@example.com
git -C missions/demo add FREEZE.toml
git -C missions/demo commit -m "unfreeze demo campaign: <reason>"
```

`unfreeze` re-hashes every current statement, bumps the version, and appends an `[[unfreeze]]` entry recording who
asked for the change, why, and who read the new hashes back before they were recorded. `--readback-identity` must
differ from `--author` — refused otherwise, the same "testimony from a different principal" rule as the node read-back
above — and that read-back identity has nothing to do with any node's own `[author]`; it is independence of the
*freeze bump itself*, a campaign-level fact, not a per-node one. Forget to commit the unfreeze and `verify` keeps
reporting the old drift: the working tree has the new hash, but the history walk a post-cutoff grant and `verify` both
run sees only what git has recorded.

### Statement fingerprints in the freeze

A statement hash says the statement FILE has not changed. It says nothing about which declaration in an artifact
proves that statement, and up to step 4 the gate answered that question by reading the artifact's text
(`guard_anchors.resolve_theorem`), which an adversarial artifact can fool. So the freeze can also record what each
statement SAYS, as Lean elaborates it: its fingerprint (the same sha256 `telperion fingerprint` computes, see
[The four checks](#the-four-checks)).

```bash
telperion mission freeze demo --fingerprints        # needs the pinned env: $TELPERION_LEAN_ENV, its trusted manifest
git -C missions/demo add FREEZE.toml DEVIATIONS.md
git -C missions/demo commit -m "freeze demo campaign"
```

That adds a `[fingerprints]` table beside `[statements]`, one `"<node>" = "<fingerprint>"` line per node, and a
`fingerprints_env` line naming the trusted env they were computed under (below). We chose an
explicit flag over "whenever a Lean env happens to be configured": a freeze is a one-way record, and what it contains
should not depend on which machine ran it. Without the flag nothing is recorded, the command says so, and every
post-cutoff `[checks]` record is refused until a freeze records them.

How each fingerprint is computed:
- **One statement constant per file.** A statement file declares exactly one: one `theorem` or `lemma`
  (`theorem foo : P := by sorry`, the form statement files have had so far), or, with none, one closed `def` or
  `abbrev … : Prop` (`def S : Prop := P`, the form spec 7 describes). Supporting definitions are fine as long as they
  are not themselves closed `Prop`s (`def bound : ℕ := 5`, `def Good (n : ℕ) : Prop := …`).
- **The textual choice.** The constant is read from the code, with comments and strings blanked by the gate's own
  lexer. In type mode it must be the theorem the gate reads as the node's statement (`guard_anchors.statement_decl`);
  in value mode the gate must find no theorem at all.
- **The statement-file grammar (a strict whitelist).** Read with the gate's own lexer, so comments and doc comments
  never trigger it:
  - every command starts a line, at column 0, with `import`, `namespace`, `end`, `section`, `open` (including
    `open scoped`), `universe`, `variable`, the statement (`theorem`/`lemma`, or `def`/`abbrev … : Prop`), or a
    supporting `def`, `abbrev`, `structure`, `inductive`, `class` or `noncomputable def`/`abbrev`/`section`;
  - anything else at a line start is refused, naming the line, and so is a command keyword anywhere else (mid-line,
    or on an indented line). Continuation lines of a multi-line declaration must be indented;
  - no string, raw-string or char literal anywhere. An interpolated `s!"{"…"}"` (or `m!`, `f!`, `throwError`,
    `dbg_trace`) can hide a whole `theorem` from every lexer but Lean's own;
  - none of: `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `notation`, `infix`/`infixl`/`infixr`, `prefix`,
    `postfix`, `declare_syntax_cat` (they can swallow a command or change what text means); `run_cmd`, `run_elab`,
    `run_meta`, `initialize`, `builtin_initialize`, and any `#` command (`#eval`, `#exit`, `#print`, ...) (they run
    code); `alias`, `export`, `attribute`, `deriving`, `instance`, `irreducible_def` (they generate declarations);
    `set_option`, `local`, `scoped` (other than `open scoped`), `private`, `protected`, `opaque`, `axiom`, `omit`,
    `include`; any attribute `@[…]`; any `«»` name; any backquote (a `` `( `` quotation or a name literal).
  Statement files come from `mission add`, so this costs nothing in practice: of the 123 node statement files in the
  campaigns written before step 5, 121 are inside it (the other two declare helper lemmas beside their theorem). The
  three campaign `…Defs.lean` modules are not node statement files and are not frozen.
- **The semantic choice, which is what decides.** The statement file is compiled as its own module with the pinned
  `lean` (no lake) and replayed into the pinned env like every other check. The replayed module must declare exactly
  the constant the text named, and nothing else that could be a statement: in type mode its only theorem (and no
  closed `Prop` definition), in value mode its only closed `Prop` definition (and no theorem). Theorems Lean generates
  that the text does not show must be accounted for: every constant the module declares must be named by a
  declaration in the text, or sit under one (a structure's `mk`, `rec`, `mk.injEq`; a definition's `match_1` or
  `proof_1`). Those auxiliaries are not statement constants. A generator the grammar did not know would show up here
  as an unaccounted name.
- **The declaration range.** Lean records, in the compiled statement `.olean`, the line and column each constant was
  declared at (`declRangeExt`). That record is read back as data, by a trusted script that imports only `Lean`, from
  the very olean that is then replayed (its sha256 is checked against the replay's copy), and the target's range must
  start at the textual declaration's line, column 0. So the frozen constant is the one the text declares, not one a
  generator made under the same name: an `alias main := …` records the alias's own line.
- **What is hashed.** The theorem is fingerprinted by its TYPE, that is `P`; the definition by its VALUE, which is `P`
  again. In both cases every non-library definition is unfolded first, so `theorem t : S`, `theorem t : P` and `S`
  itself all get the same fingerprint. Universe-polymorphic statements are included, with level parameters numbered
  by their position in each declaration's own list: `theorem t.{v} : S.{v}` matches `def S.{u}`, but an artifact that
  lists its universes in another order than the statement (`theorem t.{v, u} : S.{u, v}`) gets a different
  fingerprint and is refused. Declare them in the same order.
- The rest of the gate (the containment match and the name resolver) still expects a theorem-form statement, so a
  def-form node can be frozen this way but not yet granted.
- Imports of other campaign modules resolve from `<campaign>/lean/.lake/build/lib/lean`, or from `--olean-dir`.
- A statement that cannot be fingerprinted fails the whole freeze, and nothing is written: any refusal above, a local
  inductive or structure left after unfolding, or a `sorry` in the statement itself.
- It compiles the statement files, so it is NOT A SANDBOX either; they are the campaign's own files, but the same
  caution applies.

Then, for every node that needs checks, `checks-record` and the gate require the checked theorem's fingerprint (type
mode) to equal the frozen one. A mismatch reads "statement fingerprint mismatch"; no frozen fingerprint reads
"statement fingerprint not frozen". `checks-record` also requires the fingerprint JSON's `trusted_env_sha256` to be
the freeze's `fingerprints_env`, and refuses "fingerprint computed under a different trusted env" otherwise. `mission verify` re-checks it on every proved node, so moving a node's frozen
fingerprint later (an unfreeze that records a different one) makes its `[checks]` stop passing.

The history walk covers `[fingerprints]` with the same rules as `[statements]`: at an unchanged version a fingerprint
may not change or disappear, and one may be added only together with its node (a fingerprint appearing later for a
node that was already frozen is refused, because whoever adds it chooses what a later `[checks]` record must match).
Changing any of them takes a version bump, so `unfreeze --fingerprints`. `unfreeze` never carries fingerprints
forward: a fingerprint also depends on the definitions a statement imports, which the statement hash does not cover,
so each version records its own or none.

**The trusted env.** `fingerprints_env` and the JSON's `trusted_env_sha256` are a digest of the trusted manifest's
content (`lean_replay.trusted_env_digest`): the toolchain and every trusted file's sha256, keyed by its path inside
its package rather than by the absolute paths the manifest records, so the same pinned env gives the same digest on
any machine of the same platform. The trusted files include the platform's `lean` binary and its shared libraries, so
a macOS freeze and a Linux check get different digests, which fails closed ("different trusted env"): fingerprint the
artifact on the platform the campaign was frozen on. It is fixed for a version like the fingerprints are. Library constants are hashed by NAME, not unfolded,
so a Mathlib bump usually leaves a fingerprint unchanged; it changes one only where elaboration differs (an instance
path, a renamed lemma). That is exactly why the env is recorded: a freeze under one Mathlib and checks under another
would otherwise compare equal whenever the names happen to agree. After a bump, re-run the checks and `unfreeze
--fingerprints`.

**The freeze's own dates and history.** The `frozen` date may never change once committed, because it decides whether
the history checks fail closed at all. And for a post-cutoff node the gate requires the history to be available
whatever `frozen` says, so a back-dated freeze outside git, or in a shallow clone, is still refused.

What this does not protect: the grant cannot recompute a frozen fingerprint without Lean, so it takes FREEZE.toml's
word for it. Its trust is the freeze's trust: whoever froze the campaign, and the committed history after that (a CI
job that recomputes `[fingerprints]` is a tracked follow-up).

### The deviation ledger, and its read-back

`DEVIATIONS.md`, at the campaign root, records every place a formal statement departs from whatever informal source
motivated it — a missing side condition tightened into a hypothesis, a weaker conclusion than the original claim,
anything a reader of the informal statement would want flagged rather than discovered later. Its format is either the
single word `none` (case-insensitive, a trailing `.` allowed — the template `mission freeze` writes), or one or more
lines `- YYYY-MM-DD | what departs | why`. A bare `N/A` is refused with a pointed hint to write `none` instead:
"not applicable" and "I checked and there are none" are different claims, and the ledger should never leave which one
is meant to guesswork. A deviation dated in the future is refused too — a deviation is something that already
happened, not something scheduled.

Parsing the ledger is not the same as it being *read back*, and spec 7.3 asks for both: someone has to have actually
looked at the current ledger and said so. `telperion mission deviations-readback <campaign> --identity I --session S`
writes `DEVIATIONS.readback.toml`, recording the sha256 of the ledger's exact current bytes plus who read it and when.
A post-cutoff grant refuses without this file, refuses if the ledger has changed since the recorded sha256 (read it
back again), and refuses if the read-back's identity or session matches the node's own `[author]` — the same
self-audit comparison the node-level read-back uses, so the two checks cannot drift apart from each other. There is no
`--campaign`-scoped node argument here on purpose: the ledger is campaign-wide, so one read-back covers every node in
it, not just the one you happen to be granting next.

### Grant

`telperion mission grant <slug> --campaign C [--identity I] [--session S]` is unchanged in shape from before this
step — it is still the only verb that flips `open` to `proved`/`refuted`, and it is still a syntactic, local gate, not
a Lean rebuild. What changed is how many preconditions a post-cutoff `proved` grant now carries, and the order the
gate actually checks them in (`verify.grant_status`): the usual open/proof-link/artifact/statement-match checks first,
then — once the gate already knows the grant would be `proved` — in this order: a passing, current `[checks]` record
(whose fingerprint must be the node's frozen statement fingerprint, so a campaign that is not frozen with
fingerprints is refused here, before the freeze check itself);
an `[author]` block (refused outright if absent, since a post-cutoff node always gets one from `add`, so a missing one
can only mean a hand edit); the campaign's freeze (with the full git-history walk); the deviation ledger and its
read-back. Each layer's refusal names itself plainly — `[checks]`, "frozen" / FREEZE.toml, `DEVIATIONS.readback.toml`
— so a refused grant tells you which of the four to go satisfy next, in the order the gate will actually ask for them.
A `refuted` grant skips all four: a refutation does not rest on a passing `[checks]` record, a frozen statement, or a
deviation ledger read-back, the same way it already skips the heavy-node re-judge.

### Audit.lean and the provenance cross-check

`telperion mission audit-file <campaign>` writes `<campaign>/lean/Audit.lean`: one `import` per distinct proved-node
artifact module (sorted, de-duplicated), then one `#print axioms <theorem>` per proved node, so that running it
through `lake env lean` gives one transcript naming every axiom every proved node in the campaign actually rests on.
Capture that transcript and cross-check it against a closure audit's own JSON with:

```bash
lake env lean lean/Audit.lean > print_axioms.txt
telperion audit-closure --json closure.json   # per node, or however your CI already runs it
telperion mission audit-crosscheck --print-axioms-out print_axioms.txt --closure-json closure.json
```

A theorem on only one side — printed by `Audit.lean` but never closure-audited, or the reverse — is reported as a
problem, same as an axiom set that differs between the two. This is a drift net across the WHOLE campaign's proved
nodes in one pass, independent of the per-node, per-grant checks `checks-record` already ran.

### The provenance lint

`telperion lint-provenance <campaign-root>` enforces spec 7.4 on every `.lean` file under the campaign: a file counts
as "ported" either because its own first 30 lines mention `ported from`, `adapted from` or `copied from` (inside a
Lean comment, never inside a string or in code), or because `<dir>/PORTED.toml` names it explicitly in a `files =
[...]` list — a hand-curated declaration for a file ported verbatim with its original header already stripped, which
the mention scan alone would miss. Every file counted as ported must then carry, in that same 30-line window, a line
matching `-- Provenance: repo=... file=... commit=<40 lowercase hex>`. Clean exits 0 with one `OK` line; any problem
exits 1 and lists every file by name; a path that does not exist, or is not a directory, exits 2 rather than printing
a silent, misleadingly clean `OK` for a typo'd path.

### Known limitations, stated plainly

- **Local `.git` contents, including its history, are not fully trustworthy inputs on their own.** The freeze-history
  walk (`freeze_history_problems`) refuses `git replace` refs, grafts, alternates, and a shallow clone outright, and
  it reads through one hardened `_git` helper with a sanitised environment and `--no-replace-objects` — but rewriting
  history to a single, internally consistent commit (amending a freeze and its statement together, with the version
  left unchanged) is inherent to local git and cannot be detected by anything that only looks at the repository doing
  the claiming. The anchor for all of this is a PROTECTED remote branch (no force push) plus a `verify` run in CI
  against a FULL clone of it — never the local repository alone.
- **A shallow clone, or a repository using grafts or alternates, is refused for a post-cutoff campaign**, not silently
  tolerated with a partial history: `git rev-parse --is-shallow-repository`, and the presence of `info/grafts` or
  `objects/info/alternates` or `objects/info/http-alternates` (checked in both the git directory and, for a linked worktree, the common directory), are
  each a hard refusal. Fetch full history (`fetch-depth: 0`) and drop grafts/alternates before freezing or granting.
- **Git 2.31 or newer is required.** The history walk pins `log.follow=false` and relies on `git log --first-parent
  --raw --no-abbrev` behaving the documented way; an older git is not tested against this and may not refuse the
  things it is meant to refuse.
- **The deviation ledger's own git history is not yet checked.** `DEVIATIONS.md` and its read-back are checked
  against the WORKING TREE only (present, readable, parsed, read back, current) — unlike `FREEZE.toml`, there is no
  walk of its git history yet, so the same "rewrite history to a consistent commit" class of tampering that the
  freeze's own history walk cannot catch either, applies here with nothing watching for it at all. A tracked
  follow-up, not a gap specific to this step.
- **Module names in the generated `Audit.lean` are ASCII-only.** `_validate_module_name` refuses any module component
  outside a plain ASCII Lean-identifier charset — deliberately narrower than Lean's real identifier grammar, which
  does allow non-ASCII letters in some ranges. A real island's modules are ASCII in practice, so this fails closed
  (refuses and names the node) rather than risk later discovering a character class it should not have trusted.
- **A Unicode homoglyph can hide a "ported from" mention.** The provenance lint's "ported" detection
  (`_PORTED_MENTION_RE`) is a literal ASCII match on `ported`/`adapted`/`copied from`, exactly spec 7.4's own wording.
  Swap the Latin `a` in "from" for a Cyrillic `а` (U+0430) and the file is never classified as ported at all, so no
  provenance header is ever required of it — not a bug relative to the brief, which defines "ported" by that exact
  regex, but a real, cheap way to dodge the control, deliberately or by copying a header that already carries one.

## MCP Tools (for Claude Code / agents)

Two read-only tools in the Telperion MCP server:

- **`mission_status(campaign="")`** — Return a status tree (all campaigns if `campaign` is empty).
- **`mission_open_leaves(campaign="", include_claimed=False)`** — Return the live frontier. Pass `include_claimed=True` to show claimed nodes.

## Key Discipline

- **Always log attempts** (even NoGo / Stalled), so future sessions don't re-walk dead paths.
- **Read-back before open, and NOT BY THE AUTHOR:** A `draft` node needs a human-language
  `audit` (prose or Lean statement rendering) before it can move to `open`. This catches
  "formalized the wrong statement" early. **The renderer must not be the statement's
  author** — an independent session, or the operator (`MISSIONS_DESIGN_2026-09-11.md` §8).
  **A subagent you spawn is you**: same session, same git identity. Since 2026-09-23 the CLI
  enforces this (`AUDIT_INDEPENDENCE_2026-09-23.md`): `add` records `[author]`, `audit`
  refuses the author's session or identity, a text under 120 characters, or a text that
  only repeats the title, and `verify` fails a proved node whose read-back is a self-audit.
  The rule: a read-back is independent only if (i) different session AND different identity,
  or (ii) the `missions-comparator` job passed on the node and was recorded. Every read-back
  recorded before 2026-09-23 is `independence = "unverified"`; `mission provenance-report`
  lists the proved nodes nobody independent has vouched for. It is the only thing standing
  between a wrong or vacuous statement and a `proved` node, because `grant` is containment
  against the very statement the author wrote. If no independent session is available,
  leave the node in `draft`; a draft is honest.
- **The kernel is the sole authority:** No manual status edits. Only `mission grant` (with CI verification) flips `proved`/`refuted`.
- **Claims are soft:** Respect TTL and claim-over etiquette, but don't block other sessions.

## For Parallel Sessions

The registry is git-backed: one file per node, one append-only attempts ledger. Claim files are committed; git merge handles the rest. Collision-guard conventions (arda-style) continue to protect races.
