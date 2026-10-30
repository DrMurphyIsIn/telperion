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
| `verify [campaign]` | Run the shallow coherence battery locally (node schema, DAG acyclicity, artifact existence, normalized statement containment) — read-only; add `--deep-lean` to also lake-build the campaign's statement package |
| `graph [campaign]` | Emit DOT export of the dependency DAG with node statuses |

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
3. **The closure audit** (`telperion audit-closure`, `src/telperion/closure_audit.py`). A Lean script that walks the
   theorem's whole constant closure. It fails on a forbidden constant (by default `sorryAx`), on a forbidden module
   prefix, on an axiom outside `propext`, `Quot.sound` and `Classical.choice`, or on a missing target.
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

So the owner's decision ("Replay-isolate") is that **the probe and the fingerprint never import the untrusted module**.
Instead, `src/telperion/checks/lean_replay.py` does what Comparator and lean4checker do:
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

One check is NOT isolated this way: the closure audit. `audit-closure` still runs `lake env lean` in the submission's
project and imports its modules. That runs the project's lakefile and the modules' initializers, so an imported module
can forge the closure audit's output, and it should be treated like a build of untrusted code. This is a known gap,
accepted by the owner for this merge (2026-10-30). The interim guard is the replay axiom cross-check that
`checks-record` applies (see "One closure, bound across the probe and the fingerprint"). Porting the closure audit to a
replay callback is the step-5 follow-up (see the limitations below).

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
- The probe and fingerprint take `--trusted-env DIR` (default `$TELPERION_LEAN_ENV`) and `--trusted-manifest FILE` if
  you need to point at a non-default env or manifest. Nothing from `--project` is ever trusted.

### One closure, bound across the probe and the fingerprint

The probe and the fingerprint each report an `olean_sha256` in their `--json` output, along with `olean_closure`, the
sorted list of `[module, part, sha256]` for every untrusted `.olean` file the replay read (the whole untrusted import
closure, every part of a `module` file). `olean_sha256` is the digest of that list. The replay reads only private copies
of those files and checks afterwards that it read exactly the copies and that they did not change, so the digest names
exactly the bytes the check saw.

`mission checks-record` refuses (exit 2) unless the probe JSON and the fingerprint JSON carry the SAME `olean_sha256`.
That is how you know both checks ran on the same build. Rebuild between the two runs and the record is refused; run
both again.

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
- each `source_sha256` is PRESENT and equals the sha256 of the node's artifact as it is on disk NOW. There is no
  waiver: a JSON without one (a run without `--file`) is refused, so re-run the check with `--file`. (`--file` stays
  optional for interactive runs of the probe and the fingerprint.) A JSON that says `stale` is refused too;
- both JSONs carry the replay's axiom list (`axioms`, `collectAxioms` over every constant of the target module, which
  an imported module cannot forge, since the replay imports nothing untrusted). The two lists must be equal and a
  subset of `propext`, `Quot.sound` and `Classical.choice`, and they must include the closure audit's axioms for the
  target. The list is recorded, and the gate checks it again. This is the interim cross-check on the closure audit,
  which still imports the submission (see the limitations).

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
- **`GATE_VERSION` is `2026-10-29.1`.** Every grant records the gate version that granted it. This version is the first
  that requires `[checks]`; grants made under an earlier version keep the version they were granted with, so you can
  always tell which rules a grant was held to.

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
   `{"error": ...}`. Here `--file` is only hashed, into `source_sha256`. It takes the same
   `--trusted-env`, `--trusted-manifest`, `--olean-dir`, `--memory-mb`, `--wrapper` and `--timeout` options. The project
   (outside `.lake` and `.git`) must contain no symlink and no directory or `.lean` file named after a library root.
3. **Closure audit.** Note that `--json` takes a FILE here, unlike the other two:
   ```bash
   telperion audit-closure --project path/to/project --import Demo.MyNode \
     --target Demo.my_thm --json closure.json
   ```
   Exit 0 PASS, 1 FAIL, 2 when the audit could not run.
4. **Record them:**
   ```bash
   telperion mission checks-record my_node --campaign demo \
     --probe-json probe.json --closure-json closure.json --fingerprint-json fingerprint.json \
     --note "signoff: <reviewer> read the statement; hypotheses are satisfiable by inspection"
   ```
   Every verdict is read from those JSON files, never from a flag. They are unsigned files you produced: reading the
   verdicts from them guards against mistakes, not against an operator who writes them by hand. It refuses (exit 2,
   nothing written) on an unreadable or malformed JSON, an unknown probe verdict, a missing or mismatched
   `olean_sha256`, a target that is not the node's registered theorem, a fingerprinted theorem that the closure audit
   did not audit, a probe of a different theorem, a `source_sha256` that is absent or not the artifact's current
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
  network connections, or start a daemon. The same goes for `audit-closure`, which imports the submission, and for
  fingerprinting submitted text (`run_fingerprint_on_text` compiles it). **Untrusted submissions must be built and
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
- **The closure audit still imports the submission.** The probe and the fingerprint are bound to each other by
  `olean_sha256`, but `audit-closure` imports rather than replays, so an imported module could forge its output, and
  its JSON carries no olean digest. Its ties to the other two are the theorem name and the interim axiom cross-check:
  its axioms for the target must be among the REPLAY's axioms, which must be standard.
  - What the cross-check buys: a forged closure PASS can no longer hide a non-standard axiom. That holds only while the
    code `audit-closure` imports cannot write the probe and fingerprint JSONs or the node file, i.e. under a sandbox or
    when the audit runs as a different user. Outside a sandbox the imported code runs as YOU and can rewrite those
    files too.
  - What it does not buy: a forged PASS can still hide a forbidden constant that is not an axiom, and a forbidden
    module prefix.
  - It bounds the target's axioms only when the target is a constant of the module the probe and the fingerprint
    replayed (their axiom list covers that module's constants). So run the probe and the fingerprint on the
    artifact's OWN module (`--module` / `--import`), not on a module that merely imports it.
  - The owner accepted this gap for this merge (2026-10-30); porting the closure audit to a replay callback is step-5
    work. Run all three on the same build.
- **The theorem tie is syntactic.** `checks-record` and the gate find the node's own theorem with the gate's syntactic
  resolver (`guard_anchors.resolve_theorem`), so an honest artifact cannot pass a helper lemma's checks. An
  adversarial artifact still has known ways to fool that resolver, all of which predate step 4: `s!`-interpolated
  strings, quotes inside `«»` names, declaration text inside `«»`, `#exit`, and `(command| ...)` quotations. The sound
  fix, tying the target's statement fingerprint to the node's statement file, is step-5 work.
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
second `build` without `--force` refuses, and then runs `tests/test_negation_probe.py`, `tests/test_fingerprint.py` and
`tests/test_lean_replay.py` with `TELPERION_LEAN_ENV` set. Those files hold the must-fail controls (the evil-module
cases, a shadowed definition, a vacuous and a refuted statement, a declared axiom, a lemma the kernel never checked),
and they skip without an env, so the job fails if any of them is skipped. It first checks that the runner has at least
10 GB free, so a full disk fails in seconds rather than an hour in. There is no leanlock on the runner and none is
needed: the default wrapper is used only when `~/hodge-engine/leanlock.sh` exists. The CI runner is still not a sandbox
for third-party submissions; it runs only this repository's own test modules.

A full run builds Mathlib's env and takes a long time, so it does not run on every push. It runs when you start it by
hand (workflow_dispatch), once a week on a schedule, and on a push or pull request that touches `src/telperion/checks/`,
`src/telperion/missions/`, `src/telperion/closure_audit.py` or `src/telperion/comparator.py` (both imported by the
checks), the three test files above, `tests/test_missions_checks.py`, the test helpers `tests/lean_env.py` and
`tests/fake_lean_cli.py`, or the workflow file itself. The weekly run is the backstop: a new runner image, or anything
else outside those paths, can break the controls without touching them, and a path filter would never notice.

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
