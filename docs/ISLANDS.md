# Islands: external Lean libraries Telperion has replayed

Sooner or later a research lab wants to build on a library somebody else wrote. A
good example is AxiomMath's RiemannJensen, which proves the Jensen–Pólya
hyperbolicity results that the Riemann-hypothesis work leans on. "Somebody proved
it in Lean" is a much weaker claim than it sounds, though. Which commit? Built with
which toolchain? Against which statement: the one in the README, or a slightly
weaker one tucked away in a support file? With which axioms? And did anyone other
than the authors' own CI ever check it?

An **island** is Telperion's answer to those questions. It is an external Lean
library that is registered at one exact commit, together with the evidence of an
independent replay of its main theorems: a Comparator run with nanoda as the second
kernel, plus the step-4 statement checks (the negation probe and the statement
fingerprint). Telperion keeps that evidence and re-checks it every time anyone asks
about the island. A lab may build on an island only once the evidence is complete.

This page covers what is in a registration, the commands, what `verified` does and
does not mean, how islands fit with the kernel policy, and the two islands that are
registered today.

## Where replays run: a sandbox, never this machine

Replaying an island means building it. Building a Lean library runs its code,
including Lake configuration, macros, `initialize` blocks and tactic
metaprograms, and that code runs with the permissions of whoever starts the build.
For a library we did not write, that is not acceptable on the owner's machine.

So the owner decided on 2026-10-31 that **island replays run only in a remote
sandbox**: a Linux container in which every build, export and kernel run goes
through bubblewrap with `--cap-drop ALL` and no network. External library code is
never built locally. Locally, Telperion does only two things:

- **registers** the island: it clones the library at the pin and copies the
  challenge file byte for byte, but builds nothing;
- **ingests** the sandbox's evidence with `telperion island record-replay`, and
  re-checks it on every `island check`.

An independent auditor inspects each sandbox run, reading the byte-exact logs,
before anything is recorded here.

## What a registration holds

Each island lives in `islands/<name>/`. The directory holds the registration and
the evidence. It never holds library source.

```
islands/<name>/
  island.toml       the pin (source, commit, toolchain, licence), the challenge module and
                    its sha256, the intended theorems, and, once a replay passes, [replay]
  challenge.lean    a byte copy of the library's challenge file; its sha256 is in island.toml
  comparator.json   OUR Comparator config: the three standard axioms, enable_nanoda,
                    exactly the island's theorems
  replay/           the archived evidence of the passing replay (absent until one is recorded):
                      comparator.log.xz     the Comparator log, xz-compressed
                      probe-<sha256>.json   one `probe-negation --json` output per theorem
                      fingerprint.json      one `fingerprint --json` output for all of them
  REPLAY.md         a generated human summary of the registration and of every replay
```

A few details matter here.

- **Our `comparator.json` wins.** It is written by Telperion, not copied from the
  library. If the library's own config differs (say it permits `sorryAx`, or lists
  fewer theorems), ours still has exactly `propext`, `Quot.sound` and
  `Classical.choice`, `enable_nanoda: true` and the full theorem list, and
  REPLAY.md records the difference.
- **The challenge copy is checked.** `island check` compares `challenge.lean` with
  the sha256 recorded in island.toml. A local edit to the copy drops the island to
  self-reported.
- **The archived log is normalized.** The sandbox's per-session scratch path is
  replaced by `$SCRATCH` before the log is judged and archived
  (`--scratch-prefix`), so that the public archive does not carry it. REPLAY.md
  records the md5 and sha256 of the raw log, so the auditor's copy can still be
  matched. The probe and fingerprint JSONs get the same replacement.
- **REPLAY.md is for people.** Nothing reads it. `island check` decides only from
  island.toml and the files under `replay/`.

## The commands

```
telperion island add NAME --source URL --commit SHA --use TEXT [--licence SPDX]
telperion island record-replay NAME --log FILE --probe-json FILE ... --fingerprint-json FILE \
    --date YYYY-MM-DD --comparator-tag vX.Y.Z[-rcN] [--scratch-prefix PATH]
telperion island list
telperion island check [NAME]
telperion island replay NAME          # INSIDE A SANDBOX ONLY
```

### `island add`

`island add` clones the library at the full 40-hex commit into
`~/telperion-tools/islands/<name>/src`, outside the repository, and checks that
`git rev-parse HEAD` is the pin. It then refuses a clone whose working tree is not
exactly that commit. The check is stricter than plain `git status`: it also catches
untracked files, files hidden by `.git/info/exclude` or a global excludes file,
files marked assume-unchanged or skip-worktree, and ignored submodule changes.

From the clone it reads `lean-toolchain`, `Comparator/comparator.json` (for the
theorem names and modules), the challenge file, and the licence. It then writes
island.toml without `[replay]`, our comparator.json, a byte copy of the challenge
and REPLAY.md. Nothing is built.

It also refuses a toolchain whose Comparator tag has no known export set (see
"What `verified` means" below), because no replay on such a tag could ever pass.

### `island record-replay`

`island record-replay` ingests a replay that ran in the sandbox. It takes:
- the Comparator log, whose first line must be
  `ISLAND-HEADER island=<name> commit=<pin> challenge_sha256=<sha>`;
- one probe JSON per theorem;
- one fingerprint JSON.

It judges them with the same function that `island replay` and `island check` use
(`islands.evaluate_replay`). On PASS it archives the evidence under `replay/` and
writes `[replay]`, with the sha256 of every archived file. On FAIL it writes only a
REPLAY.md section, and any earlier `[replay]` is dropped.

### `island list` and `island check`

`island list` prints one line per island with its status. `island check` lists
everything that keeps an island from `verified`, and it exits 1 unless every island
it checked is verified.

### `island replay`

`island replay` does the whole replay itself:
1. `lake exe cache get` and `lake build` in the clone;
2. Comparator with the pinned nanoda;
3. the negation probe for each theorem;
4. the fingerprint.

**It builds and runs the library's code, so it must run inside a sandbox.** It
exists for operators who have one. We never run it on the owner's machine.

## What `verified` means, and what it does not

An island's status is `verified` or `self-reported`, with nothing in between. It is
`verified` exactly when `island check` finds no problem, and that requires every
one of these:

- island.toml is well formed, pinned to a full commit, and its challenge copy
  matches its recorded sha256;
- our comparator.json is the standard one for this island's theorems;
- the archived evidence is present, matches the sha256s in `[replay]`, and still
  parses to PASS **for this pin, this challenge and the nanoda pinned in
  `NANODA_REV`**:
  - the log's ISLAND-HEADER names this commit and this challenge sha256;
  - the log has Comparator's three accept lines ("nanoda kernel accepts the
    solution", "Lean default kernel accepts the solution", "Your solution is
    okay!") and exit 0;
  - nanoda ran at `NANODA_REV`;
  - every export list, minus the island's theorems, is exactly Comparator's fixed
    set for that tag (`COMPARATOR_EXPORTS`, read off real logs for v4.35.0 and
    v4.34.0-rc2). This binds the log to *our* config: a run under a config that
    permitted `sorryAx`, or that added a definition or dropped an axiom, shows up
    in those lists even when Comparator itself accepts quietly. An unknown tag is a
    FAIL;
  - `comparator_tag` is the island toolchain's version;
- every theorem has exactly one probe JSON, with verdict PROBE_ONLY or WITNESSED;
- the fingerprint JSON covers exactly the theorems, in type mode;
- every probe and the fingerprint name the challenge module, ran on the registered
  challenge file (`source_sha256`), are not stale, and share one `olean_sha256`,
  which means they all ran on one build.

The evidence is re-parsed on **every** check. A replay therefore counts only for the
pin, the challenge and the nanoda it ran with. Moving `commit`, editing
`challenge.lean` or bumping `NANODA_REV` drops the island to self-reported until it
is replayed again.

**What `verified` does not mean.** It does not prove that the run happened.
Whoever operates the sandbox could write a log and the JSONs by hand, and they would
parse. `verified` says the evidence on file is complete and internally consistent.
The anchor that the run really took place is the independent auditor's inspection
of it.

There are also some residual bindings that the evidence does not carry. These are
accepted gaps, written down so that nobody assumes otherwise:

- The probe and fingerprint JSONs are bound to the challenge file and to one another
  (one `olean_sha256`), but not to the commit, the toolchain or the trusted Lean env
  they ran in. A probe run on another clone with the same challenge file would pass.
- The trusted env's digest (`trusted_env_sha256`, which `checks-record` keeps for
  missions) is neither required nor recorded in `[replay]`.
- `comparator_tag` is the operator's flag. It is checked against the island's
  toolchain, but it is not parsed from the log.

A PROBE_ONLY verdict is admissible, but it is weak. It means the probe found no
vacuity and no counterexample, and it can mean that the probe found no testable
instance and searched nothing at all. Read its `detail` field before leaning on it.

## Labs may only build on verified islands

A lab that depends on an island must load it with `islands.require_verified(root,
name)`. That call returns the island only if `island check` has nothing to say, and
otherwise raises `IslandError` with every problem, including for an unknown name.
Self-reported islands are fine to register, list and talk about, but nothing may
build on one. No lab in this repository calls `require_verified` yet; riemann-jensen is the
first verified island (2026-11-06).

## The kernel policy and islands

Step 3's kernel policy (`telperion kernel-policy check`; see
[COMPARATOR.md](COMPARATOR.md), "Kernel policy") holds every Lean project in the
repository to the toolchain floor `leanprover/lean4:v4.34.1`. An island has no
`lean-toolchain` file in the repository, so the policy reads the island's toolchain
from its island.toml and treats `islands/<name>` as a project. Registering a library
therefore cannot bypass the floor. A `lean-toolchain` file inside `islands/<name>/`
is itself an error, because it would be a second, competing pin.

zeta-zeros-v2 is pinned at `leanprover/lean4:v4.34.0-rc2`, which is below the floor,
so it is on the exception list. Its reason says exactly what is true:

- **v4.34.0-rc2 does have the five v4.33.1 kernel soundness fixes,** as backports:
  the commits between v4.34.0-rc1 and v4.34.0-rc2 include #14582, #14806, #14807,
  #14808 and #14849 (and the follow-up #14843).
- **It lacks v4.34.1's later runtime fixes,** such as the reference-count ones
  (#15241, #15288 and #15307).
- **It is never built locally.** The island can be verified only from a
  recorded sandbox replay with nanoda.

The kernel policy's shrink-only check (`kernel-policy check --base REF`) reports
this entry as "exception added" against any base that predates it. That report is
the point of the check: growing the list is a deliberate act that a person reviews.

## The statement fingerprint for islands

The fingerprint (`telperion fingerprint`, `src/telperion/checks/fingerprint.py`)
hashes what a theorem *says*. It ignores binder and universe names, and it unfolds
every definition outside the trusted library roots (Mathlib, Lean, Batteries and the
rest). It never imports an untrusted module. Instead, the challenge module's
constants are kernel-replayed into a pinned, manifest-checked Lean env.

Library challenge files are not as tidy as mission statements, and two things in
them used to make the fingerprint refuse. The first was a local `structure` that
the statements mention, such as `IsDedekindZetaContinuation` in riemann-jensen. The
second was the auxiliary proof theorems that the elaborator lifts out of definitions
(`riemannXi._proof_1`). Before step 6 Task 2b, both of these would have been hashed
by name alone. That would let a changed declaration keep the old hash, so the
fingerprint refused them. Task 2b extends the fingerprint with a **declaration
closure**:

- **A local inductive** (a structure, inductive, class or mutual group) adds one
  declaration block to the hash. The block holds the inductive's type, its parameter
  and index counts, its flags, and every constructor with its field count and type,
  all unfolded and serialized the same way as the statement. A change to a field
  changes the hash; the same declaration in another module does not.
- **A non-library theorem** is hashed by its type, never by its name or its proof.
  Proof irrelevance makes that sound, and it rests on one premise: a theorem's type
  is a Prop. The kernel enforces that premise (checked on v4.34.1 and v4.35.0), and the fingerprint's
  `Meta.isProp` re-check carries it on toolchains where that was not checked, such as v4.34.0-rc2.
  A `sorry` *inside* such a proof is invisible to the fingerprint, which hashes the
  type. Guarding against it is the job of the proof-side axiom audit, which for an
  island is Comparator's axiom whitelist: a `sorryAx` reaching a theorem fails it.

**One known limitation: nested inductives.** A NESTED local inductive, such as
`inductive Rose | node : List Rose → Rose`, is refused by the kernel replay, not by
the serializer. After re-adding the declaration, the replay cannot find the
auxiliary recursor (`No such recursor Rose.rec_1`). That refusal fails closed: an
island whose challenge declares a nested inductive cannot get a fingerprint, so it
cannot be verified, until the replay learns to handle nested inductives. Neither
current challenge declares one.

## The current islands

Status as of 2026-11-06. riemann-jensen is **verified**; zeta-zeros-v2 is **self-reported**.

| island | source @ commit | toolchain | theorems | registered | status |
|---|---|---|---|---|---|
| riemann-jensen | [AxiomMath/RiemannJensen](https://github.com/AxiomMath/RiemannJensen) @ `c1e023fa` | v4.35.0 | 4 (`RiemannJensen.Challenge.*`) | 2026-11-05 | verified (2026-11-06) |
| zeta-zeros-v2 | [AxiomMath/ZetaZerosV2](https://github.com/AxiomMath/ZetaZerosV2) @ `1d7edeb4` | v4.34.0-rc2 (kernel-policy exception) | 12 (`ZetaZeros.Challenge.*`) | 2026-11-05 | self-reported |

### riemann-jensen

- **Comparator replay: done.** It ran in the sandbox on 2026-10-31: Comparator
  v4.35.0 with nanoda at `NANODA_REV` `37cb87b7`, using our config, which matches
  the library's own. Both kernels accepted, and a must-reject tamper of the
  challenge was rejected. The auditor inspected the logs.
- **Negation probes and fingerprint: done.** A first run on 2026-11-01, with
  Telperion before Task 2b, gave PROBE_ONLY for all four probes, and the fingerprint
  refused by design, on the local structure and the `_proof_n` theorems. The rerun on
  2026-11-06, in the sandbox at Telperion `289f078` (with the declaration closure),
  gave PROBE_ONLY for all four probes and a fingerprint over all four theorems, all
  on one build (one `olean_sha256`). The auditor inspected the bundle.
- **Recorded:** `island record-replay` on 2026-11-06, with the sandbox session's
  scratch path normalised to `$SCRATCH` in the archived log. `island check` reports
  `verified`.

### zeta-zeros-v2

- **Comparator replay: done.** It ran in the sandbox on 2026-10-31: Comparator
  v4.34.0-rc2, lean4export v4.34.0-rc2 and nanoda at `37cb87b7`, using our config,
  which matches the library's own. Both kernels accepted, and the export holds no
  `sorryAx`. A possible `sorry` in the PrimeNumberTheoremAnd fork was the worry
  going in, and none reached the theorems. A must-reject tamper was rejected. The
  auditor inspected the logs.
- **Negation probes and fingerprint: pending.** They need their own v4.34.0-rc2 env.
  Telperion's Lean-side checks have so far run only on v4.35.0, so whether they run
  on rc2 is still an open question.
- **Next:** the probes and the fingerprint, in the sandbox. Then `record-replay`.

## Open items

- **There is no Comparator tag for v4.34.1.** Comparator's tags go from v4.34.0
  straight to v4.35.0-rc1 and later, but the floor is v4.34.1. A project pinned at
  exactly v4.34.1 therefore has no matching Comparator build to judge it. The owner
  decided on 2026-10-31 that **new projects default to `leanprover/lean4:v4.35.0`**,
  which has a tag and carries the kernel fixes. v4.34.1 is documented as having no
  matching Comparator tag, and no Comparator is built from source to fill the gap.
- **Nested inductives** are refused by the fingerprint's replay (see above).
- **The trusted env's digest** is not yet recorded in `[replay]` (see "What
  `verified` does not mean").
