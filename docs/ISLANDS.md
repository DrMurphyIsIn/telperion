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
does not mean, overlay islands (for a library that ships no challenge module), how
islands fit with the kernel policy, and the two islands that are registered today.

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
                    (for an overlay island: the overlay the lead wrote; see "Overlay islands")
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
telperion island add NAME --source URL --commit SHA --use TEXT [--licence SPDX] \
    --overlay FILE --overlay-path PATH --overlay-import MODULE ... --solution-module MODULE
telperion island place-overlay NAME --tree DIR [--check-only]   # git only; for a sandbox run by hand
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

## Overlay islands: a challenge the lead writes

Both of the first two islands came with a challenge module of their own:
`Challenge/Basic.lean`, which states the theorems and proves nothing, plus a
`Comparator/comparator.json` that names it. Some libraries ship neither. AxiomMath's
Weil is one of them. Its main theorems sit in the middle of proof files, next to
their proofs, and there is no file that only states them.

For such a library the owner chose, on 2026-11-06, what we call **option A**. The
Telperion lead writes the statement-only module, an **overlay**, and Telperion pins it
by sha256. At replay the overlay is placed into a fresh copy of the pinned tree, and
Comparator treats it as the challenge.

### What the registration says

An overlay island's island.toml has four keys that an ordinary island does not have:

```toml
challenge_source = "overlay"
challenge_module = "Weil.TelperionChallenge"       # the overlay's module, from its path
solution_module = "Weil.AlgebraicGeometry.EtaleCohomology.Trace.WeilRiemannHypothesisForm"
overlay_path = "Weil/TelperionChallenge.lean"      # where the overlay goes in the tree
overlay_sha256 = "012753bf..."                     # in place of challenge_sha256
overlay_imports = ["Weil.Definitions"]             # the upstream definition modules it may import
```

`overlay_sha256` is the sha256 of `islands/<name>/challenge.lean`, which for an overlay
island is the overlay itself. It is called `overlay_sha256`, not `challenge_sha256`,
everywhere it appears: in island.toml, in `[replay]`, and in the log's first line. That
way nobody can mistake the lead's file for a byte copy of the library's.

`overlay_imports` is the lead's declaration of which upstream modules are *definition*
modules. An overlay may import Mathlib and these modules, and nothing else. The tool
can enforce that list, but it cannot decide what belongs on it, so bb checks the list
against the library.

### What the tooling enforces

On every `island check`, from the text of challenge.lean alone, with nothing built:

- **The sha256 matches.** challenge.lean must have the recorded `overlay_sha256`. An edit
  drops the island to self-reported, as it would for an upstream island.
- **It is statement-only.** After `module` and the imports, the overlay may contain only
  `namespace`, `section` and `end`, `open`, `universe`, `variable`, `omit ... in`, and
  theorems. Every theorem must be proved exactly `:= by sorry`. It may contain no `def`,
  `instance`, `abbrev`, attribute, `set_option`, macro, notation, `axiom`, `#eval`, and
  no string literal at all. That last rule leaves out tags such as `@[weil "..."]`, which
  are not part of any statement anyway.
- **Its imports are Mathlib plus exactly `overlay_imports`.**
- **It declares exactly the island's theorems,** each one once and under its fully
  qualified name, and each carries a comment of the form
  `-- upstream: <path>:<line>` right above it. The comment names the line of the
  library's own declaration.

At `island add --overlay`, and again every time the overlay is placed, it is checked
against the pinned tree. This is text only; nothing is built.

- **Each pointer must name a `theorem` with the same fully qualified name,** and with the
  same statement text, whitespace aside. The statement text runs from `theorem` to the
  `:=` that ends the statement.
- **The overlay must import no module that declares one of its theorems,** directly or
  through the library's own import graph.
- **The solution module must import every module that declares one of the theorems.**
- **The overlay's path must not exist in the tree.** An overlay is always an *added*
  file, never a replacement for one of the library's files. Its directory must exist, and
  must be under the solution module's root, so that `lake build` finds it in the library.

### Placing the overlay, and the clean-tree guard

The overlay only ever goes into a **fresh** copy of the pin: a git checkout whose HEAD is
the commit and whose working tree passes the same strict clean check that `island add`
uses (see "`island add`" above). Once the overlay is placed, the tree must be exactly
the pin plus that one file. The status check must print exactly `?? <overlay_path>` and
nothing else, and the placed file must have the registered sha256. Anything else is
refused: a second untracked file, an edited library file, an overlay that is already
there (a reused tree), or a placed overlay that was edited.

`island replay` does all of this itself, before it builds anything. It then builds the
solution and the challenge by name (`lake build <solution> <overlay module>`), because
the overlay is in no default target.

In a sandbox that is run by hand, `telperion island place-overlay NAME --tree DIR` does
the placing. It runs only git. After the last command,
`telperion island place-overlay NAME --tree DIR --check-only` checks that the tree is
still exactly the pin plus the overlay.

The log's first line binds the overlay rather than an upstream challenge:

```
ISLAND-HEADER island=weil commit=<pin> overlay_sha256=<the overlay's sha256>
```

`evaluate_replay` refuses a `challenge_sha256=` header for an overlay island, an
`overlay_sha256=` header for an upstream island, and a sha256 other than the registered
one. A run on an edited overlay therefore cannot be recorded against the registered
one.

### How Comparator is set up

- **The challenge module is the overlay** (`Weil.TelperionChallenge`).
- **The solution module is an upstream module that imports the proof of every theorem.**
  For Weil this is `WeilRiemannHypothesisForm`, which imports `ZetaRationality`. A
  narrower module also means a smaller build than the library's root module, which
  imports all 980 files.
- **Our comparator.json is the config,** as for every island: the three axioms,
  nanoda on, and exactly the theorems.

The theorem names are the same in the challenge and in the solution, because Comparator
matches theorems by name. The two declarations never clash, because they are never in
one environment:

- The overlay imports only definition modules, and their import closure contains no
  module that declares any of the theorems. `upstream_problems` checks that against
  the library's own import graph, and if a clash slipped past that check, the overlay
  would fail to build, which fails closed.
- Nothing imports the overlay. It is in no library module's imports, and the library's
  root module does not list it.
- Comparator builds the two modules separately, and exports each one with
  `lean4export` in a process of its own. The negation probe and the fingerprint replay
  only the overlay's closure.

Here is what Comparator then establishes. Each of the overlay's statements has exactly
the type of the solution's theorem of the same name. Every definition those types
mention is the same constant on both sides, and comes from the same upstream modules.
And the solution's proofs pass both kernels with only the three axioms. An overlay
that changes a statement fails this. It fails earlier too, at `island add` and at
placement, where the statement text is compared with upstream's
(`tests/test_islands.py`, `test_overlay_add_refuses_and_writes_nothing`).

### The trust model

**The overlay is a trusted statement layer.** The lead writes it, and nobody runs it as
evidence of anything. What it contributes is the *choice* of statements: which
theorems, and the claim that each one says what the island's description says. The
tooling makes the overlay faithful to the library, in that it has the same names, the
same statement text and, at replay, the same types. It cannot make the library's
statements mean what we think they mean. That is the reviewer's job, exactly as it is
for a library's own challenge file.

**bb checks an overlay against upstream, statement by statement,** before any replay is
assigned:

1. **Each theorem's `-- upstream:` line is the library's declaration,** and the overlay's
   text from `theorem` to `:=` is identical to upstream's.
2. **The context is upstream's.** That means the `open`, `universe` and `variable`
   commands, and any `omit ... in`, that are in scope at upstream's declaration. The
   tool does not check these, and Comparator would catch a difference only as a type
   mismatch, so bb compares them by eye.
3. **Every module in `overlay_imports` is a definition module.** It must declare
   definitions and the lemmas their definitions need, not the theorems themselves.
4. **The definitions that the statements unfold to mean what the island's description
   claims.** For Weil's point-count statements that is `zetaSeries`, then
   `pointCountOfDegree`, then `pointCount`, then
   `Stacks.EtaleCohomology.fieldValuedPoints`, which is a Mathlib-only subtype of
   morphisms `Spec K ⟶ X`.

**What the overlay adds to the residual gaps above.** An overlay changes nothing about
what `verified` means. What it adds is one more file whose content is a matter of
judgement, and so one more thing that bb reviews.

**One cost of an overlay.** The overlay's import closure is the closure of its
definition modules, and the probe and the fingerprint kernel-replay that whole closure.
For Weil, `Weil.Definitions` imports `StacksFrontier`'s ℓ-adic trace formula. Its
closure is therefore about 17,800 modules of AxiomMath/Stacks, roughly 5.3 million
lines, even though the two statements unfold only to Mathlib and a few small
definitions.

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
- **Negation probes and fingerprint: not yet run successfully.** The open question
  was whether Telperion's Lean-side checks run on rc2. The first run answered it: **no,
  at Telperion `289f078`**. It ran on 2026-11-06, in the sandbox, in its own
  v4.34.0-rc2 env (Mathlib `85e3a25e`), and all twelve probes and the fingerprint ended
  in ERROR. They all had one cause, on Telperion's side: the replay template compared
  two constants with `==` on `ConstantInfo`, and v4.34.0-rc2 derives no `BEq` for
  `ConstantInfo` (v4.35.0 does). Nothing about the library was decided by that run.
- **Fixed in `f84eb11`.** The comparison is now written out by hand. It checks every
  field of every constructor and compares every expression with `Expr.equal`, so it is
  at least as strict as v4.35.0's derived one. On rc2, the replay template and the
  probe and fingerprint callbacks now compile and run (`tests/test_rc2_compile.py`), and
  the six fingerprint pins come out the same as on v4.35.0.
- **Next:** a new Telperion pin, a fresh assignment, and a rerun of the probes and the
  fingerprint in the sandbox, on the owner's word. Then `record-replay`.

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
