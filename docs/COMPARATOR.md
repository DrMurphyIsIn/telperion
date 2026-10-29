# Independent verification with the Comparator

Telperion's trust model has three layers. `lake build` (the Lean kernel) rejects a
*false* theorem. `nonvacuity.py` rejects a *true-but-vacuous* one. The
**Comparator** — [`leanprover/comparator`](https://github.com/leanprover/comparator),
from OpenAI's [ten-proofs](https://github.com/openai/ten-proofs) — adds a *second
opinion* that no single Lean build can give: it confirms the emitted proof proves
exactly the intended statement, uses only whitelisted axioms, and survives a
kernel written by someone else.

This is the canonical reference. For runnable examples see
[`examples/bernoulli/lean/`](../examples/bernoulli/lean/) (single-file, end-to-end
CI) and `examples/r7_starofhubs/comparator/` (sharded), which stayed in Arda:
[`examples/r7_starofhubs/`](https://github.com/DrMurphyIsIn/Arda/tree/main/telperion/examples/r7_starofhubs/).

## What the Comparator checks

Given a **challenge** module (the intended statement) and a **solution** module
(the emitted proof), it exports both with `lean4export` and asserts:

1. **Statement identity** — the solution proves *exactly* the challenge statement,
   not something weaker. When the challenge is authored independently of the
   certificate, this is a generator-independent nonvacuity check.
2. **Axiom whitelist** — a per-theorem `#print axioms`, admitting only the axioms
   you list. The clean set is `[propext, Quot.sound, Classical.choice]`. This
   rejects `sorryAx`, a smuggled `axiom`, and `native_decide`'s `ofReduceBool`.
3. **Kernel replay** — the exported proof is re-checked by the Lean kernel and,
   with `enable_nanoda`, by [nanoda](https://github.com/ammkrn/nanoda_lib), a
   second kernel implemented from scratch in Rust. A soundness bug must fool both.

## The bridge — `telperion.comparator`

| function | purpose |
|---|---|
| `challenge_config(*, challenge_module, solution_module, theorem_names, permitted_axioms, enable_nanoda)` | build one config (ten-proofs JSON schema) |
| `challenge_for_result(result, profile, *, challenge_module[, solution_module])` | derive names + solution module from an `EmitResult` |
| `emitted_theorem_names(result, profile)` | fully-qualified names of every emitted theorem |
| `render_challenge_scaffold(result, profile, *, module_name)` | a challenge module: emitted signatures, independent proof (`positivity` by default) |
| `sharded_challenge_configs(result, profile, *, module_base)` | one config per shard (multi-file emits) |
| `render_sharded_challenge_scaffolds(result, profile, *, module_base)` | one challenge module per shard |
| `write_challenge_config(path, config)` | write JSON |
| `CLEAN_AXIOMS` | `("propext", "Quot.sound", "Classical.choice")` |

```python
from telperion import (challenge_for_result, render_challenge_scaffold,
                       write_challenge_config)

res = emit(certify(fam), profile, [emitter], validation, file_name="MyFam.lean")
cfg = challenge_for_result(res, profile, challenge_module="MyFamChallenge")
write_challenge_config(out / "MyFam.comparator.json", cfg)
(out / "MyFamChallenge.lean").write_text(
    render_challenge_scaffold(res, profile, module_name="MyFamChallenge"))
```

### Two modes

- **Independent challenge** (strongest). The challenge module restates the
  theorem and proves it *without* Telperion's certificate — an independent
  `positivity`, a hand proof, whatever. Statement identity then has teeth: a
  drifted emission fails the type match. Use this when the statement can be
  expressed apart from the certificate (the bernoulli example).
- **Self-check** (`challenge_module == solution_module`). Use this when a
  statement genuinely *can't* be re-stated independently — e.g. a capstone whose
  statement is *about* your own definitions. Statement identity is trivial, but
  the axiom whitelist and the second kernel remain real, independent verification.

### Naming

Keep the theorems' **namespace** distinct from the lake **package** name and every
Lean **module** name (as ten-proofs does: namespace `PermanentFormulaLowerBound`,
package `ten-proofs`, module `Permanent`). The Comparator matches theorems by
fully-qualified name, so challenge and solution are different *modules* under the
same names.

## Kernel policy

Comparator's second kernel is one of our two defenses against a bad Lean kernel. The
other is just running a *recent enough* one, and that turned out to need its own
enforcement, because for a while a handful of example islands were quietly pinned to
a toolchain old enough to predate real kernel fixes.

Lean v4.33.1 landed a cluster of kernel soundness fixes: #14806 (an order-dependent
defeq cache — two calls that should agree on whether two terms are definitionally
equal could disagree depending on what had already been cached), #14807 (`isProp`
accepting a stuck type it shouldn't have), #14808 (a gap in the recursor checks),
#14582 (non-uniform inductives), and #14849 (a numeral-size check). Any one of these,
on its own, is the kind of bug that lets a false theorem through the kernel — exactly
what Telperion's whole trust model exists to rule out. So we don't treat "the kernel
accepted it" as good enough until the kernel in question is new enough to have all
five fixes. `leanprover/lean4:v4.34.1` is the first tagged release that carries the
complete set, and that's why it's the floor: `telperion.checks.kernel_policy.FLOOR`.

The policy itself (`src/telperion/checks/kernel_policy.py`, spec 5.1) walks every
tracked `lean-toolchain` file in the repo (skipping anything under `.lake/`, since
that's vendored dependency code we don't control) and compares it against the floor.
Run it yourself with:

```
telperion kernel-policy check
```

A project below the floor fails the check — unless it's named in
`kernel_policy_exceptions.toml` at the repo root. That file is how we admit that a
handful of older example islands were proved before v4.34.1 existed, without
pretending the problem doesn't exist. Each entry looks like this:

```toml
[[exception]]
project = "examples/bernoulli/lean"
toolchain = "leanprover/lean4:v4.32.0"
reason = "support example pinned before the v4.33.1 kernel fixes; not yet re-checked by a second kernel; upgrade pending"
```

`project` is the directory holding the `lean-toolchain` file, `toolchain` is the exact
pinned string (it has to match what's on disk, or the check flags a "toolchain
mismatch" — the exception is for a *specific* pin, not a standing exemption from the
floor), and `reason` says why it's there. Today that reason is the same for every
entry: the project was pinned before v4.34.1 existed, and nothing in this repo has
re-checked it with a second kernel since. The entry is a named debt, not a clean bill
of health — closing it means either bumping the toolchain past the floor, or actually
running a second kernel such as nanoda against it and recording that.

The list is **shrink-only**. An exception can be removed (because the project's
toolchain got bumped past the floor) or edited to match a new pin, but a *new*
exception should only ever appear for a project that genuinely predates the floor —
never as a way to let a brand-new project skip ahead of it. The check itself leans on
this: an exception for a project that now meets the floor is flagged as "stale" and
has to be deleted, and an exception for a project that no longer exists at all is
flagged as stale too. There's no code path that silently grows the list; growing it is
something a human has to do on purpose, in a reviewed commit. Shrink-only is enforced
automatically on pull requests: `telperion kernel-policy check --base REF` (`kp.shrink_problems`
in the same module) reads the exceptions file as it stood at `REF` with `git show` and
flags any project added since, or any project whose toolchain dropped relative to that
base — removing an entry or raising a toolchain is always fine. CI passes `--base
origin/${{ github.base_ref }}` on `pull_request`; a plain push has no base to diff
against, so it runs the check without `--base`.

### The heavy-node rule

The same spec section also governs the Comparator configs we *render* for judging,
via `judge_config_problems` in the same module. Two things have to be true of every
rendered config: the axiom whitelist has to be exactly `CLEAN_AXIOMS` (no extra axioms
smuggled in, nothing missing), and `enable_nanoda` has to be on — nanoda, the second
kernel, has to actually run.

The one place nanoda is allowed to be off is a **heavy node**: one whose config sets
`heavy_certificates` or `judge_via = "heavy"`. Those are nodes whose certificates are
too expensive to re-export and re-check through Comparator's normal path in CI, so
instead they get a **local** second-kernel re-judge — someone runs nanoda against them
by hand, off to the side, and that re-judge is what stands in for the CI-driven check
everything else gets. A heavy node without nanoda in its rendered config isn't skipping
the second kernel; it's just getting it from a different, out-of-band place. This rule
is scoped to the mission bundles that `missions.judge.build_bundle` renders: a non-heavy
bundle it renders with `enable_nanoda: false` is a bug, and `judge_config_problems` — and
`build_bundle`, which calls it — will say so. It does not cover a committed standalone
Comparator config outside that path — `examples/bernoulli/lean/Bernoulli.comparator.json`
is one, and it ships `enable_nanoda: false` on purpose, which this check never sees.

## Running it end-to-end

All pins are **v4.32.0** — the toolchain, mathlib, and the comparator tag must
match (they do across every Telperion lean example). Several of these pins are below
the kernel-policy floor and are carried as named exceptions in
`kernel_policy_exceptions.toml` (see "Kernel policy" above) until they're upgraded or
actually re-checked by a second kernel. In CI:

1. Build your lean project (`lake exe cache get` + `lake build`).
2. Build the judge from the matching tag — `lake build lean4export comparator`
   in a checkout of `comparator@v4.32.0`. `lean4export` is a *dependency*, so its
   binary lands under `.lake/packages/lean4export/.lake/build/bin` (not
   comparator's own `bin`); locate it and pass it via `COMPARATOR_LEAN4EXPORT`.
3. (Optional) build nanoda — `cargo build --release` in `ammkrn/nanoda_lib`; point
   `COMPARATOR_NANODA` at `target/release/nanoda_bin`; regenerate the config with
   `enable_nanoda`.
4. `lake env comparator <config>.json` from the project directory.

See `.github/workflows/telperion-comparator.yml` for the reference job.

## The landrun `--` gotcha (and the shim)

Comparator wraps its children (`lake build`, `lean4export`, nanoda) in
[landrun](https://github.com/Zouuup/landrun) for sandboxing. Real landrun uses
`urfave/cli`, whose `Args().Slice()` **strips the `--` separator** — which
silently corrupts lean4export's `<module> -- <constants>` CLI (every constant is
then parsed as a module to import → `unknown module prefix '…'`, tracking the
theorem namespace and looking like a name collision that it is *not*).

Because we verify our **own** emitted proofs, the sandbox is not
security-critical — the kernel replay is the guarantee — so the CI points
`COMPARATOR_LANDRUN` at a small shim that accepts landrun's flags but execs the
child un-sandboxed with `--` preserved.

For judging **untrusted third-party** solutions, use
`.github/comparator/landrun-bwrap.sh`, which stayed in Arda (at the Arda repo root, not
under `telperion/`):
[`.github/comparator/landrun-bwrap.sh`](https://github.com/DrMurphyIsIn/Arda/blob/main/.github/comparator/landrun-bwrap.sh).
It is a landrun-CLI-compatible wrapper backed by [bubblewrap](https://github.com/containers/bubblewrap)
that gives real isolation (mount namespace, `--unshare-net`, `--clearenv`) *and*
preserves `--`. The `comparator-sandbox-check` CI job self-tests it (bwrap runs,
`--` survives, ro-root writes blocked, network unshared). A full run under bwrap
may need extra binds tuned to the project.

## Applied to a real proof — Brualdi–Goldwasser

Not just the examples: the three anchor theorems of the BG formalization — the
`Φ ≤ 1` crux (`R3Cert.phi_le_one`), the g-step / master-inequality crux
(`R3Cert.CappedJointConfig.gstep_le_one_achievable`), and the conditional R7′
capstone (`R3Cert.Step3.conjecture1_of_layers`) — are independently re-verified in
CI (`.github/workflows/proof-comparator.yml`, config generator
`proof/formalization/comparator/gen_configs.py`). Both the Lean kernel and nanoda
accept each, axiom-clean. This re-verifies what is *proved* (the two cruxes and
the conditional reduction); it does not close the still-open layers Hnorm/Hdom.

The problem itself was later answered by a different route, and that answer
went through Comparator with a genuine, independently stated challenge: in the
standalone release [DrMurphyIsIn/brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser), the maximizer
theorem is stated in Mathlib's vocabulary (`BGChallenge.lean`, which imports
only the definition of the answer), and both Lean's kernel and nanoda accepted
the proof (a local run, with a pass-through shim in place of the sandbox). For
the release's uniqueness theorem Comparator confirmed only that the statement
matches; no second-kernel verdict is recorded for it.
