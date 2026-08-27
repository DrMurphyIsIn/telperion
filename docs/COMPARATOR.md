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
CI) and [`examples/r7_starofhubs/comparator/`](../examples/r7_starofhubs/) (sharded).

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

## Running it end-to-end

All pins are **v4.32.0** — the toolchain, mathlib, and the comparator tag must
match (they do across every Telperion lean example). In CI:

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
[`.github/comparator/landrun-bwrap.sh`](../../.github/comparator/landrun-bwrap.sh):
a landrun-CLI-compatible wrapper backed by [bubblewrap](https://github.com/containers/bubblewrap)
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
