# Contributing to Telperion

Telperion is an **untrusted generator over a trusted kernel**: contributions may
be as clever or as hacky as you like internally, because the Lean kernel re-checks
the output. What the review process protects is not the generator's cleverness but
its **honesty** — that every emitted theorem is non-vacuous, byte-reproducible, and
means what it says. This guide is about clearing those gates.

New here? Read [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) first (the pipeline
and the engine/research-lab boundary), then [`docs/GETTING_STARTED.md`](docs/GETTING_STARTED.md).

## Setup

```bash
pip install -e "telperion[dev]"     # sympy + pytest + numpy + networkx
cd telperion
python -m pytest tests -q           # the suite should be green before you start
```

Keep the **engine core (`src/telperion/`) sympy-only**. numpy/networkx belong to
the `bg/` research lab and the `[bg]` extra; cvxpy belongs to the `[sdp]` finders.
`tests/test_core_boundary.py` enforces this and will fail if the core imports them.

## Adding a certificate shape (an emitter)

1. **Write the emitter** — a new `src/telperion/emit_<shape>.py` whose class
   subclasses `Emitter` (in `workflow.py`) and implements
   `emit_body(family, profile) → (text, n_theorems)`. Certify in **exact
   arithmetic** (`fractions.Fraction` / sympy); no floats on the certificate path.
2. **Register it** — add the import to `src/telperion/__init__.py` (in the right
   tier group). If it introduces a new certificate *kind*, register that kind in
   `certify.py`.
3. **Declare a sensitivity stance** — add an entry to the `REGISTRY` in
   `src/telperion/emitter_sensitivity.py`. This is mandatory:
   `tests/test_certificate_sensitivity.py::test_every_emitter_is_classified`
   fails until you do. Choose honestly:
   - **`CERTIFICATE_SENSITIVE`** — the emitted theorem carries a corruptible
     witness (a specific numeric/algebraic identity). You must also add a
     negative-control adapter under `negctrl_adapters/` that forges the witness
     and confirms the kernel rejects it.
   - **`STRUCTURALLY_NONVACUOUS`** — the theorem is positivity / decidability /
     finite-cover / hypothesis-gated glue with no corruptible witness; the
     built-in structural non-vacuity check suffices. Write a one-line note saying
     *why* (see the existing entries — e.g. `HalfPlaneDiskEmitter` — as a model).
4. **Add a worked example** — a `examples/<shape>/generate.py` that certifies →
   emits → writes `lean/<Shape>.lean`, and supports `--check` (drift/byte-stability).
   Include a `lakefile.toml` + `lean-toolchain` pinned to `leanprover/lean4:v4.32.0`,
   matching every other example.
5. **List it in the manifest** — add a `[[check]]` block to `telperion.toml`
   (`name`, `script`, `group`). An unlisted `generate.py` is a hard CI failure
   (the manifest-completeness gate). Pick the group by regeneration cost:
   `quick` (seconds), `heavy` (minutes), `audit` (adversarial/large), `sdp`
   (needs cvxpy).

## Before you open a PR

Run what CI runs:

```bash
cd telperion
python -m pytest tests -q                         # unit tests (incl. the sensitivity gate)
PYTHONPATH=src python -m telperion.cli verify --group quick   # regen drift + byte-stability
python examples/<shape>/generate.py --check       # your example is byte-stable
```

And **verify the emitted Lean actually compiles** — the whole point:

```bash
cd examples/<shape>/lean && lake exe cache get && lake build
```

If you cannot run Lean locally, the CI `telperion-lean-e2e` job compiles emitted
Lean for you; do not merge on a red Lean job.

## CI gates your PR must pass

| Workflow | What it checks |
|---|---|
| `telperion-test` | pytest across sympy versions + `verify --group quick` (drift + byte-stability). |
| `telperion-lean-e2e` | regenerate emitted Lean and `lake build` it against pinned Mathlib. |
| `telperion-casestudy` / `telperion-audit` | `verify --group heavy` / `--group audit` re-certification. |
| `telperion-production` | frozen-artifact compile + regeneration diff. |
| `telperion-comparator` | independent second check (whitelisted axioms only). |

## House rules

- **Honesty flags are load-bearing.** Keep `conjecture1_proved = False`; label
  ranges, open pieces, and negative results as such. Preserve failed-route
  `*_nogo*` modules with their reasons — they are part of the record.
- **No floats on the certificate path.** Exact arithmetic only.
- **Don't hand-edit emitted `.lean` files.** They are regenerated; edit the
  generator and re-run.

## Licensing

The Telperion engine (`src/`, CLI, MCP server) is **BUSL-1.1**; emitted
certificates and the `examples/` artifacts are Apache-2.0 (they are yours). See
[`../LICENSING.md`](../LICENSING.md). By contributing you agree your changes are
licensed on the same split terms.
