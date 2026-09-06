# Getting started with Telperion

Telperion turns a *family of mathematical statements* into **Lean 4 proofs that
Mathlib's kernel re-checks from scratch**. You describe the family; Telperion
certifies each instance in exact rational arithmetic, emits Lean, and the Lean
kernel is the sole thing you have to trust. This guide takes you from a clean
machine to **an emitted certificate you have verified locally end-to-end**.

There are two halves, and you can stop after the first:

1. **Generate** — pure Python (sympy only). Fast, no Lean required.
2. **Verify** — compile the emitted Lean against a pinned Mathlib. This is the
   step that actually makes it a proof, and it is the part newcomers most often
   skip because the toolchain setup is not obvious. It is written out in full below.

## 1. Install the Python package

Telperion requires **Python ≥ 3.11**. From the repository root:

```bash
pip install -e telperion            # the engine (sympy-only core)
```

Optional extras, installed as needed:

```bash
pip install -e "telperion[dev]"     # pytest + numpy + networkx (run the test suite)
pip install -e "telperion[sdp]"     # cvxpy — the SDP certificate finders
pip install -e "telperion[bg]"      # numpy + networkx — the Brualdi–Goldwasser research lab
pip install -e "telperion[mcp]"     # expose Telperion to LLM agents over MCP
```

This installs two console commands: `telperion` (the CLI) and `telperion-mcp`
(the MCP server). Check it works:

```bash
telperion --help
```

## 2. Generate a certificate (no Lean needed)

Every example is a self-contained `generate.py`. The simplest non-research one
proves Bernoulli's inequality `(1 + x)^k − 1 − kx ≥ 0`:

```bash
cd telperion
python examples/bernoulli/generate.py
# → wrote Bernoulli (5 theorems); input hash 3aa1dbc9…
```

That wrote `examples/bernoulli/lean/BernoulliSolution.lean` — real Lean, one
theorem per instance, each with a proof term. You can read it; you do **not**
have to trust the generator that wrote it, because the next step makes the Lean
kernel re-prove every line.

Re-running `generate.py --check` instead of writing verifies the output is
**byte-identical** to what's committed (this is the drift gate CI runs):

```bash
python examples/bernoulli/generate.py --check
# → check: OK (regeneration matches frozen output byte-for-byte)
```

## 3. Verify the emitted Lean locally (the step that matters)

Compiling the emitted Lean needs **Lean 4 `v4.32.0`** (the pin every example
shares) and a **pre-built Mathlib cache** — do *not* let it compile Mathlib from
source, which takes hours.

**3a. Install elan** (the Lean toolchain manager). `lake` will read each
example's `lean-toolchain` file and fetch the exact pinned Lean automatically:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell, or: source ~/.elan/env
```

**3b. Fetch the prebuilt Mathlib oleans, then build:**

```bash
cd telperion/examples/bernoulli/lean
lake exe cache get      # downloads the prebuilt Mathlib cache (minutes, not hours)
lake build              # the Lean kernel re-checks every emitted theorem
```

A clean exit from `lake build` means the kernel accepted every proof. That is
the whole guarantee: **a wrong certificate is a compile error, never a false
theorem.** Try it — edit a numeric constant in `BernoulliSolution.lean` and
re-run `lake build`; the kernel rejects it.

Every example under `telperion/examples/*/lean/` follows this identical
`lake exe cache get && lake build` pattern.

### Optional: independent second check (the Comparator)

For an even stronger check — that the emitted proof proves *exactly* the stated
theorem using only whitelisted axioms — Telperion integrates
`leanprover/comparator` (from `openai/ten-proofs`) and the independent `nanoda`
Rust kernel. See [`COMPARATOR.md`](COMPARATOR.md). This is what the
`telperion-comparator` CI job runs; it is not required for local use.

## 4. Use it on your own problem

The end-to-end API is `certify → validate → emit`, then `lake build` in your own
Lean project. The five-minute in-memory example and the full list of certificate
shapes are in the [Telperion README](../README.md); the internals and the
engine/research-lab boundary are in [`ARCHITECTURE.md`](ARCHITECTURE.md); how to
add a new certificate shape is in [`../CONTRIBUTING.md`](../CONTRIBUTING.md).

## Troubleshooting

- **`lake build` starts compiling Mathlib from source** — you skipped
  `lake exe cache get`, or your Lean version doesn't match the cache. Confirm
  `lean-toolchain` reads `leanprover/lean4:v4.32.0` and re-run the cache fetch.
- **`telperion` command not found** — the `pip install -e telperion` didn't put
  the console script on your `PATH`; use `python -m telperion.cli` instead.
- **`ModuleNotFoundError: cvxpy` / `networkx`** — install the matching extra
  (`[sdp]` for cvxpy, `[bg]`/`[dev]` for networkx). The sympy-only core never
  needs them; only the SDP finders and the research lab do.

`conjecture1_proved = False` — nothing here depends on trusting Telperion; the
Lean kernel is the arbiter.
