# Telperion architecture

Telperion is a **certificate generator with an untrusted-generator / trusted-kernel
trust model**: it may use any heuristic, search, or SDP solver to *find* a
certificate, but the output is Lean that Mathlib's kernel re-proves from scratch.
Nothing Telperion does needs to be trusted — a wrong certificate is a compile
error, never a false theorem. This document maps the code onto that model.

## The one boundary that matters: engine vs. research lab

The package has two clearly separated parts, and the separation is **enforced by
a test** (`tests/test_core_boundary.py`), not just convention:

| | Path | What it is | Depends on |
|---|---|---|---|
| **Engine** | `src/telperion/` (everything except `bg/`) | The reusable, problem-agnostic tool: the pipeline, ~78 certificate emitters, the CLI, the MCP server, the self-verification layer. | sympy only (core) |
| **Research lab** | `src/telperion/bg/` | The Brualdi–Goldwasser–specific research code (spectral helpers, tree search / MAP-Elites, Ehrhart probes). *Not* part of the reusable engine. | `[bg]` extra (numpy, networkx) |

The core engine never imports `bg/`. If you want to use Telperion on your own
problem, you only ever touch the engine; the `bg/` lab is one large worked
example that happens to live in the same repository.

## The pipeline

Every emitted file goes through the same four stages:

```
define ─▶ certify() ─▶ validate ─▶ emit() ─▶ lake build (Lean kernel) ─▶ freeze()
 family    exact cert    sanity       Lean          re-proves              byte-stable
 spec      per instance  gates       output         from scratch           artifact
```

- **`family.py`** — an `InequalityFamily` is a parameterized grid of instances
  (name, symbols, grid axes, constants, and the target per grid point). This is
  the only thing *you* write.
- **`certify.py`** — certifies each instance in **exact `fractions.Fraction` /
  sympy** arithmetic. No floats on the certificate path.
- **`workflow.py`** — `emit()` renders the certified family to Lean. All emitters
  subclass the single `Emitter` base class here (interface: `emit_body(family,
  profile) → (text, n_theorems)`); `LeanProfile` (in `lean.py`) carries
  everything about the target Lean project the output must respect.
- **`provenance.py`** — stamps the input-hash header, and `freeze()` writes the
  byte-stable artifact + manifest that the regeneration-diff gate compares against.
- **`lean.py`** — the Lean rendering (`file_shell`, the tactic skeletons; the
  tactic contract is documented in [`TACTIC_CONTRACT.md`](TACTIC_CONTRACT.md)).

## The certificate emitters

~78 `emit_*.py` modules, each producing one *shape* of certificate. They are
discovered by explicit imports in `src/telperion/__init__.py` (grouped by tier),
and every family generator is listed in the top-level `telperion.toml` manifest
(the source of truth for what CI regenerates and checks). Broadly:

- **General / textbook** — direct Pólya positivity, SOS (rational, Artin
  denominators), the Positivstellensatz family (Handelman, Putinar,
  Nullstellensatz + infeasibility/refutation), Chvátal–Gomory rounding, Sturm,
  Bernstein, exact identities, p-adic valuations, brackets, finite case analysis.
- **Analytic / RH** — zero-free-region atoms, half-plane–disk (Borel–Carathéodory),
  Jensen zero-count, transcendental enclosures.
- **Brualdi–Goldwasser** — tight-cap enclosure, affine-parameter endpoint,
  recursion/cavity closure, per-size dominance, curvature-boundary, integrality
  gate (23-adic), and more.
- **Proof complexity** — SOS refutation, pseudo-expectation duality, XOR moment
  PSD, cone/Farkas infeasibility.

Under the positivity shapes sits an **automatic certificate search** (the Pólya
engine plus optional SDP finders under the `[sdp]` extra), so for many statements
you never construct the certificate by hand.

## The self-verification layer

The Lean kernel catches *false* theorems. It cannot catch a theorem that is
true-but-**vacuous** (e.g. a reflexive `X = X` that proves nothing). Telperion
adds a layer specifically for that gap:

- **`nonvacuity.py`** — refuses reflexive/trivial statements at emit time
  (structural), and, for `CERTIFICATE_SENSITIVE` emitters, checks that corrupting
  the certificate actually breaks the claim (semantic).
- **`emitter_sensitivity.py`** — a registry forcing every emitter to declare a
  stance: `CERTIFICATE_SENSITIVE` (carries a corruptible witness → needs a
  kernel-gated negative-control adapter) or `STRUCTURALLY_NONVACUOUS`
  (positivity / decidable / hypothesis-gated glue → no adapter needed). A new
  emitter that declares neither **fails the test suite** until it does.
- **`negctrl_adapters/`** — the per-emitter negative controls: forge the
  certificate, confirm the kernel rejects the forgery.
- **`comparator.py`** — the independent second check (whitelisted axioms only);
  see [`COMPARATOR.md`](COMPARATOR.md).
- **`circularity.py`, `coverage.py`, `faithfulness.py`, `metacircular.py`** —
  non-circularity witnesses, coverage profiling, seeded-exact-point faithfulness,
  and the audit calculus pointed at itself (which documents the one irreducible
  trusted floor: whether a formal statement *means* the informal claim is
  undecidable — Löb/Gödel).

## Interfaces

- **CLI** (`cli.py`, console script `telperion`) — `certify`, `emit`, `diff`,
  `verify --group <quick|heavy|audit|sdp>`, `prove`, and the diagnosis helpers.
- **MCP server** (`mcp_server.py`, console script `telperion-mcp`, `[mcp]` extra)
  — exposes the same certify→emit pipeline as ~15 tools to LLM/RL agents, with no
  emit-without-certify path. Registered as a Claude plugin under
  `claude-plugin/`.

## Where to look next

- Use it end-to-end: [`GETTING_STARTED.md`](GETTING_STARTED.md).
- Add a new certificate shape: [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
- The trust model in prose: [`METHODOLOGY.md`](METHODOLOGY.md).
- The exact Mathlib tactic bindings: [`TACTIC_CONTRACT.md`](TACTIC_CONTRACT.md).
