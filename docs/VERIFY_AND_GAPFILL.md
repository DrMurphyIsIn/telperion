# Verify + gap-fill — AXLE-inspired infrastructure (2026-09-03)

Two infrastructure primitives that harden and automate the Telperion round-trip,
adopted from a review of Axiom Math's **AXLE** (a Lean-utilities service:
`verify_proof`, `sorry2lemma`, persistent `environment`, …). Telperion GENERATES
certificates from math structure; AXLE showed that the *infrastructure around the
kernel* (verify / decompose / repair) pays off as reusable, typed primitives. These
are the two highest-leverage of those, built for the live BG per-cell round-trip.

## 1. Structured verify (`telperion.verify`)

Replaces the ad-hoc `worktree add` + `lake exe cache get` + `lake build` +
`grep 'Build completed'` + separate `#print axioms` dance with one typed call:

```python
from telperion import verify_lean
r = verify_lean(content, env_dir="examples/log_combination/lean",
                decls=["log79_add_fstar"])
r.okay          # no Lean errors (the COMPILATION gate)
r.axioms_clean  # every checked decl's axioms ⊆ {propext, Classical.choice, Quot.sound}
                # (+ allow_axioms) — the TRUSTED gate; rejects `sorryAx`
r.disallowed    # decl -> axioms outside the allow-set
r.elapsed_s     # ~4–9s warm (vs a full worktree build)
```

`env_dir` is a **pre-built Lake project** — its `.lake` already holds the mathlib
olean cache and any project deps, so verification ELABORATES the given source
against that environment via `lake env lean` **without re-fetching the cache or
rebuilding dependencies** (the "persistent environment"). Point it at any built
project — a Telperion example's `lean/` dir, or a worktree of the BG `R3Cert`
project — to verify emitted Lean *in context*.

The `okay` (compile) vs `axioms_clean` (trusted, sorry-rejecting) split mirrors
AXLE's `check` vs `verify_proof`, and Telperion's untrusted-generator /
trusted-kernel boundary. CLI: `python -m telperion.verify <file> --env <dir> --decl <name>`.

*Follow-up:* a warm long-lived Lean server for sub-second repeat verification. This
MVP already removes the per-call cache-get + dependency rebuild.

## 2. Gap-driven emitter loop (`telperion.gap_fill`)

Automates the round-trip that was hand-driven cell-by-cell (AXLE `sorry2lemma` →
route-match → fill). The BG session writes a cell whose analytic core is a
`sorry`-bodied standalone lemma; this module extracts the goal, recognizes it as a
log-combination enclosure, auto-selects the route, generates the proof, and
verifies it:

```python
from telperion import fill_gap, extract_gaps, Gap
for gap in extract_gaps(cell_file_content):        # every `:= by sorry` lemma
    proof, route = fill_gap(gap)                    # extract -> match -> route -> emit
    # route ∈ {monotone, tangent, tight} chosen automatically
```

Route auto-selection recovers **exactly** the routes chosen by hand for the six real
BG subaction enclosures (`test_gap_fill.py`):

| gap | statement | auto route |
|---|---|---|
| `log74_le_4fstar` | `log(7/4) ≤ 4·FSTAR` | monotone |
| `log54_sub_fstar_le` | `log(5/4) − FSTAR ≤ 1/20` | tangent |
| `log74_le_4fstar_broom` | `log(7/4) − 4·FSTAR ≤ −1/2688` | tangent (neg `q`) |
| `log119_sub_fstar` | `log(11/9) − FSTAR ≤ −1/200` | tangent |
| `log79_add_fstar` | `log(7/9) + FSTAR + 1/24 ≤ 0` | tight (+F\*, deg-3 exp) |

Each fill was checked end-to-end: emitted proof → `verify_lean` → `[OK] axioms clean`
against the built env in ~4–5s. CLI:
`python -m telperion.gap_fill <cell_file.lean> [--env <built_dir>]`.

**Scope.** The current matcher handles the FSTAR-normalized single-log family
`c·log(r) − k·FSTAR (+ const) ≤ q` (`FSTAR = log(B)/N`, default BG `B=621/64, N=11`)
— exactly the atoms the BG subaction cells need, all three routes, incl. the `+F*`
(negative coefficient) and negative-`q` cases. Other emitter families register their
own matchers behind the same `extract → match → pick_route → fill` interface. The
DECOUPLE + per-child assembly around each atom is still authored in Lean (it composes
`log_tangent` + the filled enclosure); this loop automates the *enclosure atom*, which
was the per-cell hand-work. `conjecture1_proved = False`.
