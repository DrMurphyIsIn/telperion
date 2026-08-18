# Honesty patterns — the methodology, as checkable modules

Eight reusable "meta-skill" patterns distilled from the Brualdi–Goldwasser crux
campaign, where 20+ probes closed with a **zero false-positive rate**.  The
patterns most worth keeping were not the ones that ran a specific probe — they
were the ones that **caught false positives**.  This is that discipline ported
into Telperion: each pattern is a small module whose checker returns a
`ProbeVerdict`, decided in exact rationals, never on a float.

The load-bearing one is #8.  Every other pattern is only as trustworthy as the
discipline of closing it with an explicit verdict and owning self-corrections.

| # | Pattern | Module | What it catches / does |
|---|---------|--------|------------------------|
| **8** | **Honest-verdict record** | `verdict.py` | The spine. Forces every probe to close as one of `VALIDATED / OBSTRUCTED_AND_LOCATED / NULL / RE_DERIVATION`, and **refuses floats at decision points** (`require_exact` / `decide`). Structural invariants: OBSTRUCTED needs a located obstruction, RE_DERIVATION must name what it supersedes, VALIDATED needs exact evidence. |
| 6 | Circularity / strength check | `circularity.py` | Refuses a lemma that assumes (implies) the goal — a proper reduction needs a *separating witness* (holds where the goal fails). Caught the spectral-gap mis-framing. |
| 1 | Faithfulness cross-check | `faithfulness.py` | Cross-checks a model against an independent implementation at seeded exact points; a disagreement is located, not absorbed. Caught the recursion-model-unfaithful-for-cherry-trees bug. Generalizes `certify._dual_engine_check`. |
| 2 | Large-tree-limit probe | `limit_probe.py` | The anti-size-bounded-trap: evaluates a size-parameterized claim as size → ∞, locating the smallest size where it breaks or a margin degrading toward the boundary. Recurred 4+ times in the campaign. |
| 7 | Sampled → proof upgradability | `upgradability.py` | Distinguishes MECHANICAL (a finite complete cover, upgradable by exhaustion) from a CONCEPTUAL SEAM (an unbounded axis a finite sample can't cross). |
| 4 | Super-solution tester | `super_solution.py` | Exact `P ≥ T P` domination test; on a *branching* domain a pointwise pass is downgraded to an explicit caveat (the value-iteration divergence / non-local-coupling lesson) so it can't silently overclaim a global bound. |
| 5 | Discharging-conservation checker | `discharging.py` | Verifies a discharging scheme conserves total charge exactly and meets its per-node target. The Lean-machine-checked discharging (G1Discharge / G1ConsTree) lives in the origin proof repo; this is the exact invariant it rests on. |
| 3 | Exact ratio-unimodality prover | `unimodal.py`, `branching_unimodality.py` | *(pre-existing)* Clears the root, forms `r(s)=f(s+1)/f(s)`, shows it crosses 1 exactly once with exact rational crossing localization (the 529/486 closure, `R(5)=1`). |

## The discipline, concretely

```python
from telperion import validated, obstructed, null, re_derivation, decide, require_exact

# A decision NEVER hangs on a float:
if decide(margin, ">=", 0):          # both sides coerced to exact rationals
    v = validated("claim", f"margin {margin} >= 0 exactly")
else:
    v = obstructed("claim", f"violated at ... : margin {margin} < 0")

# A self-correction is owned, not edited away:
v = re_derivation("BG is about rooted Phi (max over roots)",
                  corrected_from="raw-rho competitor extremality")
```

`require_exact` refuses Python floats, sympy `Float`, and other inexact types at
any decision point; if a quantity is genuinely transcendental, bracket it exactly
first (`IntervalBracketEmitter`) and decide on the rational enclosure.

## Why #8 is load-bearing

The individual tests are only as good as the discipline of closing each with an
explicit verdict from the fixed four-state taxonomy and owning self-corrections.
That is what held the false-positive rate at zero across a very long crux hunt.
If Telperion keeps one thing from this port, it is that.  `conjecture1_proved`
stays `False` — a VALIDATED-gated fact, never a default.
