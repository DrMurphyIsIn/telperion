# Honesty patterns — the methodology, as checkable modules

Eight reusable "meta-skill" patterns distilled from the Brualdi–Goldwasser crux
campaign, where 20+ probes closed with a **zero false-positive rate**.  The
patterns most worth keeping were not the ones that ran a specific probe — they
were the ones that **caught false positives**.  This is that discipline ported
into Telperion: each pattern is a small module whose checker returns a
`ProbeVerdict`, decided in exact rationals, never on a float.

The load-bearing one is #8.  Every other pattern is only as trustworthy as the
discipline of closing it with an explicit verdict and owning self-corrections.

A second family, #9 to #12, was distilled on 2026-09-22 from the RH formalization
campaign (`SHAPES_AUDIT_48H_2026-09-22.md` section 5).  Those four are **gate-side and
kernel-side**, not probe-side: they are disciplines for CI greps, registry scans,
conditional theorems and residual accounting.  They are written up below with their
instances and their recommended mechanism; unlike #1 to #8, they do **not** yet have
checker modules, and this file does not pretend otherwise.

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

---

# The gate-side family: #9 to #12

Distilled 2026-09-22 from four cluster audits over PRs #583 to #596
(`SHAPES_AUDIT_48H_2026-09-22.md` section 5).  Where #1 to #8 ask whether a probe told
the truth, these ask whether a **gate** can tell the truth: whether it can fail at all,
whether a hypothesis is doing work, whether a statement is trivial, and whether the open
content is written down.  No module implements them yet; each names the mechanism it
wants.

## #9 Gate non-vacuity: every refusal gate ships a positive control that trips it

A gate that silently matches nothing passes forever.  A grep, a drift scan or a count pin
is not evidence until something is shown to make it fail.

Instances: the mirror-drift test that asserts its own scan is non-empty
(`tests/test_missions_mirror_drift.py`); the anti-phantom probe that corrupts an exponent
and asserts refusal; the axiom-line floor that fails when the guard prints too few lines;
the anchored `'Name' (depends on axioms|does not depend)` match adopted after a bare
substring check was satisfied by a *longer* name, so the lemma it claimed to guard never
printed at all.  The emitter-side instance is a refusal with a located witness, as when a
positivity certificate is refused at the first degree where a negative point exists.

Mechanism: the negative-control harness already enforces this for emitters.  #9 is the
same discipline for CI greps and registry scans, which currently have none.

## #10 Load-bearing-hypothesis twin

A conditional theorem ships a kernel witness that deleting its hypothesis makes it false.
This is the kernel-side form of pattern #6: #6 refuses a lemma that assumes its goal, #10
refuses a hypothesis that was never needed.

Instances: `leak_dh_multiplicativity_is_necessary`, `probe_hypothesis_is_load_bearing`,
`orthogonality_is_load_bearing`, and the non-vacuity twins beside them.  In this session's
own work, the ladder's angle bound is stated only for `|Im rho| >= 1` because it genuinely
fails below about 0.285, and the audit confirmed the hypothesis is load-bearing rather
than defensive.

Mechanism: a `--twin` face for conditional emitter kinds, so the twin is emitted rather
than remembered.

## #11 Triviality tiering by unfolding probe

A statement is probed with `rfl`, `simp [defs]`, `decide` and `aesop`, each expected to
FAIL.  A success is a finding, not a convenience.  Three tiers: definitional, classical,
new.

Instances: a torus dictionary node that `simp [defs]` closes outright (tier 1, and on that
evidence the node was deprecated rather than granted on 2026-09-22); a leakage node where
all four tactics fail on the first conjunct (tier 2); a probe file carrying fourteen
expected failures.

Mechanism: pin "every `example` errors" rather than a count.  A count pin breaks silently
when a probe is added, and it reads as a pass when the file fails to load at all.

## #12 Named-residual ledger

A conditional proof names its residual as a `def : Prop`, the registry lists it, and the
axiom guard alone is never the grant.

This is the pattern the axiom guard cannot see.  A capstone conditional on two named
hypotheses prints exactly the three standard axioms *because* its open content is a
hypothesis; the guard is clean precisely when the mathematics is not finished.  Instances:
a box probe taking `SecondDerivBoundOnBox` and `GridModulusLowerBound`; the rh reduction
ladder where each rung's obligation is a `def : Prop` and never a `sorry`;
`NoRealZeroInStrip` carried as a named `Prop` and later discharged from a proved box.

Mechanism: a registry field `[proof] open_obligations = [...]` that the grant gate must
find as `def` or hypothesis names in the artifact, and that the node title must print.
The accounting failure this catches is a registered statement whose text does not mention
the objects its title claims to be about.

## Three notes under #8

- **Crash is not a verdict.**  A tooling failure is `NULL`, never `OBSTRUCTED`.  Run the
  matrix, check the exit status, *then* grep.  A `ModuleNotFoundError` was once read as
  "the clause no longer rejects", and `tee` has masked a non-zero exit from Lean.
- **A boolean without a provenance field cannot carry a ruling.**  A `closure_clean` field
  recomputed as `status == "proved"` laundered a deliberate `False`; a stored `False` needs
  a `closure_override_reason` beside it.
- **Write the trust ladder once.**  kernel > arb > mpmath-numeric, where the last is
  EVIDENCE, NOT A PROOF, belongs in the README trust-model section rather than being
  re-derived in each memo.

`conjecture1_proved` stays `False` here as everywhere: a VALIDATED-gated fact, never a
default.
