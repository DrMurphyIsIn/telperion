# The tactic contract

The default skeletons assume these Mathlib tactics, in these roles. If your
Mathlib pin changes their behavior, override the skeleton via
`LeanProfile.skeletons` rather than editing generated files.

| Tactic | Role in the templates | Notes |
|---|---|---|
| `simp only [...]` | unfold the emitted coefficient defs + the profile's `unfold_lemmas` | never bare `simp` — closed lemma lists keep output stable |
| `push_cast` | normalize ℕ→ℝ casts before ring normalization | matters once reparameterization adapters land |
| `field_simp` | clear denominators in `hkey` identities | **matches `≠ 0` hypotheses syntactically** — hence the factored-denominator spelling rule and the per-factor `have hdN : f ≠ 0 := by positivity` lines |
| `ring` / `try ring` | close the cleared identity | `try` because `field_simp` sometimes closes the goal itself, and a trailing `ring` on no goals is an error (origin campaign gotcha); if `try ring` leaves a goal, the build still fails loudly with "unsolved goals" |
| `positivity` | discharge `0 ≤ num/den` for all-nonneg numerator over positive-factored denominator, and every `≠ 0` side hypothesis | the workhorse; requires the Polya form the certifier enforces |
| `nlinarith` | inside the user-supplied corner combinator only | not emitted by the tool itself |

Compile-cost knob: `LeanProfile.options = ("set_option maxHeartbeats 1000000",)`
for large batches. The origin campaign needed 4,000,000 for its heaviest
generated file; budget accordingly and shard large families across files.

Known-good pin: Lean `v4.32.0` + Mathlib `v4.32.0` (the toy example's lake
manifest, compiled in CI on every push).
