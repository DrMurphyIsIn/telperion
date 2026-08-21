# The trusted floor — Telperion pointed at its own audit calculus

*Companion to `src/telperion/metacircular.py` and `tests/test_metacircular.py`.*

Telperion's differentiator is a **meta-soundness layer above the Lean kernel**:
the kernel rejects a *false* theorem, but is structurally blind to the
meaning-level defects that live in the *statement* — vacuity, unfaithful models,
circular reductions, finite samples masquerading as proofs. The reflexive checks
(`nonvacuity`, `faithfulness`, `circularity`, `upgradability`) occupy that layer.

The fixed-point question is unavoidable: **is that layer itself sound, and what
must still be trusted underneath it?** This is the honest answer, executed in the
same exact, verdict-closed discipline as every other probe — not asserted.

## Finding 1 — the structural non-vacuity check has a *located* gap

`check_nonvacuous` is syntactic: it refuses a reflexive conclusion `t ⋈ t`. A
ring identity with distinct sides — `(a+b)² = a²+2ab+b²`, `a+b = b+a` — is
universally true, hence **vacuous as a certificate of anything specific**, yet is
not syntactically reflexive, so it slips past.

`probe_structural_nonvacuity()` exhibits these witnesses and closes
`OBSTRUCTED_AND_LOCATED`. This is not a bug; it is the **honest boundary** of the
structural layer. Catching semantic tautologies is precisely the job of the
*semantic* layer, `assert_certificate_sensitive` (a corrupted certificate must
break the claim), which the emitter-sensitivity registry
(`emitter_sensitivity.py`) now tracks across all 30 emitters.

## Finding 2 — the two layers are non-circular

If the structural check already subsumed the semantic one, the semantic layer
would be redundant. `check_metachecker_noncircular()` runs `circularity_check`
with `lemma = "structural check accepts"` against
`goal = "semantically non-vacuous"`. The ring identities are **separating
witnesses** — accepted structurally, yet semantically vacuous — so the check
closes `VALIDATED`: the layers are genuinely independent, each catching a class
the other cannot.

## Finding 3 — the trusted base is small, named, and has an undecidable floor

Self-application does **not** eliminate the trusted base. It *monotonically
shrinks and locates* it — each reflex peels off one more human-audit obligation —
and then asymptotes at an irreducible residue (`trusted_base()`):

1. **The Lean 4 kernel** — the sole arbiter of proof validity; a false theorem
   never compiles.
2. **The exact-arithmetic decision primitives** (`require_exact` / `decide`) — no
   float ever decides a verdict, so the meta-checks cannot be fooled by rounding.
3. **The statement-intent match** — whether a formal statement *means* the
   informal claim. This is **undecidable in general** (Löb/Gödel): a sound system
   cannot certify its own statement-faithfulness to an informal intent. This is
   the floor.

## Why this is the differentiator, stated plainly

Frontier provers (AlphaProof, DeepSeek-Prover, Goedel, Seed-Prover, Kimina,
Aristotle, DeepThink) all rest on the kernel as the sole gate, and their
soundness story stops at *"the kernel checked it."* Telperion's story is
stronger and more honest: **here is the minimal, named, located set of things you
must trust — the kernel, exact decision, and one undecidable residue — and
everything else, including the checks on the checks, is machine-audited.** Being
explicit about the floor is not a weakness; it is the whole point.
