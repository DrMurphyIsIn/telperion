# Step 6, Task 2b: fingerprint covers local inductives and auxiliary proofs (plan, lead, 2026-11-01)

**Why.** Contrarian assignment #18 ran `telperion fingerprint` on the four riemann-jensen challenge theorems at f90d983. All
four were REFUSED, failing closed:
- `exists_*` and `unique_*` depend on `RiemannJensen.IsDedekindZetaContinuation`, a local `structure`, i.e. an inductive;
- `dedekind_thm_main` depends on `RiemannJensen.riemannXi._proof_1`, a theorem;
- `riemannJensen_main` depends on `RiemannJensen.nonrealRootCount._proof_1`, a theorem.

The docstring of `src/telperion/checks/fingerprint.py` already names the fix as "a later extension". The owner chose
"Extend Telperion" on 2026-11-01. Without the extension the island cannot reach `verified`, which needs a recorded
fingerprint per theorem.

## Requirements
1. **Local inductives (and structures).** When a non-library inductive `I` is left after unfolding, either as a constant
   (`I`, a constructor or a recursor) or as a projection's structure, it is no longer refused. Instead the serialization gets
   a DECLARATION BLOCK for `I`'s whole mutual/nested group, emitted once per fingerprint in a deterministic order (by first
   occurrence). The block includes, for each inductive in the group:
   - its name;
   - its level-parameter COUNT (numbered positionally, as for the target);
   - its type;
   - numParams, numIndices, isRec, isUnsafe, isReflexive and isNested;
   - all constructors in order, each with its name, numFields and type.

   Everything in the block is serialized with the SAME `tpSer`, after the SAME `deltaExpand`. The block is recursive: any
   further local inductive found inside it gets its own block. Mutual groups (`all`) are emitted together. Recursors are not
   serialized; they are determined by the declaration, so a reference to `I.rec` or to a constructor hashes by name plus the
   block. Names stay part of the hash, exactly as library constant names are.
2. **Auxiliary proof constants.** A non-library THEOREM is accepted only if it is an auxiliary lemma: its name's last
   component matches `_proof_<n>` (or Lean's other internal proof-auxiliary forms: `_auxLemma`, `match_<n>` proofs). It is
   then serialized as `(prf <its type, fingerprinted recursively>)`. By proof irrelevance any two proofs of the same Prop are
   definitionally equal, so this is faithful. Every other non-library theorem stays REFUSED, so a user `theorem` cannot slip
   through. A non-library axiom, opaque or quot stays REFUSED.
   **Amended by the Ruling (lead, 2026-11-05) below: every non-library theorem is accepted by its type.**
3. **Injectivity and determinism.** The new tags must be self-delimiting and must not collide with the existing ones.
   Re-running gives byte-identical output. Two statements that differ only in a local inductive's constructor type, field
   count or parameter count must hash differently.
4. **Unchanged behaviour for existing inputs.** Every existing fingerprint in the test suite and in recorded ledgers must
   keep its hash, so statements with no local inductive or aux proof serialize byte-identically to f90d983. Add a regression
   test that pins at least three previously recorded hashes.
5. **The size cap** (`2^22`) counts the declaration blocks too.
6. **Docstring:** update "WHAT IS HASHED" and "WHAT IS REFUSED" to match.

## Tests (TDD; `tests/test_fingerprint.py`; Lean tests are under `@lean` and run with TELPERION_LEAN_ENV set)
Positive:
- a statement over a local `structure` fingerprints;
- two copies of the same structure under the SAME name in different modules hash equal;
- a statement whose definition's value contains `_proof_1` fingerprints;
- recursion: a structure whose field is another local structure.

Negative controls, each of which must give a DIFFERENT hash or a REFUSED:
- (a) the same structure with one field's type changed;
- (b) an extra field;
- (c) a renamed constructor;
- (d) an inductive whose constructor order is swapped;
- (e) a user-declared non-auxiliary `theorem` referenced through a definition stays REFUSED;
- (f) a local `axiom` stays REFUSED;
- (g) a theorem NAMED like `foo._proof_1` but declared by the user as an ordinary theorem.

On (g): Lean lets you declare `theorem foo._proof_1`. Decide the policy and justify it in the docstring. Is it acceptable,
given that by proof irrelevance only its TYPE is hashed? If it is accepted, the test must show that the hash is of the type
and that a false-typed lemma cannot change what the statement says.

Plus a mutual inductive pair, and the regression pins from requirement 4.

## Constraints
These are the step-6 Global Constraints, plus:
- Work ONLY in the worktree `~/telperion-wt-fp` (branch `step6-fp-closure`, from f90d983).
- Every lean or lake command goes through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`. Never run lake on a shared
  packagesDir, and never run `lake update`.
- The pinned env is `TELPERION_LEAN_ENV=~/telperion-tools/lean-env` or whatever the existing Lean tests use; check
  `tests/test_fingerprint.py`.
- No git: the lead commits. No external code run.
- Do not edit `~/.claude`, `~/telperion-repo` or `~/telperion-tools/research-main`.
- Run the full non-Lean test suite plus the Lean fingerprint tests. Report counts.
- The report is your final message, ≤ 20 lines, with the full detail in `docs/superpowers/plans/...-REPORT.md` in the
  worktree.

## Ruling (lead, 2026-11-05)
This amends requirement 2 and test (e). It follows bb's plan review REVIEW_PLAN_FP_CLOSURE (0aefdf7b), pre-flag 1, which
offered two options; this ruling takes the first. No owner decision is on record for it.

- **Every non-library theorem is accepted by its TYPE**, `(prf <type>)`, whatever its name. No `_proof_<n>` regex and no
  `Name.isInternal` test selects which. `match_<n>` is dropped: matchers are definitions and already unfold.
- **Why it is exact: proof irrelevance.** Any two proofs of one Prop are definitionally equal, so the type is all the
  kernel sees of a theorem.
- **The premise is a Prop type, and the kernel enforces it.** The kernel rejects a theorem whose type is not a
  proposition. bb probed this on v4.34.1 and v4.35.0: a Nat-typed `thmDecl` gives "(kernel) type of theorem … is not
  a proposition". The replay re-adds every untrusted constant through that kernel. As defence in depth, `tpBuildCtx`
  re-checks the type with `Meta.isProp` and refuses `non-prop-theorem`.
- **Why no name test.** It would protect nothing: a refused `theorem lem` inlined into a definition is lifted by the
  elaborator to `f._proof_1`, which any name test accepts. It would also make the hash depend on a name.
- **Consequences.**
  - Test (e) becomes a positive control. `⟨3, lem⟩` hashes as `⟨3, by omega⟩`, and a lemma of another type hashes as
    another statement.
  - Test (g) is answered by the same policy: `foo._proof_1` is accepted and hashed by its type, and `foo._proof_1 :
    False` gives a different statement.
- **What guards a sorry inside a proof.** It is invisible to the fingerprint. The guard is the proof-side axiom audit
  (`CLEAN_AXIOMS` over the replay's `collectAxioms`). `Fingerprints.axioms` alone is not that guard: a mission statement
  file carries its own `:= by sorry`, so `sorryAx` is always listed there (bb's review of 3c49ed0, R-2).
