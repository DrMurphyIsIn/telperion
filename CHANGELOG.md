# Changelog

## 0.1.0 (2026-08-15/16) — extraction + hardening

Born from the Brualdi–Goldwasser campaign (`../proof/`), where the pattern
produced 200+ CI-green Mathlib theorems.

**Core**: `InequalityFamily` (direct + bilinear-box), `certify()` with
structural refusals, three emitter kinds (Polya batches, ℕ-reparam adapters,
`interval_cases` assemblies), enforced certify→validate→emit→freeze workflow,
input-hash provenance, byte-stable rendering across sympy versions.

**Hardening round 1**: `diagnose` refusal triage (FALSE with exact witness /
NOT_POLYA with remedy hints / CERTIFIABLE); structural lint gate inside
`emit()`; `ShardSpec` file sharding with cross-shard imports; `telperion.toml`
manifest + `verify` drift net (fails on unlisted generate scripts);
fuzz/property tests.

**Hardening round 2**: `safe_parse_expr` token whitelist on every
string-taking surface (CLI probe/diagnose, MCP tools) — sympy's parser is
never fed raw input; `telperion init` project scaffolding (family template
with the validation discipline built in, pinned Lean shell, drift manifest,
lean-verify workflow); `certify(progress=)` + `certify -v` for long runs;
path-hashed module loading (family.py can't shadow installed modules);
`CustomAssemblyEmitter` escape hatch for hand-designed assemblies.

**The Pólya engine**: `polya_lift` (multiply through by `(1+Σxᵢ)^N` — Pólya's
theorem as an algorithm; certifies strict positivity, provably cannot converge
at equality cases) integrated as `family.auto_lift` / `polya_certify(lift_max)`;
recursive box subdivision (`auto_subdivide` on corner refusals,
`force_subdivide` to isolate tie regions) producing leaf cells plus
`SubdivisionGlueEmitter`'s `le_total` case-split glue reconstructing the
original cell theorem; diagnose now reports the exact lift exponent when one
exists, and names the tie obstruction when none does.  Toy example gains
ToyLift and ToySplit — both new shapes compile against pinned Mathlib in CI.

**Tie-variety extraction + margins** (`margins.py`, CLI `margins`/`ties`, MCP
tools): the exact equality cases of every certificate — combinatorial tie
faces via minimal hitting sets for certified (nonneg-coefficient) numerators
(with the structural corollary: certified instances have no interior ties,
which is exactly why interior-tie claims need the arithmetic treatment),
exact real roots for refused univariate claims; per-certificate margin reports
(constant-term floor + exact-rational sample minimum with argmin), tight
instances first.  diagnose now names the tie points when lifting fails.

**Wishlist 3–7**: `telperion latex` — paper appendix / leanblueprint nodes
stamped with the SAME input hash as the Lean (sync checkable by comparing two
hex strings); symbolic-tail families (`TailFrom` axis: finite table + one
``K = K₀ + t`` certificate, `TailNatEmitter` emitting the ℕ-quantified
``∀ K ≥ K₀`` theorem; the certifier's integrality check even catches int/int
float contamination in user targets); exact SOS certificates for the
rationalizable subset (even powers + iterated quadratic completion — reaches
interior-tie shapes lifting cannot; surfaced via diagnose); CAS-neutral
certificate interchange (JSON with expression ASTs + a PURE-stdlib
`recheck.py` — coefficient signs, factor positivity, Schwartz–Zippel identity
spot-checks in `fractions` — a third independent verifier beside sympy and the
Lean kernel); `certify(workers=N)` fork-parallel certification;
`telperion package` reviewer bundles (family + frozen + certificates.json +
standalone rechecker + generated REVIEWING.md).

**The honesty engine** (from a review of what made the origin proof
possible): (1) tie pinning — `family.ties`/`family.anchors` declarations; the
certifier asserts the target AND the certificate vanish exactly at declared
ties (the campaign's overclaim trap, which killed three false proofs, as a
standing invariant) and that anchors evaluate exactly (the pi(T(3,3,3)) =
19683/256 pattern); (2) the relaxation probe (`telperion relax`) — the
campaign's decisive maneuver as a tool: interpolate an integer grid axis
continuously and hunt for exact violations; ARITHMETIC verdict with witness
means no smooth certificate can close the family; (3) the adversarial hunt
(`telperion hunt`) — exact-rational minimization in three modes: coordinate
descent, GA with memetic descent refinement (the Arda evolution engine's
transferable core), and a MAP-Elites quality-diversity archive returning
DIVERSE near-tight points (tie varieties have many points; a pure minimizer
finds one — demonstrated: both basins of a bimodal tie landscape recovered
exactly). diagnose escalates from sampling to hunting before concluding
NOT_POLYA. Deliberately not ported from Arda: Rust kernels (audit surface),
island/climate machinery (overkill). Named future step: pluggable hunt
domains (the origin hunted over TREES via Prufer sequences).

**Route ledger + executable status** (the collaboration layer from the
history review): `--ledger` on diagnose/relax/hunt appends refused routes and
exact disproofs to a deduplicated, fingerprint-keyed JSON ledger
(`telperion ledger` renders ROUTES.md) — the origin's `*_nogo*` convention as
infrastructure, so nobody re-attempts a dead route blind.  `telperion status`
generates STATUS.md by EXECUTING every manifest check (theorem counts and
input hashes read from frozen manifests; verdicts never asserted), with the
origin's reminder that green certificates do not by themselves prove a
surrounding conjecture.  `telperion review-brief` fills the adversarial
review checklist with the family's actual facts — and nags when ties or
anchors are undeclared.

**Identity families + kernel facts** (second history-review run, items B+C):
`equation=(lhs, rhs)` claims — certified by exact symbolic zero-check, emitted
by `IdentityEmitter` in the proven field_simp shape with a RAW tree renderer
that preserves the author's spelling (a together-based render had produced a
vacuous `1 = 1`; construction-time evaluation caveat documented — use
UnevaluatedExpr/evaluate=False when spelling matters); identities flow through
interchange/recheck (stdlib identity spot-checks) and latex.
`ExactFactEmitter` + `fact_pow`/`int_expr_lean`: kernel integer/rational facts
in unevaluated-power spelling closed by decide/norm_num — regenerates the
origin's `s_tail_crux : (3:ℤ)^317 * 2^81 ≤ 23^129 := by decide` verbatim, and
makes VerifiedConstant brackets emittable. Closes two named-opens.

**The second-brainstorm batch (A, D–H)**: witness-search claims
(`family.witnesses` — the per-residue comparator pattern as API: existential
claims, first certifiable candidate wins, label recorded and exported: the
winner-table pattern); the sharpness probe (`telperion sharpen` — bisect a cap
between the CERTIFICATE boundary and the TRUTH boundary; the gap is the room a
better method could win — the G3/G4 cap-widening question as a tool);
`emit --pilot N` (validate the template on N instances in CI before a
972-theorem batch — the campaign's first-try-green ritual as a flag);
`telperion cilog` (the Lean-failure knowledge base: seven hard-won gotcha
classes as executable diagnostics, error COUNT always reported first);
`per_node_family` + `fixed_points` (the telescoping-potential shape's
achievable half: per-node inequality families with the step map's fixed point
as the pinned tie — full induction emission stays the v2 headline); exact cone
membership (`cone_combination` — target = Σ λᵢ·basisᵢ with λ ≥ 0 decided in
exact rational arithmetic; the LP cutting-plane maneuver's solvable core,
float-guided LP for the underdetermined case named-open).

**Named open items** (deliberately not shipped as stubs): `python-flint` fast
path (sympy expand/together dominates the profile, so a flint coefficient pass
would be decorative until the conversion layer is done properly);
bilinear-family built-in assembly (use `CustomAssemblyEmitter`); Kind-3
multi-axis grids; the SOS Lean-emitter path (certificates found by sos.py are
surfaced in diagnose but not yet emitted — needs a squares-aware skeleton);
incremental per-instance certification caching; bilinear tails; retrofitting
the R7 star-of-hubs family onto the witness API (it hand-rolls the search);
float-guided LP for underdetermined cone membership; generic induction
emission for telescoping potentials (the v2 headline); hunt over pluggable
combinatorial domains.
