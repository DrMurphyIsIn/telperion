# Audit independence: what the 2026-09-19 to 2026-09-22 testimonies are, and the rule from now on

`conjecture1_proved = False`. Nothing in this note retracts a proof. Every Lean artifact the
registry calls `proved` has been rebuilt and its axioms printed under independent reads
(CLOSURE_RUN_2026-09-22.md section 2: 103 nodes, no critical finding). What this note
corrects is the *record of who checked the statements*, and it changes what the registry
will accept from now on.

## 1. What happened

Every `AUDIT_TESTIMONY_*.md` in this directory dated 2026-09-19 through 2026-09-22, and the
read-backs they back in `telperion/missions/*/nodes/*.toml`, were produced by **subagents of
the session that wrote the proofs**, committed under the same git identity as the proof
commits (`228240291+DrMurphyIsIn@users.noreply.github.com` for all 33 testimony commits and for the artifact
commits they vouch for). The word *blind* in those files means the auditor **did not read the
node title or the roadmap** before rendering the formal statement. It does **not** mean a
different principal. A subagent spawned by the authoring session, running under the
author's account, with a prompt the author wrote, is the author for the purpose of the
independence rule in MISSIONS_DESIGN_2026-09-11.md section 8.

The rule was not broken out of shortcutting. It lived in one paragraph of the design
document and nowhere a session actually reads (MISSIONS_ARCHITECTURE_AUDIT_2026-09-19.md
section 4d): `mission audit` took a free-text `--auditor`, nothing recorded who registered a
statement, and `promote_to_open` checked only that a read-back existed. A session that read
the how-to and audited its own node had followed the instructions it was given.

Why it matters even though the Lean is fine: the read-back is the only check on
*vacuity* -- whether the formal statement says what the title claims. `grant` is containment
against the very statement the author wrote; the kernel checks the proof, not the
proposition's meaning. If the author's own subagent is the only reader, the strongest link
in the chain has one principal behind it.

## 2. What the registry now records

Governance commit `missions: record provenance; refuse self-audits; pin grants to digests`
(branch `missions/grant-provenance`):

* `mission add` writes `[author] {identity, session, date}` (`git config user.email`,
  `$CLAUDE_SESSION_ID` or `--session`; both required).
* `mission audit` writes the auditor as `{auditor_identity, auditor_session}` inside
  `[readback]` plus `independence`, and **refuses** when the session or the identity is the
  author's, when the text is under 120 characters, or when it only repeats the title.
  Nothing is written on refusal. `--auditor` is now a display label.
* `mission grant` writes `[grant] {artifact_sha256, statement_sha256, gate_version, date,
  identity, session}`; `mission verify` recomputes both digests and fails on a mismatch, and
  fails a proved node whose read-back is a self-audit.
* Every read-back that existed on 2026-09-23 (117 across the four campaigns) carries
  `independence = "unverified"`. No status changed; no testimony was deleted or edited.
* A node may declare `requires_ci_job = "<workflow>:<job>"` (owner ruling 2026-09-24, for
  artifacts verified only by a non-required job such as the anduril kernel ladder). The
  gate then refuses to grant, and `verify` refuses a proved status, unless `mission
  ci-record` has stored a `success` run of exactly that job on the current artifact
  digest (`[ci_record] {workflow, job, run_id, head_sha, artifact_sha256, conclusion, date}`).
* `mission provenance-report` lists, per campaign, the proved nodes with no independent
  read-back and no passing judge run. On 2026-09-23 that is every proved node:
  anduril 6/6, bg 9/9, mirrormere 38/38, rh 53/53.

None of this is unforgeable. A session can supply any identity string for itself or for a
subagent. What it buys is a record the next reader can check against `git log` and the
attempts ledger, and a CLI that will not write a self-audit unless it is lied to.

## 3. The rule

A read-back counts as **independent** only if one of the following holds:

1. **Different principal.** Its `auditor_session` differs from the node's `[author].session`
   **and** its `auditor_identity` differs from `[author].identity`. A subagent you spawned
   is your session and your identity. `mission audit` records this as
   `independence = "independent"`; it refuses anything else.
2. **The independent judge passed.** The `missions-comparator` job (openai/ten-proofs
   Comparator, `.github/workflows/missions-comparator.yml`) passed on the node, and the run
   is recorded with `mission comparator-record <Slug> --run-id <run> --theorem <name>`. The
   judge certifies that the artifact proves exactly the *registered* formal statement,
   kernel-clean under two kernels; it does not read the title, so it settles the
   proof-matches-statement question, not the statement-matches-title question. Both are
   needed for a node to leave the provenance report.

Everything else -- a legacy read-back, a read-back on a node with no `[author]` block, a
testimony from a same-account subagent however careful -- is `unverified`. Unverified is not
an accusation; it is the honest label for evidence whose independence nobody can establish
after the fact.

## 4. What the judge is and is not independent of

The Comparator run is independent of the author in three concrete ways: the statement it
checks is taken from the registry file (hash-pinned; the committed challenge is regenerated
and diffed in CI), not from the artifact; the checker is a separate program built from a
pinned upstream tag, with a separate Rust kernel (nanoda) replaying the export; and it runs
on a GitHub-hosted runner from a clean checkout. It is **not** independent of the island's
vocabulary: the registered statement is elaborated in the artifact's own namespace and
`open` context on the island, not against the campaign's vocabulary mirror
(`Statements.RHDefs`, `MMDefs`), because the Comparator needs both sides in one Lake
workspace. The judge step raises the process stack limit (`ulimit -s unlimited`, 4 GB
fallback) before invoking the Comparator: nanoda replays proofs recursively and the large
`decide +kernel` certificates of the KWin artifacts overflowed the 8 MB main-thread stack
(#615, run 36055910789); a stack overflow is a runner limit, not a verdict, and the job
says so. With the stack raised, the same certificates exhaust the runner's 16 GB under
nanoda instead (the runner is killed mid-replay). A node may therefore declare
`heavy_certificates = true`: the judge then asserts it with `enable_nanoda = false` (Lean
kernel replay and axiom whitelist still run), the shard provisions swap for the Lean
replay, and the record must be written with `mission comparator-record --lean-kernel-only`,
which stores `second_kernel = "none: heavy_certificates"`; `provenance-report` prints such
nodes as "Lean kernel only". One kernel instead of two is a weaker verdict and is
labelled as such, never silently. Whether the mirror still matches the island is `missions/mirrors.py` and the
islands' `generate.py --check` jobs. Whether the island's `DBN.H` is the de Bruijn-Newman
`H` is the read-back's job. The judge closes the gap between the two: given the vocabulary,
the artifact proves this proposition and nothing weaker.

Coverage on 2026-09-23: the `dbn` island (3 nodes), the `rvm_bridge` island (52 nodes,
four shards) and the `zeta_reflection` island (9 of 10 nodes: `AND_g2_reflected_band`
declares a namespace inside its statement, which the bridge cannot reproduce beside the
artifact; it is reported, not skipped) are wired; `li_positivity` (24 nodes) renders and is
listed but not yet run; `quasicrystal` (7 of 8: `MM_leakage_composite_zero` carries local
`def`s), `zero_free_bridge` (1) and `zeta_zero_localization` (3; monolith lakefile, cannot be
path-required) are not wired. BG's nine nodes are judged by `proof-comparator.yml` in
self-check mode (no independent statement; statement identity there is by human review).

## 5. What a session should do now

* Registering a statement: `mission add ... --session "$CLAUDE_SESSION_ID"` (identity is your
  git email). Then **ask a different session, under a different account, to run
  `mission audit`.** If you cannot, leave the node in `draft`; a draft is honest.
* Auditing: render the formal statement in your own words -- what it quantifies over, what
  it concludes, what could make it vacuous -- and run `mission audit <Slug> --text "..."
  --session "$CLAUDE_SESSION_ID"`. Do not read the title first. If the CLI refuses you as the
  author, that is the rule working.
* Granting: `mission grant <Slug> --session "$CLAUDE_SESSION_ID"`. The `[grant]` block is
  written for you. Then, once `missions-comparator` is green on your PR, record the run.
* Reviewing an existing proved node: `mission provenance-report <campaign>`. A node on that
  list has a kernel-checked proof and an unverified reading of its statement. Treat the
  title as a claim, not a fact, until someone independent has read the Lean.
