# Telperion Missions Registry — Quick Start

The missions registry tracks proof campaigns (BG, RH) as directed graphs of nodes with status, artifact links, claims, and work history. This HOWTO covers the essentials for picking up work in an active campaign.

## Status Machine

Every node flows through statuses enforced by the kernel:

```
draft ──(read-back recorded)──────────────> open
open ──(verified artifact linked)─────────> proved | refuted
any ──(with deprecated_reason)────────────> deprecated
```

**Key rule:** `proved` and `refuted` are **granted only by the kernel** via `mission grant` (which checks artifact existence and normalized statement containment — a syntactic, local gate). A node may link an artifact, but until the gate verifies the statement match, the status stays unchanged. The KERNEL authority for whether the artifact's Lean proof actually elaborates is the artifact's home package's own CI (e.g. proof-lean for BG; the home island for RH cross-island nodes); `mission grant` does not re-run that build. Pass `--deep-lean` to `mission verify` to lake-build the campaign's statement package (statements elaborate; proofs are not re-checked here). For reductions (proofs that import sorry-statements of other open nodes), the flag `closure_clean: false` until the entire import closure is sorry-free.

## Claims & the Claim Protocol

A claim reserves a node for one session for a TTL (default: 24 hours). Claims are **advisory, not locks** — they coordinate work but don't block other sessions. An expired claim can be claimed-over; the new claim records that it superseded the old one.

- **Claim:** `telperion mission claim <node-slug> --session <your-session-name> [--ttl 24] [--note "intent"]`
- **Release:** `telperion mission release <node-slug> --session <your-session-name>`
- **Check status:** `telperion mission open-leaves` (hides claimed nodes by default; use `--all` to show them)

## The Verbs

| Verb | Purpose |
|------|---------|
| `status [campaign]` | Print one-glance tree: all nodes with status, closure_clean flags, who claimed them |
| `open-leaves [campaign] [--all]` | List nodes ready to work on: open, all dependencies proved, not freshly claimed (or include them with `--all`) |
| `claim <slug> --session S` | Claim a node; TTL default 24h |
| `release <slug> --session S` | Release a claim |
| `add <campaign> <name>` | Scaffold a new node (creates both .toml and statement file in draft status) |
| `audit <slug> --text "..." --auditor "name"` | Record a human-language read-back and promote draft → open |
| `link <slug> --artifact P --kind K --via V` | Attach a proof/disproof artifact (K: `lean_module` or `frozen_cert`; V: `direct` or `reduction`) |
| `attempt <slug> --session S --route R --verdict V --detail D` | Log a work attempt; verdict: `Proved`, `Refuted`, `NoGo`, `Stalled` |
| `grant <slug>` | **Gate verb:** run CI verification and flip `proved`/`refuted` (only verb that changes status) |
| `verify [campaign]` | Run the shallow coherence battery locally (node schema, DAG acyclicity, artifact existence, normalized statement containment) — read-only; add `--deep-lean` to also lake-build the campaign's statement package |
| `graph [campaign]` | Emit DOT export of the dependency DAG with node statuses |

## Five-Minute Quickstart

1. **Check the frontier:**
   ```bash
   telperion mission status demo
   telperion mission open-leaves demo
   ```

2. **Claim work:**
   ```bash
   telperion mission claim node_slug --session your-session-id
   ```

3. **Do the math.** Edit your local branch, write Lean, build, verify kernel checks.

4. **Log the attempt (always):**
   ```bash
   telperion mission attempt node_slug --session your-session-id \
     --route "emitter_name or tactic_approach" \
     --verdict Proved --detail "artifact path or summary"
   ```

5. **Link the artifact (if proved/refuted):**
   ```bash
   telperion mission link node_slug --artifact path/to/proof.lean \
     --kind lean_module --via direct
   ```

6. **Grant the status (invoke the gate):**
   ```bash
   telperion mission grant node_slug
   ```
   The gate checks: artifact exists and its normalized content contains the registry statement (syntactic, local — no Lean build). If both pass, status flips to `proved` (or `refuted` for disproofs). The KERNEL authority for the proof's elaboration is the artifact's home package CI, not this gate. If closure_clean was false (reduction), it's recomputed.

7. **Release the claim:**
   ```bash
   telperion mission release node_slug --session your-session-id
   ```

## MCP Tools (for Claude Code / agents)

Two read-only tools in the Telperion MCP server:

- **`mission_status(campaign="")`** — Return a status tree (all campaigns if `campaign` is empty).
- **`mission_open_leaves(campaign="", include_claimed=False)`** — Return the live frontier. Pass `include_claimed=True` to show claimed nodes.

## Key Discipline

- **Always log attempts** (even NoGo / Stalled), so future sessions don't re-walk dead paths.
- **Read-back before open:** A `draft` node needs a human-language `audit` (prose or Lean statement rendering) before it can move to `open`. This catches "formalized the wrong statement" early.
- **The kernel is the sole authority:** No manual status edits. Only `mission grant` (with CI verification) flips `proved`/`refuted`.
- **Claims are soft:** Respect TTL and claim-over etiquette, but don't block other sessions.

## For Parallel Sessions

The registry is git-backed: one file per node, one append-only attempts ledger. Claim files are committed; git merge handles the rest. Collision-guard conventions (arda-style) continue to protect races.
