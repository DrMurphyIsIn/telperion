# RUNNER SHARD DESIGN — C2 (multi-node campaign runner) + B2 (lake package sharding)

*(PROGRAM ANDÚRIL WS-C2 + WS-B2. `conjecture1_proved = False` — this is finite
verification scaffolding, not a proof of RH.)*

## Problem

`campaign.py` today is a single-node orchestrator whose durable state is one
`campaign_state.json` holding **every** band's completion record in one dict.
Two things break at scale:

1. **O(N²) state writes.** `save_state()` rewrites the WHOLE JSON on every band
   completion. At T=80000 the file is ~2030 bands; a full T=10⁶ run is tens of
   thousands. Rewriting the entire file per band completion is quadratic in
   total bytes written and serializes all lanes through one file.
2. **No horizontal scale-out.** All bands run in one process against one state
   file. To use a cluster (charter decision 2: "height-sharded multi-node
   support designed in from the start"), height ranges must run in independent
   processes/nodes with independent state, then merge.

B2 is the Lean-side analogue: one `lakefile.toml` with a `defaultTargets` array
of thousands of module names (already >2000 at T=80000). This is one build unit;
it grows unboundedly and every band touches the same file.

Both are fixed by the SAME idea: **partition by height block.** Bands are
planned deterministically per 1000-height `BLOCK` (`plan_bands`), and every band
lies entirely within one block (block edges land on round 1000s). So a height
block is the natural shard AND the natural lake package.

## Shard model — height blocks

- A **shard** is a contiguous height range `[FROM, TO)` aligned to (or a union
  of) `BLOCK`-sized (1000-height) blocks. `plan_bands(FROM, TO)` is the shard's
  band list; because band edges never straddle a 1000-block boundary, a shard's
  band set is disjoint from any other non-overlapping shard's — EXCEPT for the
  shared partition edge (see below).
- Each shard owns an **append-only journal** `state/shard_<FROM>_<TO>.jsonl`:
  one JSON record per band completion, appended (never rewritten). This is the
  O(N) fix — each completion is one `open(…, "a")` + `write` + `fsync`, no
  whole-file rewrite.
- Shards are independent processes/nodes. Merge is a separate, explicit step.

### The shared boundary edge

Horizontal-edge Platt caches (`edge_stretch.json`) are shared between ADJACENT
bands: the interior edge between band `i` and band `i+1` is priced once. Across a
shard boundary at height `H` (a 1000-multiple), the last band of shard
`[…, H)` and the first band of shard `[H, …)` both touch the edge at `H`. Both
shards may independently price it (a Platt `zeros_in_interval` query, ~0.3s).
This is **idempotent**: the stretch result for a given edge is deterministic, so
both shards compute the same `down:H` / `up:H` value. The cache write is
last-writer-wins with identical content. No correctness issue; at most one
redundant ~0.3s Platt query per shard boundary. The merge step unions the
per-shard stretch caches (below) so subsequent runs pay it zero times.

## Journal record format

One JSONL line per band completion. Superset of today's in-memory record plus
the identifying `tag` (so a journal line is self-describing and mergeable):

```json
{"tag": "1d4000000_3999999d4000000_4000_4040", "den": 4000000,
 "lo": 4000, "hi": 4040, "status": "ok", "n": 43, "density": 1.0,
 "prec": 300, "secs": 2.2, "route": "t5", "ts": 1757000000.0}
```

- `tag` = `band_tag(den, lo, hi)` (nominal edges) — the same key used in
  `campaign_state.json["bands"]`, so a journal replays 1:1 into legacy state.
- `status` ∈ {`ok`, `refused`}; refused records carry `error` instead of `n`.
- `ts` = completion wall-clock (float epoch), for last-writer tie-breaking on
  identical-`tag` duplicates within one journal (resume re-runs).

**Resume semantics.** A shard run reads its own journal on startup, folds it to
the latest record per `tag` (max `ts`), and skips bands already `ok`. Identical
to today's `cmd_emit_bands` skip logic but sourced from the journal instead of
the monolithic state. A crash mid-band loses only the in-flight band (never
journaled) — the next run re-emits it (idempotent; the Lean file + cert sidecar
overwrite deterministically).

## Merge semantics

`merge-shards` rebuilds a unified view from journals:

1. **Collect** all `state/shard_*.jsonl` (or an explicit list).
2. **Fold** each journal to latest-per-`tag` (max `ts`).
3. **Conflict assert on overlap.** If two DIFFERENT shards both have a record
   for the same `tag`, their *decision* must agree: same `status`, and for `ok`
   records the same `n` (the zero count is the load-bearing fact; `secs`/`ts`/
   `density`/`prec` are run-metadata and may differ — a band re-emitted at a
   higher retry-ladder density still certifies the same `n`). A mismatch in
   `status` or `n` is a hard error (`AssertionError`) — it means two nodes
   disagree on a certified count, which must never be silently merged.
   - This only fires on the shared boundary edge case or on operator error
     (overlapping shard ranges). The boundary bands themselves have DIFFERENT
     tags in adjacent shards (band edges don't straddle the boundary), so in
     the normal aligned-block case there is NO tag overlap at all; the assert is
     a safety net for misconfigured ranges.
4. **Emit** a unified `campaign_state.json`-shaped dict (`{"bands": {tag: rec}}`)
   — byte-compatible with the legacy single-node reader, so all downstream
   (`status`, `emit-segment`, `verify-bands`) works unchanged on the merged
   view.
5. **Union stretch caches.** Merge every `state/shard_*.edge_stretch.json` (and
   the global `edge_stretch.json`) into the canonical `edge_stretch.json`,
   asserting identical values on key collisions (deterministic, so collisions
   agree). No entry is lost.

### Merge with the LIVE root-owned state in `~/arda-million`

The production climb runs as root from `~/arda-million` and writes the monolithic
`campaign_state.json` there. Integration path (spelled out for the operator):

- `merge-shards --into <path>` folds journals INTO an existing legacy state file
  rather than emitting fresh: it loads `<path>` (the live state), overlays the
  journal-folded records, applies the same conflict assert against the live
  records, and atomically rewrites `<path>` (tmp + `replace`, matching the
  existing pattern). A band already `ok` in the live state with the same `n` is a
  no-op; a differing `n` aborts the merge (loud) rather than corrupting the live
  record.
- Because the live file may be root-owned, the merge must run with write access
  to it (root, or after `chown`). The tool never writes unless every record
  reconciles — a failed assert leaves the live file untouched (tmp discarded).
- **Open question for integration:** whether the live climb should itself switch
  to journal mode (`emit-bands --journal`) so there is no monolithic file to
  reconcile at all, or keep the monolith and only fold shard journals in at
  milestone boundaries. This design supports BOTH; recommendation is to keep the
  live climb on the monolith for now (zero disruption) and use journals only for
  farmed-out cluster shards, merging at each leg assembly.

## Compressed per-zero certificate record format

The Ω(N) mass (charter: 30–300 TB at 10¹³). The band records above are ~one per
~43 zeros; the per-ZERO archive is the bulk. Target: **≤ ~30 bytes/zero.**

Format: per height block, a gzipped JSONL (`certs/zeros_<FROM>_<TO>.jsonl.gz`),
one record per zero:

```
{"i": 0, "band": "…_4000_4040", "lo": "...", "hi": "..."}
```

where `lo`/`hi` are the dyadic bracket ordinates (the refinement pass's isolating
interval for that zero). To hit the byte budget we DON'T store full rationals per
zero — instead:

- **Delta-of-dyadic encoding.** Within a block the zero ordinates are monotone
  increasing and densely spaced (~1/density apart). Store the block's base
  ordinate once, then per zero a small integer delta (the low bits of the dyadic
  mantissa relative to the previous zero) plus a bracket half-width exponent.
  Typical delta fits in 2–4 bytes; the exponent 1 byte; the band id is implicit
  from position (zeros are grouped by band). Gzip over the JSONL then removes the
  residual key/whitespace overhead.
- Measured target: raw ~44 B/zero (driver-scout §4) → ~10 B gzipped for the
  numeric-only delta stream; the ≤30 B/zero budget holds with room for the band
  attribution index.

The compressed record is written by the REFINEMENT pass (not the sign-count
sweep), feeds both the Bragg/B0 archive and the 10¹³ external-storage archive,
and is independent of the band journal (band journal = "this range is certified";
zero archive = "here are the isolating brackets"). This design specifies the
FORMAT and the writer/reader API; the refinement-pass producer is a separate
deliverable (it needs the per-zero brackets the current sweep discards).

## B2 — Lake package sharding

Today: one `lakefile.toml`, one `defaultTargets` array with every module. B2:
one lake **package per 25,000-height block** (charter §B2 / concrete-design B2),
plus a shared core package and an umbrella.

- **`zzl_core/`** — the height-independent core: `TuringBand`, `RHInBox*` atoms,
  `DiffractionCore`, `AllZerosUpToHeight`, `ZetaZeroConfinement`, `StripClear`,
  the Dlvp modules. Every block package `require`s it.
- **`ZetaBands_h<BLOCKTOP>/`** (one per 25000-height block, e.g.
  `ZetaBands_h25000/`, `ZetaBands_h50000/`) — the band modules
  (`RHInBoxT_*`) and the segment/capstone chain files (`AllZeros_h*`) whose top
  falls in that block. Each has its own `lakefile.toml` with its own
  `defaultTargets` (only ITS modules) and `require zzl_core`. Bounded size: ≤ one
  block's worth of modules regardless of total campaign height.
- **Umbrella** (`lakefile.toml` at the island root) `require`s every block
  package + `zzl_core`. The capstone chain composes ACROSS packages via the
  conclusion-level `AllZerosUpToHeight.height_chain` (package-agnostic — it only
  sees conclusions, per chain-scout §1), so a block-N capstone importing a
  block-(N-1) capstone works across the package boundary as an ordinary import.

`register-lakefile --sharded` routes each module to its block package's lakefile
(creating the package skeleton — `lakefile.toml` + `require zzl_core` — on first
module in a block) instead of the monolithic array. Backward compat: without
`--sharded`, the existing single-lakefile behavior is untouched and default.

Validation is by generated TEXT (golden-file unit tests), not by building — this
worktree has no `.lake` cache. The generated `lakefile.toml` text per block is
asserted against goldens: correct `name`, `require zzl_core`, `defaultTargets`
containing exactly the block's modules, `[[lean_lib]]` stanza per module.

## Backward compatibility

- Default single-state mode (`campaign_state.json`, monolithic lakefile) is
  UNTOUCHED and remains the default. Journals/sharding are opt-in via new flags
  (`--journal`, `--shard FROM TO`, `--sharded`) and new subcommands
  (`merge-shards`). The live root-owned climb needs no change.
- Journal records are a superset of legacy records; a journal folds losslessly
  into legacy state and vice-versa (legacy `bands` dict → synthetic journal for
  re-sharding if ever needed).

## Failure / resume summary

| Failure | Behavior |
|---|---|
| Crash mid-band | In-flight band not journaled; next run re-emits (idempotent). |
| Crash mid-journal-write | Append is one line; a torn final line is detected on read (JSON parse fail on last line only) and dropped; the band re-emits. |
| Two shards, overlapping ranges, same `n` | Merge succeeds (identical-record). |
| Two shards, same tag, different `n` | Merge ABORTS loudly (AssertionError); no file written. |
| Shared boundary edge | Both shards price it idempotently; stretch caches union losslessly. |
| Live state merge assert fail | Live file untouched (tmp discarded). |
