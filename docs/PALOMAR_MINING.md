# Palomar certificate mining — distilling Palomar into Telperion

`src/telperion/palomar_mine.py` is the systematic distiller: it turns the Palomar
registry (Lean-verified, comparator-checked formalizations) into ranked *candidate
Telperion emitter shapes* for this project's two research fronts — Riemann (`rh`)
and Brualdi–Goldwasser (`bg`) — plus a proof-complexity front (`pvsnp`).

## Design

Split into a PURE offline-testable core and a thin network layer (same
untrusted-input / testable-core discipline as the emitters):

- **`classify_entry(entry, topics=None)`** — matches an entry's title/abstract/MSC
  against the topic lexicons (`TOPIC_KEYWORDS`) and the shape rules (`SHAPE_RULES`),
  returning a `MiningCandidate` (topics, shapes, trust-boundary flag, score) or `None`.
  Each shape carries either an EXISTING Telperion `kind` (maps onto proven tooling) or
  `None` (a candidate NEW shape to design).
- **`mine(entries, topics, min_score)`** — classify + rank (score desc).
- **`mining_report(candidates)`** — markdown, split into "new candidate shapes" vs
  "map onto existing emitters".
- **`fetch_registry(url)`** — thin urllib GET of `recent.json`.
- **`poll(state_path, topics, fetch=…)`** — the recurring subroutine: fetch, diff
  against the seen-state file, classify only NEW entries, persist the enlarged seen-set,
  return the new candidates. `fetch` is injectable so the loop is unit-tested offline.

Nothing here trusts Palomar: a candidate is a lead for a human/agent to build and
CI-verify, never an emitter itself.

## Shape rules (math vocabulary → emitter family)

| matched vocabulary | family | Telperion `kind` |
|---|---|---|
| Li-Keiper / Li's criterion | Li positivity ladder | NEW |
| explicit formula / pair correlation / von Mangoldt / Weil | explicit-formula / Weil positivity | NEW |
| Jensen / Laguerre / Turán / real-root / log-concave / Newton | real-rootedness / hyperbolicity | `interlacing` |
| SOS / semidefinite / PSD / Gram / low-rank | SOS / PSD positivity | `psd_form` |
| eigenvalue / spectral / Hermitian / inertia / signature | Hermitian eigenvalue / inertia | `rank_trace_scalar` |
| argument principle / winding / residue / zero-count / Turing | argument-principle / winding | `argument_principle` |
| permanent / matching / immanant / spanning tree / cavity | permanent / matching (BG cavity) | NEW |
| Nullstellensatz / Handelman / Putinar / Chvátal–Gomory | Positivstellensatz / integer rounding | `handelman` |
| interval arithmetic / enclosure / exact-arith / finite / decide | finite-decide / enclosure | `finite_decide` |
| spectral theorem / self-adjoint / PVM / Stone / Cayley | Hilbert–Pólya infrastructure | NEW |

## CLI

```
telperion palomar-mine --topic rh                    # live: fetch recent.json + report (RH)
telperion palomar-mine --topic bg --min-score 3      # BG, thin candidates pruned
telperion palomar-mine --source feed --topic rh,bg   # lighter-weight: the RSS feed.xml source
telperion palomar-mine --file recent.json --json     # offline JSON (a saved registry)
telperion palomar-mine --poll --topic rh,bg --state palomar-seen.json
```

## Sources & update cadence

Palomar exposes two PULL sources — there is no push/webhook to subscribe a callback:
- `recent.json` (default, `--source recent`): structured, carries MSC — best signal.
- `feed.xml` (`--source feed`): RSS; title + description only (no MSC), lighter. Both
  share the same entry-id space, so a shared `--poll --state` file dedups across sources.
- A Palomar Lean **Zulip** channel (`leanprover.zulipchat.com`, stream `Palomar`) is the
  human announce/discussion channel; a Zulip API/bot poll could be added as a third source.

`--poll` is the recurring form: on each run it surfaces only entries new since the last run.
Registry volume is only ~4–6 total submissions/day and RH/BG-relevant ones are sparse, so a
**weekly** scheduled poll is sufficient (the seen-state dedups a week's backlog). Schedule it
as a cloud routine (`/schedule`) or a local cron.

## Current leads

See `PALOMAR_RH_SOURCES.md` and `PALOMAR_BG_SOURCES.md` for the curated, roadmap-tagged
lead lists (the standout: Track-2 Li's criterion is already formalized upstream —
reuse it; and Davenport–Heilbronn is the negative control for the RH certificate families).
