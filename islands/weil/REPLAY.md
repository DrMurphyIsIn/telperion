# Replay record: weil

This file is a generated human summary. `telperion island check` never reads it: whether the island is verified is decided from island.toml's [replay] record and the evidence archived under replay/, which is re-parsed on every check. Verified means that evidence is present and internally consistent; it does not prove the run happened (whoever ran the sandbox could write a log by hand). The independent auditor's review of the run is the anchor.

- source: https://github.com/AxiomMath/Weil
- commit: 27cdb2049be62ee2911429b47f54774078450e32
- toolchain: leanprover/lean4:v4.34.0-rc2
- licence: Apache-2.0
- challenge: Weil.TelperionChallenge, a Telperion lead-authored statement-only OVERLAY (challenge.lean, overlay_sha256 012753bfbab54efb5e7aa50ca90e826549feb07089fd093eb394a5bc83866b33); at replay it is placed at `Weil/TelperionChallenge.lean` in a fresh copy of the pin, the one file added to it
- overlay imports (upstream definition modules, besides Mathlib): `Weil.Definitions`
- solution: Weil.AlgebraicGeometry.EtaleCohomology.Trace.WeilRiemannHypothesisForm (upstream)
- intended use: point-count statements of the Weil conjectures (classical RH form for the zeta series, rationality); reference for function-field RH work
- theorems (each with the upstream line its statement was copied from):
  - `Weil.exists_zetaSeries_mul_prod_even_eq_prod_odd`: `Weil/AlgebraicGeometry/EtaleCohomology/Trace/WeilRiemannHypothesisForm.lean:206`
  - `AlgebraicGeometry.exists_mul_zetaSeries_eq`: `Weil/AlgebraicGeometry/EtaleCohomology/Trace/ZetaRationality.lean:170`

## 2026-11-06: registered (`telperion island add --overlay`)

The library ships no Comparator config or challenge module; the overlay is the challenge and our comparator.json is the config. The overlay is a TRUSTED statement layer: bb checks it against the library, statement by statement, and Comparator checks at replay that each of its statements has exactly the type of the solution's theorem of the same name.

Status: not yet replayed (self-reported).
