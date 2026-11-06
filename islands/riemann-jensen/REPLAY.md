# Replay record: riemann-jensen

This file is a generated human summary. `telperion island check` never reads it: whether the island is verified is decided from island.toml's [replay] record and the evidence archived under replay/, which is re-parsed on every check. Verified means that evidence is present and internally consistent; it does not prove the run happened (whoever ran the sandbox could write a log by hand). The independent auditor's review of the run is the anchor.

- source: https://github.com/AxiomMath/RiemannJensen
- commit: c1e023fa3ae7161219dde3dcb73f0c28ff972be2
- toolchain: leanprover/lean4:v4.35.0
- licence: Apache-2.0
- challenge: Challenge.Basic (challenge.lean, sha256 eeae0da96ab3d5784522a5745dc46353b1a804c3ea32972be4040cd4cd73354c)
- intended use: RH Track 1 (Jensen-Polya hyperbolicity); upstream for Arda's rh_jensen lab
- theorems:
  - `RiemannJensen.Challenge.exists_isDedekindZetaContinuation`
  - `RiemannJensen.Challenge.isDedekindZetaContinuation_unique`
  - `RiemannJensen.Challenge.dedekind_thm_main`
  - `RiemannJensen.Challenge.riemannJensen_main`

## 2026-11-05: registered (`telperion island add`)

The library's own Comparator/comparator.json matches ours.

Status: not yet replayed (self-reported).
