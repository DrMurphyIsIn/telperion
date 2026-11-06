# Replay record: zeta-zeros-v2

This file is a generated human summary. `telperion island check` never reads it: whether the island is verified is decided from island.toml's [replay] record and the evidence archived under replay/, which is re-parsed on every check. Verified means that evidence is present and internally consistent; it does not prove the run happened (whoever ran the sandbox could write a log by hand). The independent auditor's review of the run is the anchor.

- source: https://github.com/AxiomMath/ZetaZerosV2
- commit: 1d7edeb4e67096f9da1b37cd4b763e8b73886655
- toolchain: leanprover/lean4:v4.34.0-rc2
- licence: Apache-2.0
- challenge: Challenge.Basic (challenge.lean, sha256 dc3cc10e3fb36af0c966a5de73e1ac37ff379825a627807f973920b396fda0b7)
- intended use: positive-proportion results (Lamzouri 67.25%); reference for RH emitter work
- theorems:
  - `ZetaZeros.Challenge.prop_simple_real_lower`
  - `ZetaZeros.Challenge.prop_distinct_lower`
  - `ZetaZeros.Challenge.prop_simple_plus_real_lower`
  - `ZetaZeros.Challenge.prop_simple_or_real_lower`
  - `ZetaZeros.Challenge.thm_simple`
  - `ZetaZeros.Challenge.thm_distinct`
  - `ZetaZeros.Challenge.thm_average`
  - `ZetaZeros.Challenge.thm_simple_or_critical`
  - `ZetaZeros.Challenge.thm_simple_numeric`
  - `ZetaZeros.Challenge.thm_distinct_numeric`
  - `ZetaZeros.Challenge.thm_average_numeric`
  - `ZetaZeros.Challenge.thm_simple_or_critical_numeric`

## 2026-11-05: registered (`telperion island add`)

The library's own Comparator/comparator.json matches ours.

Status: not yet replayed (self-reported).
