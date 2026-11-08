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

## 2026-11-07: PASS (`telperion island record-replay`)

- commit 1d7edeb4e67096f9da1b37cd4b763e8b73886655, challenge_sha256 dc3cc10e3fb36af0c966a5de73e1ac37ff379825a627807f973920b396fda0b7
- nanoda_lib 37cb87b7e6cd6862ef2bd121faa9f4604f59fe96 (NANODA_REV), Comparator v4.34.0-rc2
- Comparator log sha256 be8249fe4d4bd3d2b585686fb55880ec9456a6c968cf64618ceca7ee247e6328, md5 fe7368a46f66415259e9b533d56001ec (20389 bytes); archived as replay/comparator.log.xz
- the log as received: md5 573d6ead9d959ea35a5ee7dadaed242a, sha256 637f7a121d3fc37ca0962f9c483f05d94247647d43ac6f07f8c430f4a4c438ee (21493 bytes); the sandbox's session scratch path was replaced by $SCRATCH (16 occurrences) before it was judged and archived (Ruling 7)
- `ZetaZeros.Challenge.prop_simple_real_lower`: probe PROBE_ONLY, fingerprint b756a5401778089caa5bb3a9e78913eedcb132298f26619eb7b6a47b39040c5e
- `ZetaZeros.Challenge.prop_distinct_lower`: probe PROBE_ONLY, fingerprint 7ea7988ea2ce3c46b56a6d561f1209dafd801309bc32dbe1d39ea08128b75b5a
- `ZetaZeros.Challenge.prop_simple_plus_real_lower`: probe PROBE_ONLY, fingerprint a15cb74cec32caa8bef7d22d485ad76a97be8efd9c8d9257e5c38de82c58ce04
- `ZetaZeros.Challenge.prop_simple_or_real_lower`: probe PROBE_ONLY, fingerprint a06b2f775e0ef12dbb6552df2e299223f4f17dbd5ff387bbd2e1038a163b67b6
- `ZetaZeros.Challenge.thm_simple`: probe PROBE_ONLY, fingerprint a167966cc3f803f73e4bd291ff626ad14826deaa5cc03d64afe3925a9acd12ff
- `ZetaZeros.Challenge.thm_distinct`: probe PROBE_ONLY, fingerprint 1862326fd8248c739d9c3475fea9a240be6f98efa654aee85bd25f030a814326
- `ZetaZeros.Challenge.thm_average`: probe PROBE_ONLY, fingerprint 291fec3d453ff4ec5a2ecab74bb79a50fea781e9e0ecaa3a0dab18e3a1d5c24e
- `ZetaZeros.Challenge.thm_simple_or_critical`: probe PROBE_ONLY, fingerprint 48a6e1d57bfb460823a04b90b121a0869e60d20c298cef130db13fb2090d5f50
- `ZetaZeros.Challenge.thm_simple_numeric`: probe PROBE_ONLY, fingerprint 071b40d09c94e6d41e47787812b5f8f18512e64b1478a51ca16842bfd3d1a70a
- `ZetaZeros.Challenge.thm_distinct_numeric`: probe PROBE_ONLY, fingerprint 23f3418c596baaa8cc27c4954427cb30e9af42452d238f3cdf1ced6e43bb160f
- `ZetaZeros.Challenge.thm_average_numeric`: probe PROBE_ONLY, fingerprint 8691619518a24d6216f560de8c5bc9e49a82b3d3f2f69055f0257ebac395b004
- `ZetaZeros.Challenge.thm_simple_or_critical_numeric`: probe PROBE_ONLY, fingerprint be683c94c3ab67684934066d2033634b06222ead00dcdee0a9f408dc2d13daad
