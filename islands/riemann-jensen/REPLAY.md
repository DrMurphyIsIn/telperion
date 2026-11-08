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

## 2026-11-06: PASS (`telperion island record-replay`)

- commit c1e023fa3ae7161219dde3dcb73f0c28ff972be2, challenge_sha256 eeae0da96ab3d5784522a5745dc46353b1a804c3ea32972be4040cd4cd73354c
- nanoda_lib 37cb87b7e6cd6862ef2bd121faa9f4604f59fe96 (NANODA_REV), Comparator v4.35.0
- Comparator log sha256 d60dcee003774797537d0eb93777aed0b013075ed9fe7ab202614e241e3b3ba3, md5 76562f259882a09d7f939b24590e0af8 (15565 bytes); archived as replay/comparator.log.xz
- the log as received: md5 76bc5e06fefaff12634a5bd7bcc39c87, sha256 883713c39a06280f03535384c3ba807fb4d2f3f641b6e4bceb023570be70382b (16669 bytes); the sandbox's session scratch path was replaced by $SCRATCH (16 occurrences) before it was judged and archived (Ruling 7)
- `RiemannJensen.Challenge.exists_isDedekindZetaContinuation`: probe PROBE_ONLY, fingerprint 41c301213afbfd742494a3193790cd1a2597ba3adf09de4d1907baeeafeb7099
- `RiemannJensen.Challenge.isDedekindZetaContinuation_unique`: probe PROBE_ONLY, fingerprint 76fe47f998a4d373c7d1681ae4fc64975719cb8e1ac81bcf3e205de687159617
- `RiemannJensen.Challenge.dedekind_thm_main`: probe PROBE_ONLY, fingerprint b467aa4c7242e399efe99bd81e960448b2bd0754f8c14775ce879406f1fb7918
- `RiemannJensen.Challenge.riemannJensen_main`: probe PROBE_ONLY, fingerprint 92bd633431229d70a3e6467332e862e5c2f8b6360539a19791e5221fd0e235af
