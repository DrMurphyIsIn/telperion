# Step 0: Pin nanoda and Re-judge Lean-kernel-only Nodes, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Every judge builds nanoda from one pinned commit. Each proved node that was judged with the Lean kernel alone
(`heavy_certificates = true`) carries a recorded, passing, local Comparator run with nanoda ON, on its current artifact.

**Architecture:**
- One pinned revision file and one build script replace the eight unpinned `git clone` sites in the workflows.
- The judge gains a `force_nanoda` switch, so a heavy node's bundle can be rendered with nanoda on.
- The heavy bundles run locally on the 96 GiB Mac. Hosted runners are 16 GB, which is why nanoda was off. The run goes
  through Comparator with a pass-through landrun shim, as in the 2026-09-27 BG precedent.
- A new `[rejudge]` record in the node TOML stores each result, and `mission verify` enforces it for heavy nodes.

**Tech Stack:** Python 3.11+ (telperion, pytest), GitHub Actions YAML, bash, Lean/Lake via leanlock, Comparator +
lean4export at the island's toolchain tag, nanoda_lib (Rust, cargo).

**Spec:** `telperion/docs/superpowers/specs/2026-10-27-telperion-standalone-design.md` (commit 2781e3a6f), section 5.1 and
rollout step 0.

**Spec refinement (owner to confirm at plan review).**
- **What the spec says:** "A judge config with nanoda off fails validation, the heavy judge included."
- **The conflict:** heavy nodes turn nanoda off because their exact `decide +kernel` certificates exhaust a 16 GB hosted
  runner under nanoda (schema.py, `ComparatorRecord.second_kernel`).
- **This plan's rule:**
  - a nanoda-off config is valid ONLY for a node with `heavy_certificates = true`;
  - such a node stays proved ONLY with a passing `[rejudge]` record (local Comparator, nanoda on) on its current artifact
    sha256.
- **The alternative:** paid larger GitHub runners.

## Global Constraints

- Pinned nanoda: `ammkrn/nanoda_lib` commit `37cb87b7e6cd6862ef2bd121faa9f4604f59fe96`, stored ONLY in `telperion/NANODA_REV`.
- nanoda config: `unpermitted_axiom_hard_error: true`. Permitted axioms are exactly `propext`, `Quot.sound` and
  `Classical.choice` (`CLEAN_AXIOMS` in `judge.py`).
- Comparator and lean4export are built at `comparator_tag(island_toolchain)`, never at another tag.
- All Lean and Lake runs go through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`. `OPENBLAS_NUM_THREADS=1`. No `lake update`.
  No lake command on a shared packages directory.
- Run one heavy re-judge at a time (peak memory reached 63.5 GB in the BG precedent).
- Git runs as the user (`sudo -u peterwmurphy git ...`), in worktree `~/arda-telperion-standalone`. Commits carry
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and NO Claude-Session trailer (Arda is public).
- Nothing is pushed and no PR is opened without the owner's word. A FAIL verdict is reported to the owner immediately, in
  the same turn.
- Node set:
  - `MM_weil_positivity_window_two_fifths`, `MM_hodge1_window5493`, `MM_hodge1_rh_reduction`, `MM_hodge1_window45`,
    `MM_weil_positivity_prime_free_window` (mirrormere, island `rvm_bridge`, Lean v4.33.0-rc2);
  - `AND_ladder_h8000_kernel`, `AND_ladder_h11000_kernel` (anduril, island `zeta_reflection`, Lean v4.32.0).

## Review Focus

1. **A pass is only valid for the artifact it judged.** A `[rejudge]` record on an older artifact sha256 must not count once
   the artifact changes. A person expects `verify` to call it stale (Task 3 test `test_rejudge_stale_artifact`).
2. **The verdict comes from the log, not from a flag.** A log that lacks `Nanoda kernel accepts the solution` must record as
   FAIL, even if Comparator exited 0 (Task 3 test `test_rejudge_verdict_requires_nanoda_line`).
3. **An unpinned nanoda clone sneaking back into a workflow.** A new workflow copying the old clone block must fail the
   policy test (Task 1 test `test_no_unpinned_nanoda_clone`).
4. **`force_nanoda` must not leak into the per-PR bundle.** The committed bundle must stay byte-identical (Task 2 test
   `test_committed_bundle_unchanged`).
5. **The `AND_ladder_h11000_kernel` record anomaly.** It is heavy, yet its `[comparator]` block has no `second_kernel`, so it
   reads as "nanoda". A person expects provenance to say "Lean kernel only" until re-judged (Task 3 test
   `test_heavy_node_without_second_kernel_reads_lean_only`).

---

### Task 1: One pinned nanoda for every workflow

**Files:**
- Create: `telperion/NANODA_REV`
- Create: `.github/scripts/build-nanoda.sh`
- Modify:
  - `.github/workflows/liu-dbn-bridge.yml:165-172`;
  - `.github/workflows/missions-comparator-heavy.yml:292-300`;
  - `.github/workflows/oai-qrh-bridge.yml` (the block at line 185);
  - `.github/workflows/missions-comparator.yml` (blocks at lines 390, 609 and 803);
  - `.github/workflows/proof-comparator.yml` (line 201);
  - `.github/workflows/telperion-comparator.yml` (line 143).
- Test: `telperion/tests/test_nanoda_pin.py`

**Interfaces:**
- Produces:
  - `telperion/NANODA_REV`, one line holding a 40-hex sha;
  - `.github/scripts/build-nanoda.sh [DEST]`, which builds `DEST/target/release/nanoda_bin` (DEST defaults to
    `$HOME/nanoda`), appends `COMPARATOR_NANODA=...` to `$GITHUB_ENV` when that variable is set, and prints the built
    revision.

- [ ] **Step 1: Write the failing test**

```python
# telperion/tests/test_nanoda_pin.py
"""nanoda is the second kernel; every judge must build the SAME reviewed commit (spec 5.1)."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = sorted((ROOT / ".github" / "workflows").glob("*.yml"))
REV_FILE = ROOT / "telperion" / "NANODA_REV"
SCRIPT = ROOT / ".github" / "scripts" / "build-nanoda.sh"


def test_rev_file_is_a_full_sha():
    rev = REV_FILE.read_text().strip()
    assert re.fullmatch(r"[0-9a-f]{40}", rev), rev


def test_no_unpinned_nanoda_clone():
    offenders = [w.name for w in WORKFLOWS if re.search(r"git clone[^\n]*nanoda", w.read_text())]
    assert not offenders, f"clone nanoda only via build-nanoda.sh: {offenders}"


def test_every_nanoda_workflow_uses_the_script():
    users = [w for w in WORKFLOWS if "COMPARATOR_NANODA" in w.read_text()]
    assert users, "expected nanoda-using workflows"
    for w in users:
        assert ".github/scripts/build-nanoda.sh" in w.read_text(), w.name


def test_script_checks_out_exact_rev():
    s = SCRIPT.read_text()
    assert "telperion/NANODA_REV" in s
    assert "git fetch --depth 1 origin" in s and "git rev-parse HEAD" in s
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd telperion && python -m pytest tests/test_nanoda_pin.py -v`
Expected: FAIL. `NANODA_REV` is missing, and `test_no_unpinned_nanoda_clone` lists the six workflows.

- [ ] **Step 3: Write the rev file and the script**

`telperion/NANODA_REV`:
```
37cb87b7e6cd6862ef2bd121faa9f4604f59fe96
```

`.github/scripts/build-nanoda.sh`:
```bash
#!/usr/bin/env bash
# Build nanoda_bin at the ONE reviewed commit in telperion/NANODA_REV (spec 5.1).
# Usage: build-nanoda.sh [DEST]   (DEST defaults to $HOME/nanoda)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
REV="$(tr -d '[:space:]' < "$ROOT/telperion/NANODA_REV")"
DEST="${1:-$HOME/nanoda}"
if [ ! -d "$DEST/.git" ]; then
  git init -q "$DEST"
  git -C "$DEST" remote add origin https://github.com/ammkrn/nanoda_lib.git
fi
git -C "$DEST" fetch --depth 1 origin "$REV"
git -C "$DEST" checkout -q --detach FETCH_HEAD
GOT="$(git -C "$DEST" rev-parse HEAD)"
[ "$GOT" = "$REV" ] || { echo "nanoda checkout $GOT != pinned $REV" >&2; exit 1; }
(cd "$DEST" && cargo build --release)
test -x "$DEST/target/release/nanoda_bin"
if [ -n "${GITHUB_ENV:-}" ]; then
  echo "COMPARATOR_NANODA=$DEST/target/release/nanoda_bin" >> "$GITHUB_ENV"
fi
echo "nanoda_bin built at $REV"
```
Run: `chmod +x .github/scripts/build-nanoda.sh`

- [ ] **Step 4: Replace each clone block in the six workflows**

Each block of this shape:
```yaml
        run: |
          set -euo pipefail
          git clone --depth 1 https://github.com/ammkrn/nanoda_lib.git "$HOME/nanoda"
          cd "$HOME/nanoda"
          cargo build --release
          test -x "$HOME/nanoda/target/release/nanoda_bin"
          echo "COMPARATOR_NANODA=$HOME/nanoda/target/release/nanoda_bin" >> "$GITHUB_ENV"
```
becomes:
```yaml
        run: |
          set -euo pipefail
          bash "$GITHUB_WORKSPACE/.github/scripts/build-nanoda.sh" "$HOME/nanoda"
```
Keep each step's `name:` and `if:` lines unchanged. Check the step checks out the repo before this step: `actions/checkout` is
already the first step of every job in these files. Verify with `grep -n "actions/checkout" <file>`.

- [ ] **Step 5: Run the tests and a local build of the script**

Run: `cd telperion && python -m pytest tests/test_nanoda_pin.py -v`. Expected: 4 passed.
Run: `bash .github/scripts/build-nanoda.sh ~/telperion-tools/nanoda-37cb87b7`.
Expected: last line `nanoda_bin built at 37cb87b7e6cd6862ef2bd121faa9f4604f59fe96`.

- [ ] **Step 6: Commit**

```bash
sudo -u peterwmurphy git add telperion/NANODA_REV .github/scripts/build-nanoda.sh .github/workflows/*.yml telperion/tests/test_nanoda_pin.py
sudo -u peterwmurphy git commit -m "ci: build nanoda from one pinned commit (telperion/NANODA_REV)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: `force_nanoda` for rendering heavy bundles with the second kernel on

**Files:**
- Modify: `telperion/src/telperion/missions/judge.py`. This touches `build_bundle` (line 958), its node loop (lines
  1052-1068), the compose parts that hard-code `nanoda=False` (lines 1097-1121), and `main` (lines 1185-1215).
- Test: `telperion/tests/test_judge_heavy.py` (append)

**Interfaces:**
- Consumes: `build_bundle(telperion_root, island, *, enable_nanoda=True, only=None, heavy=False, pending=False) -> Bundle`.
- Produces:
  - `build_bundle(..., force_nanoda: bool = False)`. When it is True, every rendered challenge, compose parts included, has
    `Challenge.nanoda is True` and `config["enable_nanoda"] is True`, regardless of `heavy_certificates`.
  - CLI flag `--force-nanoda`, valid only together with `--heavy`; otherwise the CLI exits 2 with `::error::`.

- [ ] **Step 1: Write the failing tests** (append; reuse this file's existing fixture that builds a heavy node. Read the file's
  top first and use its `TELPERION` root constant and node-slug conventions):

```python
def test_force_nanoda_turns_second_kernel_on_for_heavy_node():
    b = build_bundle(TELPERION, "zeta_reflection", only=["AND_ladder_h8000_kernel"], heavy=True,
                     force_nanoda=True)
    assert b.challenges, "heavy node rendered"
    for c in b.challenges:
        assert c.nanoda is True
        assert c.config["enable_nanoda"] is True


def test_heavy_node_default_stays_lean_kernel_only():
    b = build_bundle(TELPERION, "zeta_reflection", only=["AND_ladder_h8000_kernel"], heavy=True)
    assert all(c.nanoda is False for c in b.challenges)


def test_force_nanoda_requires_heavy(capsys):
    rc = judge_main(["--telperion", str(TELPERION), "--island", "zeta_reflection", "--force-nanoda",
                     "--list"])
    assert rc == 2
    assert "--force-nanoda requires --heavy" in capsys.readouterr().err


def test_committed_bundle_unchanged():
    # force_nanoda defaults off, so the committed per-PR bundle must still check clean.
    b = build_bundle(TELPERION, "rvm_bridge")
    assert check_bundle(b, default_out(TELPERION, "rvm_bridge")) == []
```
Import `main as judge_main`, `check_bundle` and `default_out` from `telperion.missions.judge`, if the file does not already.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cd telperion && python -m pytest tests/test_judge_heavy.py -k "force_nanoda or committed_bundle" -v`
Expected: the force tests FAIL with `TypeError: unexpected keyword argument 'force_nanoda'`, and the CLI test fails with
argparse rc 2 and a different message. `test_committed_bundle_unchanged` should already PASS. It is a guard.

- [ ] **Step 3: Implement**

In `build_bundle`'s signature add `force_nanoda: bool = False`. Replace the per-node line (around line 1062):
```python
        node_nanoda = enable_nanoda and (force_nanoda or not node_heavy)
```
In the two compose-part constructions (around lines 1097 and 1119), replace the literal `nanoda=False` and
`enable_nanoda=False` with:
```python
        part_nanoda = bool(force_nanoda and enable_nanoda)
        ...  nanoda=part_nanoda, ...
        ...  enable_nanoda=part_nanoda, ...
```
Pass `force_nanoda` through to `compose_parts(...)` if those constructions live there. Add a keyword parameter
`force_nanoda: bool = False` to `compose_parts` and forward it.

In `main`, add the flag and the guard right after `parse_args`:
```python
    ap.add_argument("--force-nanoda", action="store_true",
                    help="with --heavy: render nanoda ON even for heavy_certificates nodes "
                         "(local re-judge on a large machine; never committed)")
    ...
    if args.force_nanoda and not args.heavy:
        print("::error::--force-nanoda requires --heavy", file=sys.stderr)
        return 2
```
and pass `force_nanoda=args.force_nanoda` into `build_bundle(...)`.

- [ ] **Step 4: Run the tests**

Run: `cd telperion && python -m pytest tests/test_judge_heavy.py tests/test_missions_judge.py -v`
Expected: all pass, including the 4 new tests.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/missions/judge.py telperion/tests/test_judge_heavy.py
sudo -u peterwmurphy git commit -m "missions/judge: --force-nanoda renders heavy bundles with the second kernel on

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: The `[rejudge]` record, its CLI and its verify rule

**Files:**
- Modify: `telperion/src/telperion/missions/schema.py`:
  - add the `RejudgeRecord` dataclass next to `CIRecord` (line 352);
  - add a `Node.rejudge` field next to `ci_record` (line 405);
  - add `"rejudge"` to `_MODELLED_NODE_KEYS` (line 485);
  - serialise it next to `ci_record` (line 614);
  - parse it next to `ci_record` (line 675).
- Modify: `telperion/src/telperion/missions/provenance.py`:
  - add `rejudge_problem()` next to `required_ci_problem` (line 254);
  - make the heavy branch (lines 355-400) report "Lean kernel only" unless `rejudge_problem` returns "".
- Modify: `telperion/src/telperion/missions/verify.py`: a proved node with `heavy_certificates = true` fails verify when
  `rejudge_problem` is non-empty. This lands in Task 5, NOT here. Here, only add the function and the report wording.
- Modify: `telperion/src/telperion/cli.py`: add a `rejudge-record` subparser next to `ci-record` (line 2513).
- Create: `telperion/src/telperion/missions/rejudge.py`, the log parser.
- Test: `telperion/tests/test_missions_rejudge.py`

**Interfaces:**
- Produces:
  - `RejudgeRecord(date, machine, nanoda_rev, comparator_tag, artifact_sha256, verdict, log_sha256, peak_rss_kb=0, note="")`.
    `verdict` is `"pass"` or `"fail"`; any other value raises `SchemaError`.
  - `parse_comparator_log(text: str) -> str`, returning `"pass"` or `"fail"`.
  - `rejudge_problem(campaign_root: Path, node: Node) -> str`, which returns `""` when the node is not heavy, or when its
    `[rejudge]` is a pass on the current artifact sha256; otherwise a reason.
  - CLI: `telperion mission rejudge-record SLUG --campaign C --log PATH --comparator-tag TAG [--peak-rss-kb N] [--note S]`.
    It reads `NANODA_REV`, derives the verdict from the log, writes `[rejudge]`, and prints `REJUDGE FAIL ... REPORT TO
    OWNER` with exit 1 on fail.

- [ ] **Step 1: Write the failing tests**

```python
# telperion/tests/test_missions_rejudge.py
import dataclasses
from pathlib import Path
import pytest
from telperion.missions.schema import RejudgeRecord, SchemaError
from telperion.missions.rejudge import parse_comparator_log

PASS_LOG = ("Lean default kernel accepts the solution\n"
            "Nanoda kernel accepts the solution\nYour solution is okay!\n")


def test_pass_needs_all_three_lines():
    assert parse_comparator_log(PASS_LOG) == "pass"


def test_rejudge_verdict_requires_nanoda_line():
    log = "Lean default kernel accepts the solution\nYour solution is okay!\n"
    assert parse_comparator_log(log) == "fail"


def test_any_error_line_fails():
    assert parse_comparator_log(PASS_LOG + "error: unpermitted axiom sorryAx\n") == "fail"


def test_bad_verdict_rejected():
    with pytest.raises(SchemaError):
        RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                      artifact_sha256="b" * 64, verdict="maybe", log_sha256="c" * 64)


def test_rejudge_roundtrip(tmp_path):
    from telperion.missions.schema import _node_to_doc, _doc_to_node
    from tests.missions_fixtures import minimal_proved_node          # see Step 1b
    node = minimal_proved_node(tmp_path, heavy=True)
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                        artifact_sha256="b" * 64, verdict="pass", log_sha256="c" * 64, peak_rss_kb=1)
    node2 = _doc_to_node(_node_to_doc(dataclasses.replace(node, rejudge=rec)), tmp_path / "n.toml")
    assert node2.rejudge == rec


def test_rejudge_stale_artifact(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from tests.missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)  # writes a real artifact file
    rec = RejudgeRecord(date="2026-10-27", machine="m", nanoda_rev="a" * 40, comparator_tag="v4.32.0",
                        artifact_sha256="0" * 64, verdict="pass", log_sha256="c" * 64)
    assert "artifact" in rejudge_problem(tmp_path, dataclasses.replace(node, rejudge=rec))


def test_heavy_node_without_second_kernel_reads_lean_only(tmp_path):
    from telperion.missions.provenance import rejudge_problem
    from tests.missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=True)
    assert rejudge_problem(tmp_path, node) != ""
```

- [ ] **Step 1b: Write the shared fixture** (`Proof` is `(artifact, artifact_kind, via, closure_clean=False,
  fidelity_note="")`, with `artifact_kind` in `("lean_module", "frozen_cert")` and `via` in `("direct", "reduction")`.
  `Node` requires `name, title, kind, status, depends_on, statement_module`. `sha256_file` is in
  `telperion.missions.provenance`):

```python
# telperion/tests/missions_fixtures.py
from pathlib import Path
from telperion.missions.schema import Node, Proof


def minimal_proved_node(root: Path, *, heavy: bool) -> Node:
    (root / "Art.lean").write_text("theorem t : True := trivial\n")
    proof = Proof(artifact="Art.lean", artifact_kind="lean_module", via="direct")
    return Node(name="n", title="t", kind="lemma", status="proved", depends_on=(),
                statement_module="S", proof=proof, heavy_certificates=heavy)
```
If `kind="lemma"` is rejected by `Node.__post_init__`, use the first allowed value from the `KINDS` tuple in schema.py.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cd telperion && python -m pytest tests/test_missions_rejudge.py -v`
Expected: FAIL at import (`RejudgeRecord`, `telperion.missions.rejudge` not found).

- [ ] **Step 3: Implement the schema record** (schema.py, after `CIRecord`):

```python
@dataclass(frozen=True)
class RejudgeRecord:
    """A local Comparator run with nanoda ON for a `heavy_certificates` node (spec 5.1, step 0).

    Hosted runners (16 GB) cannot replay heavy certificates under nanoda, so these nodes are
    judged Lean-kernel-only in CI. They stay proved only with a passing re-judge on the CURRENT
    artifact, run on a large machine at the pinned telperion/NANODA_REV.
    """
    date: str
    machine: str
    nanoda_rev: str
    comparator_tag: str
    artifact_sha256: str
    verdict: str
    log_sha256: str
    peak_rss_kb: int = 0
    note: str = ""

    def __post_init__(self):
        for f in ("date", "machine", "nanoda_rev", "comparator_tag", "artifact_sha256", "log_sha256"):
            if not str(getattr(self, f)).strip():
                raise SchemaError(f"rejudge.{f} must be non-empty")
        if self.verdict not in ("pass", "fail"):
            raise SchemaError(f"rejudge.verdict must be 'pass' or 'fail', not {self.verdict!r}")
```
Add `rejudge: Optional[RejudgeRecord] = None` to `Node`, and `"rejudge"` to `_MODELLED_NODE_KEYS`. Serialise in the
doc-builder:
```python
    if node.rejudge is not None:
        r = node.rejudge
        doc["rejudge"] = {k: getattr(r, k) for k in (
            "date", "machine", "nanoda_rev", "comparator_tag", "artifact_sha256", "verdict",
            "log_sha256", "peak_rss_kb")}
        if r.note:
            doc["rejudge"]["note"] = r.note
```
Parse in `_doc_to_node`:
```python
        rejudge = None
        if "rejudge" in doc:
            r = doc["rejudge"]
            rejudge = RejudgeRecord(
                date=r["date"], machine=r["machine"], nanoda_rev=r["nanoda_rev"],
                comparator_tag=r["comparator_tag"], artifact_sha256=r["artifact_sha256"],
                verdict=r["verdict"], log_sha256=r["log_sha256"],
                peak_rss_kb=int(r.get("peak_rss_kb", 0)), note=r.get("note", ""))
```
and pass `rejudge=rejudge` into the `Node(...)` call.

- [ ] **Step 4: Implement the log parser** (`telperion/src/telperion/missions/rejudge.py`):

```python
"""Verdict of a local Comparator re-judge, read from its log (never from a flag)."""
REQUIRED = ("Lean default kernel accepts the solution",
            "Nanoda kernel accepts the solution",
            "Your solution is okay!")


def parse_comparator_log(text: str) -> str:
    lines = text.splitlines()
    if any(l.lstrip().lower().startswith(("error", "uncaught exception")) for l in lines):
        return "fail"
    return "pass" if all(any(req in l for l in lines) for req in REQUIRED) else "fail"
```
Check the exact strings against the BG precedent log (`~/brualdi-goldwasser/formalization/comparator`; the memory note
quotes "Nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!"). Before
relying on the parser, also grep one real CI log of a missions-comparator pass with `gh run view --log`, and adjust REQUIRED
if the wording differs.

- [ ] **Step 5: Implement `rejudge_problem`** (provenance.py, after `required_ci_problem`):

```python
def rejudge_problem(campaign_root: Path, node: Node) -> str:
    """"" unless a heavy node lacks a passing nanoda re-judge on its current artifact."""
    if not node.heavy_certificates:
        return ""
    r = node.rejudge
    if r is None:
        return "heavy_certificates: no local nanoda re-judge recorded (`mission rejudge-record`)"
    if r.verdict != "pass":
        return f"local nanoda re-judge on {r.date} FAILED (nanoda {r.nanoda_rev[:8]})"
    if node.proof is None:
        return "heavy node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"artifact {node.proof.artifact!r} does not exist"
    if sha256_file(art) != r.artifact_sha256:
        return (f"re-judge of {r.date} was on artifact sha256 {r.artifact_sha256[:12]}, "
                "which is no longer the artifact")
    return ""
```
In the heavy branch of the provenance report (lines 355-400), print `Lean kernel + nanoda (local re-judge <date>, nanoda
<rev8>)` when `rejudge_problem(...) == ""`, else keep `Lean kernel only` and append the reason.

- [ ] **Step 6: Implement the CLI** (cli.py, next to `ci-record`). Mirror `ci-record`'s campaign and node loading and
  writing code exactly:

```python
    p = msub.add_parser("rejudge-record",
                        help="record a local Comparator run with nanoda ON for a heavy node")
    p.add_argument("slug")
    p.add_argument("--campaign", required=True)
    p.add_argument("--log", required=True, type=Path)
    p.add_argument("--comparator-tag", required=True)
    p.add_argument("--peak-rss-kb", type=int, default=0)
    p.add_argument("--note", default="")
```
Handler body:
```python
    text = args.log.read_text(errors="replace")
    verdict = parse_comparator_log(text)
    rev = (repo_root / "telperion" / "NANODA_REV").read_text().strip()
    art = campaign_root / node.proof.artifact
    rec = RejudgeRecord(date=_dt.date.today().isoformat(), machine=platform.node(), nanoda_rev=rev,
                        comparator_tag=args.comparator_tag, artifact_sha256=sha256_file(art),
                        verdict=verdict, log_sha256=hashlib.sha256(text.encode()).hexdigest(),
                        peak_rss_kb=args.peak_rss_kb, note=args.note)
    write_node(dataclasses.replace(node, rejudge=rec))
    if verdict != "pass":
        print(f"REJUDGE FAIL {args.slug}: nanoda/Comparator did not accept -- REPORT TO OWNER",
              file=sys.stderr)
        return 1
    print(f"REJUDGE PASS {args.slug} nanoda={rev[:8]} artifact={rec.artifact_sha256[:12]}")
    return 0
```
(Use the module's existing helpers for `repo_root`, `campaign_root`, `node` loading and `write_node`. Their names are in the
`ci-record` handler.)

- [ ] **Step 7: Run the tests**

Run: `cd telperion && python -m pytest tests/test_missions_rejudge.py tests/test_missions_schema.py tests/test_missions_provenance.py -v`
Expected: all pass.

- [ ] **Step 8: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/missions/{schema,provenance,rejudge}.py telperion/src/telperion/cli.py telperion/tests/test_missions_rejudge.py telperion/tests/missions_fixtures.py
sudo -u peterwmurphy git commit -m "missions: [rejudge] record for local nanoda re-judges of heavy nodes

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Run the local re-judges (operational; one node at a time)

**Files:**
- Create: `telperion/missions/judge/REJUDGE_2026-10.md`, the run log (per node: command lines, wall time, peak RSS, log
  sha256, verdict).
- Modify: the seven node TOMLs, via `mission rejudge-record` only.

**Interfaces:**
- Consumes:
  - Task 1 (`build-nanoda.sh`);
  - Task 2 (`--force-nanoda`);
  - Task 3 (`mission rejudge-record`);
  - `comparator_tag(toolchain)` from `judge.py`.

- [ ] **Step 1: Build the tools once.** These are outside any repository, and no shared `.lake` is involved.

```bash
mkdir -p ~/telperion-tools
bash .github/scripts/build-nanoda.sh ~/telperion-tools/nanoda-37cb87b7
for TAG in $(cd telperion && python -c "from telperion.missions.judge import comparator_tag; print(comparator_tag('leanprover/lean4:v4.32.0'), comparator_tag('leanprover/lean4:v4.33.0-rc2'))"); do
  git clone -q --depth 1 --branch "$TAG" https://github.com/leanprover/comparator.git ~/telperion-tools/comparator-$TAG
  (cd ~/telperion-tools/comparator-$TAG && ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh lake build lean4export comparator)
done
mkdir -p ~/telperion-tools/bin && cat > ~/telperion-tools/bin/landrun <<'SHIM'
#!/usr/bin/env bash
# pass-through: landrun is Linux-only; the macOS run is UNSANDBOXED (recorded in each note)
args=("$@"); i=0
while [ $i -lt ${#args[@]} ]; do case "${args[$i]}" in --) i=$((i+1)); break;; --*=*) i=$((i+1));; -*) i=$((i+1));; *) break;; esac; done
exec "${args[@]:$i}"
SHIM
chmod +x ~/telperion-tools/bin/landrun
```
Expected: both `comparator` and `lean4export` binaries exist under each `comparator-$TAG/.lake`. The shim's argument
skipping must match the heavy workflow's shim (`missions-comparator-heavy.yml`, the lines before 279). Diff them, and copy
the workflow's shim verbatim if they differ.

- [ ] **Step 2: Negative controls first** (both must FAIL; record them in `REJUDGE_2026-10.md`):
  - (a) Render `AND_ladder_h8000_kernel` with `--heavy --force-nanoda` to `/tmp/rj-neg`. Edit one numeral in its challenge
    statement, then run Comparator. Expected: FAIL at statement identity.
  - (b) Run `nanoda_bin` on that bundle's lean4export output with a config whose `permitted_axioms` is `[]` and
    `unpermitted_axiom_hard_error: true`. Expected: hard error on `propext`.
  - If either one passes, STOP and report to the owner.

- [ ] **Step 3: Check the h11000 record anomaly.** Run `grep -n -A12 '^\[comparator\]'
  telperion/missions/anduril/nodes/AND_ladder_h11000_kernel.toml`. If `second_kernel` is absent but the node is heavy, write
  that into `REJUDGE_2026-10.md` as a data finding. The re-judge supersedes it. Do not hand-edit the record.

- [ ] **Step 4: For each node, smallest first** (order by last CI peak RSS from `gh run view --log` of its heavy run, or by
  artifact size if unavailable):

```bash
NODE=AND_ladder_h8000_kernel; ISLAND=zeta_reflection; CAMPAIGN=anduril
TAG=$(cd telperion && python -c "from telperion.missions.judge import comparator_tag, island_toolchain, island_dir; from pathlib import Path; print(comparator_tag(island_toolchain(island_dir(Path('.'), '$ISLAND') / 'lean')))")
OUT=~/telperion-tools/rejudge/$NODE; rm -rf "$OUT"
(cd telperion && python -m telperion.missions.judge --telperion . --island $ISLAND --only $NODE --heavy --force-nanoda --out "$OUT")
(cd telperion && python -m telperion.missions.judge --telperion . --island $ISLAND --only $NODE --heavy --build-plan) > "$OUT/build-plan.json"
# build exactly what build-plan.json lists, as the heavy workflow does, under leanlock:
(cd "$OUT" && ARDA_LEAN_SLOTS=1 OPENBLAS_NUM_THREADS=1 ~/hodge-engine/leanlock.sh lake build)
CFG=$(cd telperion && python -m telperion.missions.judge --telperion . --island $ISLAND --only $NODE --heavy --force-nanoda --configs | cut -f2)
(cd "$OUT" && ulimit -s 65520; PATH=~/telperion-tools/bin:~/telperion-tools/comparator-$TAG/.lake/build/bin:$PATH \
  COMPARATOR_LANDRUN=~/telperion-tools/bin/landrun \
  COMPARATOR_LEAN4EXPORT=$(find ~/telperion-tools/comparator-$TAG/.lake -type f -name lean4export -path '*/bin/*' | head -1) \
  COMPARATOR_NANODA=~/telperion-tools/nanoda-37cb87b7/target/release/nanoda_bin \
  /usr/bin/time -l env ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh lake env comparator "$CFG") > "$OUT/comparator.log" 2>&1
PEAK=$(grep "maximum resident set size" "$OUT/comparator.log" | awk '{print int($1/1024)}')
(cd telperion && python -m telperion.cli mission rejudge-record $NODE --campaign $CAMPAIGN --log "$OUT/comparator.log" --comparator-tag $TAG --peak-rss-kb $PEAK --note "local macOS, landrun shim (unsandboxed)")
```
Expected: `REJUDGE PASS ...`. On `REJUDGE FAIL`, stop the queue and report to the owner in the same turn, with the log tail.
- `/usr/bin/time -l` on macOS reports bytes, hence the `/1024`.
- If the heavy workflow builds in segments (`"mode": "segments"` in `build-plan.json`), the node is compositional. Run
  Comparator once per part line printed by `--configs`; the node passes only if every part passes. Record the log of each part
  under `$OUT/part-<n>.log`, and give `rejudge-record` a concatenated log.

- [ ] **Step 5: Commit the records and the run log** (after all seven, or after each, at the executor's choice):

```bash
sudo -u peterwmurphy git add telperion/missions/*/nodes/*.toml telperion/missions/judge/REJUDGE_2026-10.md
sudo -u peterwmurphy git commit -m "missions: local nanoda re-judge of the 7 heavy_certificates nodes

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 5: Enforce it: verify rule + judge README

**Files:**
- Modify: `telperion/src/telperion/missions/verify.py`. Enforce it in both places that already enforce `required_ci_problem`:
  `grant_status` (line 586, raises `GateError`) and `verify_campaign` (line 816, appends to `errors` for proved nodes).
- Modify: `telperion/missions/judge/README.md`. In the section on `heavy_certificates`, state the rule and point to
  `REJUDGE_2026-10.md`.
- Test: `telperion/tests/test_missions_rejudge.py` (append)

**Interfaces:**
- Consumes: `rejudge_problem` (Task 3).
- Produces: `mission verify` exits non-zero for a proved heavy node without a passing current re-judge.

- [ ] **Step 1: Write the failing test**

```python
TELPERION_ROOT = Path(__file__).resolve().parents[1]


def _verify_copy_without_rejudge(tmp_path, campaign, slug):
    """Copy a real campaign, drop one node's [rejudge] record, run verify_campaign on the copy."""
    import shutil
    from telperion.missions.schema import load_node, save_node
    from telperion.missions.verify import verify_campaign
    dst = tmp_path / campaign
    shutil.copytree(TELPERION_ROOT / "missions" / campaign, dst)
    p = dst / "nodes" / f"{slug}.toml"
    save_node(dataclasses.replace(load_node(p), rejudge=None), p)
    return verify_campaign(dst).errors


def test_verify_rejects_proved_heavy_node_without_rejudge(tmp_path):
    errors = _verify_copy_without_rejudge(tmp_path, "anduril", "AND_ladder_h8000_kernel")
    assert any("AND_ladder_h8000_kernel" in e and "re-judge" in e for e in errors)
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd telperion && python -m pytest tests/test_missions_rejudge.py::test_verify_rejects_proved_heavy_node_without_rejudge -v`
Expected: FAIL (no re-judge error reported). If the copied campaign fails to verify for an unrelated reason (for example,
artifacts outside `missions/anduril` resolved relative to the repo root), copy what `verify_campaign` needs, following how
`tests/test_missions_provenance.py` builds its campaign fixtures, and keep the assertion unchanged.

- [ ] **Step 3: Implement.** Import `rejudge_problem` next to `required_ci_problem` (line 40). In `grant_status`, after the
  `ci` check:

```python
    rj = rejudge_problem(campaign.root, node)
    if rj:
        raise GateError(f"Node {slug!r}: {rj}")
```
In `verify_campaign`, after the `ci` check:
```python
        rj = rejudge_problem(root, node)
        if rj and node.status == "proved":
            errors.append(f"Node {sl!r}: status is 'proved' but {rj} (re-judge)")
```

- [ ] **Step 4: Run the whole missions suite against the REAL registry**

Run:
```bash
cd telperion && python -m pytest tests/ -q -k "missions or judge or rejudge or nanoda"
python -m telperion.cli mission verify
```
Expected: tests pass, and `mission verify` is clean. Task 4 recorded passes on all seven nodes, so nothing should fail. Any
failure here means a node is unrecorded or stale; report it to the owner.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/missions/verify.py telperion/missions/judge/README.md telperion/tests/test_missions_rejudge.py
sudo -u peterwmurphy git commit -m "missions/verify: heavy nodes stay proved only with a passing nanoda re-judge

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

- [ ] **Step 6: Report to the owner**, with no push. Include the per-node verdict table from `REJUDGE_2026-10.md`, the
  negative-control results, the h11000 finding, and the branch name. Ask whether to push and open the PR.
