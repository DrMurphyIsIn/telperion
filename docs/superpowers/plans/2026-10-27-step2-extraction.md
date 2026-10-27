# Step 2: Extract Telperion into a Standalone Repository (Local), Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `~/telperion-repo`, a local git repository whose history is Arda's history filtered to the engine. It has a
CI workflow, and its engine test suite gives exactly the outcomes recorded in a lab-removed baseline. Nothing is pushed:
creating the GitHub repository is an owner gate after this plan.

**Architecture:**
- One reviewable rules file (`docs/extraction/extraction_rules.toml`) plus the step 1 manifest generate the exact path list
  that `git filter-repo` keeps.
- The baseline comes from running the engine tests twice. The first run is in Arda as it is. The second is a "lab-removed
  dry run": a scratch tree containing only the kept paths.
- Every test whose outcome differs between the two runs is resolved before extraction, either by shipping its data or by
  reclassifying the test as lab.
- The filtered repository must reproduce the dry-run outcomes exactly.

**Tech Stack:**
- `git filter-repo` (a40bce548d2c, at /usr/local/bin);
- `gitleaks` (installed via Homebrew in Task 3);
- Python 3.14 with pytest and the CI dependency set;
- GitHub Actions YAML.

**Spec:** `telperion/docs/superpowers/specs/2026-10-27-telperion-standalone-design.md` (2781e3a6f), sections 2, 3, 8
(step 2), 9 and 10.

**Owner decisions folded in (2026-10-27):**
- Canonical examples are exactly `rational_sos, sos_refutation, handelman, putinar, real_nullstellensatz, sturm_positive,
  polya_zeros, wz, primality, padic_valuation`.
- `missions/judge_tools` stays with the engine. `missions/judge/` ships only its README. Its island bundles and the step 0
  re-judge queue are Arda data. Lead's finding, 2026-10-27, recorded for the owner's gate review.
- The entry-point plugin seam is dropped (step 1).

## Global Constraints

- Base: branch `telperion/step1-lab-boundary` at `e0b40d933` or later, worktree `~/arda-telperion-step1`. Do NOT use
  `~/arda-telperion-standalone`, where the step 0 re-judge queue runs.
- PRECONDITION: step 0 is complete. Its Task 4 records and Task 5 verify gate are on `docs/telperion-standalone-spec`, and
  that branch has been merged into `telperion/step1-lab-boundary`, so the extracted history carries the `[rejudge]` work.
  Task 1 Step 0 checks this.
- New repository path: `~/telperion-repo`. Scratch area: `~/telperion-tools/extract/`. Nothing is created on GitHub, nothing
  is pushed, no remote is added.
- Kept history: commits touching kept paths only. Each kept path is renamed `telperion/<x>` -> `<x>`. Commit messages drop
  every line beginning `Claude-Session:`. `Co-Authored-By` lines are kept.
- Labs (`LABS` in `telperion/src/telperion/boundary.py`), `lab_tests`, `test_support["lab"]`, and `mission_data["moves"]`
  are excluded, along with `research/`. Of the examples, only the 10 canonical ones and those required by kept tests are
  included (Task 2 settles the second set).
- Licence split, unchanged:
  - engine (`src/`, CLI, MCP, tooling) is BSL-1.1, per `pyproject.toml` and `LICENSE`, with `CLA.md`;
  - examples, docs and emitted certificates are Apache-2.0 / CC-BY-4.0, with a `LICENSING.md` modelled on
    `~/tenth-discriminant/LICENSING.md`.
- Tests run with a venv that matches CI: `~/telperion-tools/venv314` plus `cvxpy "scs<3.3" pyyaml` (Task 2 installs these).
  Lean-env tests skip unless an env is built, and none is built in the scratch trees.
- Git in Arda worktrees runs as `sudo -u peterwmurphy git`. `~/telperion-repo` is owned by peterwmurphy, so run git there as
  the same user. Commits carry `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and NO Claude-Session trailer.
- README style: verbose and conversational. The README tells the reader the story (owner preference).

## Review Focus

1. **A kept file imports a module that filtering dropped.** The dry run catches it only if a test imports it. Task 2 also
   imports every kept `src/telperion/**.py` module in the dry-run tree (`test_every_kept_module_imports`).
2. **History filtering keeps a secret that was later deleted from HEAD.** Task 3 scans the whole filtered HISTORY, not just
   the tree.
3. **A path renamed into the repo root collides with a new scaffold file**, such as `README.md` or `LICENSE`. Task 4 edits the
   existing files instead of overwriting them blindly, and its diff shows each change.
4. **`Claude-Session:` hides in the middle of a message or uses a different case.** Task 3's callback and its check both
   match `(?im)^\s*claude-session:`.
5. **Test outcomes drift between the dry run and the new repo** because of a path that exists only in the scratch tree. Task 5
   compares per-test outcomes, not totals.

---

### Task 1: Extraction rules and the generated path list

**Files:**
- Create: `telperion/docs/extraction/extraction_rules.toml`
- Create: `telperion/scripts/extraction_paths.py`
- Modify: `telperion/scripts/lab_manifest.py` (`missions/judge_tools` becomes `stays_in_engine`)
- Test: `telperion/tests/test_extraction_paths.py`

**Interfaces:**
- Consumes: `docs/extraction/LAB_MANIFEST.json` (step 1), with the keys `labs`, `lab_tests`, `engine_tests`, `test_support`,
  `mission_data`, `top_level_dirs`, `limitations`.
- Produces:
  - `extraction_paths.py --write` writes `docs/extraction/EXTRACTION_PATHS.txt`: one `telperion/<path>` per line, sorted. Each
    line is a file path or a directory prefix ending in `/`. This is the format `git filter-repo --paths-from-file` reads.
  - `extraction_paths.py --check` exits 1 when the file is stale.
  - `kept_paths(root) -> list[str]` and `kept_files(root) -> list[str]`, the latter expanding directories over `git ls-files`.

- [ ] **Step 0: Precondition check.** Run `git -C ~/arda-telperion-step1 merge-base --is-ancestor $(git -C ~/arda-telperion-standalone rev-parse docs/telperion-standalone-spec) HEAD && echo merged`.
  If the output is not `merged`, STOP and report BLOCKED: the step 0 branch has not been merged in yet.

- [ ] **Step 1: Write the rules file** `telperion/docs/extraction/extraction_rules.toml`:

```toml
# What the standalone Telperion repo keeps (spec section 3). Owner-reviewed at the step 2 gate.
# Everything not listed is NOT kept. Paths are relative to telperion/.

[keep]
dirs = ["src/telperion/", "tests/", "missions/judge_tools/"]
# missions/judge/ holds Arda's committed judge BUNDLES for RH/BG islands (rvm_bridge, li_positivity, zeta_reflection,
# dbn, bg, quasicrystal, liu_dbn_bridge, oai_qrh_bridge) and step 0's Arda-specific rejudge_queue.sh / REJUDGE log:
# lab data. Only its README (the judge's how-to) ships.
files = ["pyproject.toml", "README.md", "LICENSE", "CLA.md", "CONTRIBUTING.md", "CHANGELOG.md", "NANODA_REV",
         "missions/judge/README.md",
         "scripts/guard_anchors.py", "scripts/judge_materialize.sh"]
# docs/ is ~380 files, almost all RH/BG mission notes: ENGINE docs are an explicit allowlist (owner reviews at the gate).
docs = ["docs/ARCHITECTURE.md", "docs/ANALYTIC_CERT_STRUCTURES.md", "docs/COMPARATOR.md", "docs/GETTING_STARTED.md",
        "docs/HONESTY_PATTERNS.md", "docs/METHODOLOGY.md", "docs/MISSIONS_HOWTO.md", "docs/TACTIC_CONTRACT.md",
        "docs/TRUSTED_FLOOR.md", "docs/VERIFY_AND_GAPFILL.md", "docs/SECOND_PASS_EMITTER_CATALOG.md",
        "docs/NEW_EMITTERS_SUMMARY.md", "docs/AUDIT_INDEPENDENCE_2026-09-23.md", "docs/RUNNER_SHARD_DESIGN.md",
        "docs/PALOMAR_MINING.md",
        "docs/superpowers/specs/2026-08-18-telperion-evolve-design.md",
        "docs/superpowers/specs/2026-08-20-telperion-self-application-program-design.md",
        "docs/superpowers/specs/2026-09-05-analytic-cert-structures-design.md",
        "docs/superpowers/specs/2026-10-27-telperion-standalone-design.md",
        "docs/superpowers/plans/2026-08-18-telperion-evolve.md",
        "docs/superpowers/plans/2026-09-05-analytic-cert-structures.md",
        "docs/superpowers/plans/2026-10-27-step0-nanoda-pin-rejudge.md",
        "docs/superpowers/plans/2026-10-27-step1-lab-boundary.md",
        "docs/superpowers/plans/2026-10-27-step2-extraction.md",
        "docs/superpowers/plans/2026-10-27-step3-kernel-policy.md"]
# Files kept because a kept test reads them (Task 2 fills; each entry names the test in [resolutions]).
extra_files = []
canonical_examples = ["rational_sos", "sos_refutation", "handelman", "putinar", "real_nullstellensatz",
                      "sturm_positive", "polya_zeros", "wz", "primality", "padic_valuation"]
# Examples that kept tests read as data. Task 2 fills this from the dry run; each entry says which test needs it.
test_data_examples = []

[drop]
# Removed from inside kept dirs. Labs, lab tests and lab test-support come from LAB_MANIFEST.json automatically.
dirs = []
# Arda-side extraction tooling: it describes Arda's labs, so it stays in Arda and is not shipped.
files = ["tests/test_lab_manifest.py", "tests/test_extraction_paths.py", "tests/test_extraction_baseline.py"]
```

- [ ] **Step 2: Write the failing tests**

```python
# telperion/tests/test_extraction_paths.py
import subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import extraction_paths as ep  # noqa: E402

CANON = {"rational_sos", "sos_refutation", "handelman", "putinar", "real_nullstellensatz",
         "sturm_positive", "polya_zeros", "wz", "primality", "padic_valuation"}


def _kept():
    return set(ep.kept_files(ROOT))


def test_no_lab_source_kept():
    kept = _kept()
    for lab in ("bg/", "rh_jensen/"):
        assert not any(p.startswith(f"telperion/src/telperion/{lab}") for p in kept)
    for mod in ("bg_upper_bound", "bg_bulk_discharge", "li_coeff", "weil_form_eval"):
        assert f"telperion/src/telperion/{mod}.py" not in kept


def test_no_lab_test_or_support_kept():
    import json
    m = json.loads((ROOT / "docs/extraction/LAB_MANIFEST.json").read_text())
    kept = _kept()
    for t in m["lab_tests"] + m["test_support"]["lab"]:
        assert f"telperion/{t}" not in kept, t


def test_moving_missions_dropped_and_judge_kept():
    kept = _kept()
    for c in ("rh", "mirrormere", "anduril", "bg"):
        assert not any(p.startswith(f"telperion/missions/{c}/") for p in kept)
    assert "telperion/missions/judge/README.md" in kept
    assert any(p.startswith("telperion/missions/judge_tools/") for p in kept)
    # committed island bundles and the Arda-specific re-judge queue are lab data
    assert not any(p.startswith("telperion/missions/judge/") and p != "telperion/missions/judge/README.md"
                   for p in kept)


def test_canonical_examples_kept_and_others_not():
    kept = _kept()
    ex = {p.split("/")[2] for p in kept if p.startswith("telperion/examples/")}
    assert CANON <= ex
    assert not ({"zeta_zero_localization", "rvm_bridge", "zeta_reflection", "li_positivity"} & ex)


def test_research_and_mission_docs_dropped():
    kept = _kept()
    assert not any(p.startswith(("telperion/research/", "telperion/docs/probes/",
                                 "telperion/docs/research/")) for p in kept)
    assert "telperion/docs/ARCHITECTURE.md" in kept
    assert not any("AUDIT_TESTIMONY" in p or "ANDURIL" in p for p in kept)


def test_arda_side_tools_not_shipped():
    kept = _kept()
    for p in ("scripts/lab_manifest.py", "scripts/extraction_paths.py", "scripts/extraction_baseline.py",
              "scripts/extract_repo.sh", "tests/test_lab_manifest.py", "tests/test_extraction_paths.py",
              "tests/test_extraction_baseline.py", "docs/extraction/LAB_MANIFEST.json"):
        assert f"telperion/{p}" not in kept, p


def test_paths_file_is_current():
    r = subprocess.run([sys.executable, str(ROOT / "scripts/extraction_paths.py"), "--check"],
                       cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
```

- [ ] **Step 3: Run them to verify they fail**

Run: `cd ~/arda-telperion-step1/telperion && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_extraction_paths.py -q -p no:cacheprovider`
Expected: FAIL with `ModuleNotFoundError: extraction_paths`.

- [ ] **Step 4: Implement `telperion/scripts/extraction_paths.py`**

```python
#!/usr/bin/env python3
"""Generate docs/extraction/EXTRACTION_PATHS.txt for `git filter-repo --paths-from-file` (step 2).

Kept = [keep] rules  minus  labs / lab tests / lab test-support (LAB_MANIFEST.json)  minus  [drop] rules.
Directories are expanded to individual tracked files whenever a kept dir contains a dropped file, so
filter-repo never keeps a lab file through a parent-directory rule.
"""
from __future__ import annotations

import argparse, json, subprocess, sys, tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RULES = Path("docs/extraction/extraction_rules.toml")
OUT = Path("docs/extraction/EXTRACTION_PATHS.txt")


def _tracked(root: Path) -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout
    return sorted(p for p in out.decode().split("\0") if p)


def _excluded(root: Path, rules: dict) -> set[str]:
    m = json.loads((root / "docs/extraction/LAB_MANIFEST.json").read_text())
    ex: set[str] = set()
    for files in m["labs"].values():
        ex.update(files)
    ex.update(m["lab_tests"])
    ex.update(m["test_support"]["lab"])
    return ex


def _drop_prefixes(root: Path, rules: dict) -> tuple[str, ...]:
    m = json.loads((root / "docs/extraction/LAB_MANIFEST.json").read_text())
    # lab sources are excluded file-by-file via _excluded(); this adds rule dirs + moving campaigns
    return tuple(list(rules["drop"]["dirs"]) + [d.rstrip("/") + "/" for d in m["mission_data"]["moves"]])


def kept_files(root: Path) -> list[str]:
    rules = tomllib.loads((root / RULES).read_text())
    keep_dirs = tuple(rules["keep"]["dirs"])
    keep_files = set(rules["keep"]["files"]) | set(rules["keep"]["docs"]) | set(rules["keep"]["extra_files"])
    examples = set(rules["keep"]["canonical_examples"]) | set(rules["keep"]["test_data_examples"])
    excluded, drop = _excluded(root, rules), _drop_prefixes(root, rules)
    kept = []
    for p in _tracked(root):
        is_ex = p.startswith("examples/") and p.split("/")[1] in examples
        if not (p in keep_files or p.startswith(keep_dirs) or is_ex):
            continue
        if p in excluded or p.startswith(drop) or p in rules["drop"]["files"]:
            continue
        kept.append(f"telperion/{p}")
    return kept


def kept_paths(root: Path) -> list[str]:
    """Exact file list (no dir prefixes): simplest correct input for --paths-from-file."""
    return kept_files(root)


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    a = ap.parse_args()
    text = "\n".join(kept_paths(ROOT)) + "\n"
    if a.write:
        (ROOT / OUT).write_text(text)
        print(f"wrote {OUT}: {text.count(chr(10))} paths")
        return 0
    if not (ROOT / OUT).exists() or (ROOT / OUT).read_text() != text:
        print(f"{OUT} is stale: run scripts/extraction_paths.py --write", file=sys.stderr)
        return 1
    print(f"{OUT} is current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

The kept tree lists exact files only, so filter-repo cannot pull a lab file in through a parent directory. Files added to
Arda later do not appear until `--write` is re-run. `--check` and its test enforce that.

In `scripts/lab_manifest.py`, change the `stays_in_engine` rule from `m == "missions/judge"` to
`m in ("missions/judge", "missions/judge_tools")`. Then run `--write` for the manifest, and update `test_lab_manifest.py`'s
mission assertion so it expects `missions/judge_tools` in `stays_in_engine` and `unclassified == []`.

- [ ] **Step 5: Generate the files and run the tests**

```bash
cd ~/arda-telperion-step1/telperion
PY=~/telperion-tools/venv314/bin/python
PYTHONPATH=src $PY scripts/lab_manifest.py --write && PYTHONPATH=src $PY scripts/extraction_paths.py --write
PYTHONPATH=src $PY -m pytest tests/test_extraction_paths.py tests/test_lab_manifest.py -q -p no:cacheprovider
```
Expected: all tests pass. Report the path count.

- [ ] **Step 6: Commit** (in `~/arda-telperion-step1`):

```bash
sudo -u peterwmurphy git add telperion/docs/extraction/ telperion/scripts/extraction_paths.py telperion/scripts/lab_manifest.py telperion/tests/test_extraction_paths.py telperion/tests/test_lab_manifest.py
sudo -u peterwmurphy git commit -m "telperion: extraction rules + generated filter-repo path list (step 2)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: Two baselines, and resolving every difference

**Files:**
- Create: `telperion/scripts/extraction_baseline.py`
- Create (generated): `telperion/docs/extraction/BASELINE.json`, `telperion/docs/extraction/BASELINE.md`
- Modify: `telperion/docs/extraction/extraction_rules.toml` (fill `test_data_examples`, and add `[reclassify] lab_tests = [...]`
  if needed)
- Modify: `telperion/scripts/lab_manifest.py`. It honours `[reclassify]`: in `build_manifest`, after computing `lab_tests`,
  read `docs/extraction/extraction_rules.toml` (if present) and move every path in `[reclassify] lab_tests` from
  `engine_tests` to `lab_tests`, keeping both lists sorted. Add a test showing that a reclassified path lands in
  `lab_tests`.
- Test: `telperion/tests/test_extraction_baseline.py`

**Interfaces:**
- Consumes: `kept_files(root)` (Task 1).
- Produces:
  - `extraction_baseline.py full`: runs the kept engine tests in the Arda worktree and writes per-test outcomes.
  - `extraction_baseline.py dry`: materialises `~/telperion-tools/extract/dry/` (kept files only, `telperion/` prefix
    stripped), runs the same tests there, writes outcomes, and also imports every kept module.
  - `extraction_baseline.py compare`: writes `BASELINE.json` (`{"full": {...}, "dry": {...}, "diffs": [...]}`, keyed by pytest
    nodeid, outcome in passed/failed/skipped/error) and `BASELINE.md`, a human table of the diffs with a resolution column.
    It exits 1 while any diff has no resolution.

- [ ] **Step 1: Install the CI dependency set into the venv**

```bash
~/telperion-tools/venv314/bin/pip install -q cvxpy "scs<3.3" pyyaml && chown -R peterwmurphy:staff ~/telperion-tools/venv314
```

- [ ] **Step 2: Write the failing tests**

```python
# telperion/tests/test_extraction_baseline.py
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import extraction_baseline as eb  # noqa: E402


def test_parse_junit_outcomes(tmp_path):
    x = tmp_path / "r.xml"
    x.write_text('<testsuites><testsuite>'
                 '<testcase classname="tests.test_a" name="test_ok"/>'
                 '<testcase classname="tests.test_a" name="test_bad"><failure message="m"/></testcase>'
                 '<testcase classname="tests.test_b" name="test_sk"><skipped message="s"/></testcase>'
                 '<testcase classname="tests.test_b" name="test_er"><error message="e"/></testcase>'
                 '</testsuite></testsuites>')
    assert eb.parse_junit(x) == {"tests.test_a::test_ok": "passed", "tests.test_a::test_bad": "failed",
                                 "tests.test_b::test_sk": "skipped", "tests.test_b::test_er": "error"}


def test_diffs_and_resolutions():
    full = {"a::x": "passed", "a::y": "passed", "a::z": "skipped"}
    dry = {"a::x": "passed", "a::y": "failed"}
    res = {"a::y": "test_data_examples += log_combination"}
    d = eb.diffs(full, dry, res)
    assert d == [{"test": "a::y", "full": "passed", "dry": "failed",
                  "resolution": "test_data_examples += log_combination"},
                 {"test": "a::z", "full": "skipped", "dry": "missing", "resolution": ""}]


def test_unresolved_count():
    assert eb.unresolved([{"resolution": ""}, {"resolution": "x"}]) == 1
```

- [ ] **Step 3: Run them to verify they fail**

Run: `cd ~/arda-telperion-step1/telperion && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_extraction_baseline.py -q -p no:cacheprovider`
Expected: FAIL with `ModuleNotFoundError: extraction_baseline`.

- [ ] **Step 4: Implement `telperion/scripts/extraction_baseline.py`**

```python
#!/usr/bin/env python3
"""Step 2 baselines: engine tests in Arda (full) vs in a kept-files-only tree (dry); diffs need resolutions."""
from __future__ import annotations

import argparse, json, os, shutil, subprocess, sys, tomllib
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from extraction_paths import kept_files  # noqa: E402

PY = os.path.expanduser("~/telperion-tools/venv314/bin/python")
SCRATCH = Path(os.path.expanduser("~/telperion-tools/extract"))
OUTDIR = ROOT / "docs/extraction"


def parse_junit(path: Path) -> dict:
    out = {}
    for tc in ET.parse(path).getroot().iter("testcase"):
        key = f"{tc.get('classname')}::{tc.get('name')}"
        tags = {c.tag for c in tc}
        out[key] = ("failed" if "failure" in tags else "error" if "error" in tags
                    else "skipped" if "skipped" in tags else "passed")
    return out


def diffs(full: dict, dry: dict, resolutions: dict) -> list:
    return [{"test": t, "full": full[t], "dry": dry.get(t, "missing"), "resolution": resolutions.get(t, "")}
            for t in sorted(full) if full[t] != dry.get(t, "missing")]


def unresolved(ds: list) -> int:
    return sum(1 for d in ds if not d["resolution"])


def _engine_test_files() -> list[str]:
    return sorted(p[len("telperion/"):] for p in kept_files(ROOT)
                  if p.startswith("telperion/tests/") and Path(p).name.startswith("test_"))


def _run(tree: Path, junit: Path) -> None:
    env = {**os.environ, "PYTHONPATH": str(tree / "src")}
    subprocess.run([PY, "-X", "faulthandler", "-m", "pytest", *_engine_test_files(), "-q", "-p", "no:cacheprovider",
                    "--junitxml", str(junit)], cwd=tree, env=env)


def cmd_full() -> None:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    _run(ROOT, SCRATCH / "full.xml")


def cmd_dry() -> None:
    dry = SCRATCH / "dry"
    shutil.rmtree(dry, ignore_errors=True)
    for p in kept_files(ROOT):
        rel = p[len("telperion/"):]
        (dry / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / rel, dry / rel)
    _run(dry, SCRATCH / "dry.xml")
    # every kept module must import in the dry tree (Review Focus 1)
    mods = sorted(p[len("telperion/src/"):-3].replace("/", ".").removesuffix(".__init__")
                  for p in kept_files(ROOT) if p.startswith("telperion/src/") and p.endswith(".py"))
    bad = []
    for m in mods:
        r = subprocess.run([PY, "-c", f"import {m}"], cwd=dry, env={**os.environ, "PYTHONPATH": str(dry / "src")},
                           capture_output=True, text=True)
        if r.returncode != 0:
            bad.append({"module": m, "error": (r.stderr.strip().splitlines() or ["?"])[-1]})
    (SCRATCH / "dry_imports.json").write_text(json.dumps(bad, indent=2))


def cmd_compare() -> int:
    rules = tomllib.loads((ROOT / "docs/extraction/extraction_rules.toml").read_text())
    res = rules.get("resolutions", {})
    full, dry = parse_junit(SCRATCH / "full.xml"), parse_junit(SCRATCH / "dry.xml")
    ds = diffs(full, dry, res)
    imports = json.loads((SCRATCH / "dry_imports.json").read_text())
    (OUTDIR / "BASELINE.json").write_text(json.dumps({"full": full, "dry": dry, "diffs": ds,
                                                      "dry_import_failures": imports}, indent=1, sort_keys=True) + "\n")
    lines = ["# Step 2 baseline: Arda (full) vs lab-removed dry run", "",
             f"Engine tests: {len(full)} in full, {len(dry)} in dry. Differences: {len(ds)}; "
             f"unresolved: {unresolved(ds)}. Dry-run module import failures: {len(imports)}.", "",
             "| test | full | dry | resolution |", "|---|---|---|---|"]
    lines += [f"| `{d['test']}` | {d['full']} | {d['dry']} | {d['resolution'] or '**UNRESOLVED**'} |" for d in ds]
    lines += ["", "## Module import failures in the dry tree", ""]
    lines += [f"- `{i['module']}`: {i['error']}" for i in imports] or ["none"]
    (OUTDIR / "BASELINE.md").write_text("\n".join(lines) + "\n")
    return 1 if unresolved(ds) or imports else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["full", "dry", "compare"])
    c = ap.parse_args().cmd
    sys.exit({"full": cmd_full, "dry": cmd_dry}.get(c, lambda: None)() or (cmd_compare() if c == "compare" else 0))
```

- [ ] **Step 5: Run the unit tests (green), then the two baselines**

```bash
cd ~/arda-telperion-step1/telperion && PY=~/telperion-tools/venv314/bin/python
PYTHONPATH=src $PY -m pytest tests/test_extraction_baseline.py -q -p no:cacheprovider
PYTHONPATH=src $PY scripts/extraction_baseline.py full      # ~20-30 min (CI's suite is ~22 min)
PYTHONPATH=src $PY scripts/extraction_baseline.py dry
PYTHONPATH=src $PY scripts/extraction_baseline.py compare; echo "compare exit $?"
```
Expected: the unit tests pass. `compare` exits 1 on the first pass and lists the diffs. The step 1 final review predicted
about 25 tests that read lab data.

Before `full`, run `git -C ~/arda-telperion-step1 status --short`. Run it again after `full`, and `git checkout --` any file
the suite rewrote. One example is `examples/jensen_hyperbolicity/lean/JensenHyperbolicity.lean`, which the rh_jensen e2e
test regenerates. That file is lab, and it is not run here.

- [ ] **Step 6: Resolve every difference.** For each diff in `BASELINE.md`, choose exactly one of these, in this order of
  preference, and record it under `[resolutions]` in `extraction_rules.toml` as `"<nodeid>" = "<what was done>"`:
  1. The test reads a domain-neutral example or engine file: add the example to `test_data_examples`, or the file to
     `extra_files`. Write a resolution such as `"test_data_examples += log_combination"`.
  2. The test reads RH or BG material (`zeta_*`, `rvm_bridge`, `li_positivity`, `quasicrystal`, `zero_free_bridge`, BG
     examples, the moving missions, or `research/`): add the test FILE under `[reclassify] lab_tests` and write a
     resolution such as `"reclassified lab: reads missions/anduril"`. Then re-run `lab_manifest.py --write` and
     `extraction_paths.py --write`. The file now leaves the kept set, so its nodeids drop out of `full` on the next `full`
     run.
  3. The test exercises Arda-side tooling (`scripts/schedule_health.py`, `scripts/bg_spine_audit.py`, Arda workflows):
     reclassify it as lab, with a resolution such as `"reclassified lab: Arda CI tooling"`.
  4. A module import failure means a kept module imports a dropped one. STOP and report DONE_WITH_CONCERNS. That is a
     step 1 boundary escape, and it must not be patched here.

  Re-run `full` (only when a test file was reclassified), `dry` and `compare` until `compare` exits 0. Report the final
  counts and the full resolution table.

- [ ] **Step 7: Commit**

```bash
sudo -u peterwmurphy git add telperion/scripts/extraction_baseline.py telperion/tests/test_extraction_baseline.py telperion/docs/extraction/ telperion/scripts/lab_manifest.py
sudo -u peterwmurphy git commit -m "telperion: step 2 baselines (full vs lab-removed dry run), every diff resolved

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Filtered history into `~/telperion-repo`, scanned

**Files:**
- Create: `telperion/scripts/extract_repo.sh` (in Arda)
- Create (outside Arda): `~/telperion-repo` (the filtered repository); `~/telperion-tools/extract/gitleaks.json`

**Interfaces:**
- Consumes: `docs/extraction/EXTRACTION_PATHS.txt` (Tasks 1 and 2, final).
- Produces: `~/telperion-repo` on branch `main`. Its tree equals the dry-run tree byte for byte, and its history contains no
  `Claude-Session:` lines and no gitleaks findings, or only findings the owner accepts.

- [ ] **Step 1: Install gitleaks**: `brew install gitleaks` as peterwmurphy (`sudo -u peterwmurphy brew install gitleaks`).
  Check with `gitleaks version`.

- [ ] **Step 2: Write `telperion/scripts/extract_repo.sh`**

```bash
#!/usr/bin/env bash
# Step 2: filter Arda's history down to the kept Telperion paths into ~/telperion-repo (local only).
set -euo pipefail
ARDA="${1:-$HOME/arda-telperion-step1}"
OUT="${2:-$HOME/telperion-repo}"
PATHS="$ARDA/telperion/docs/extraction/EXTRACTION_PATHS.txt"
[ -e "$OUT" ] && { echo "$OUT exists; refusing to overwrite" >&2; exit 1; }
git clone --no-local --single-branch --branch "$(git -C "$ARDA" rev-parse --abbrev-ref HEAD)" "$ARDA" "$OUT"
cd "$OUT"
git remote remove origin
git filter-repo --force --paths-from-file "$PATHS" --path-rename telperion/: \
  --message-callback '
import re
return re.sub(rb"(?im)^[ \t]*claude-session:.*\n?", b"", message)
'
git branch -m main
echo "commits: $(git rev-list --count HEAD)"
```
Make it executable. It refuses to overwrite `$OUT`, removes the origin remote, and never pushes.

- [ ] **Step 3: Run it, then verify.** Run the script as peterwmurphy. Then:

```bash
cd ~/telperion-repo
git log --format=%B | grep -ciE '^[[:space:]]*claude-session:' && echo "FAIL: trailer survived" || echo "trailers: none"
diff -r --exclude=.git --exclude=__pycache__ ~/telperion-repo ~/telperion-tools/extract/dry && echo "tree == dry run"
gitleaks detect --source . --log-opts="--all" --report-format json --report-path ~/telperion-tools/extract/gitleaks.json; echo "gitleaks exit $?"
git ls-files | grep -E '^(src/telperion/(bg|rh_jensen)/|research/|missions/(rh|mirrormere|anduril|bg)/)' && echo "FAIL: lab path" || echo "no lab paths"
```
Expected:
- `trailers: none`;
- `tree == dry run`;
- gitleaks exit 0, or a findings file to bring to the owner. Do NOT rewrite history to remove findings without the owner's
  word;
- `no lab paths`.

The dry run leaves `__pycache__/` directories in the dry tree. Run the diff with `--exclude=__pycache__` as well, and never
exclude real files.

- [ ] **Step 4: Commit the script in Arda**

```bash
cd ~/arda-telperion-step1 && sudo -u peterwmurphy git add telperion/scripts/extract_repo.sh
sudo -u peterwmurphy git commit -m "telperion: extract_repo.sh (filter-repo into a local standalone repo)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Standalone scaffolding commit in `~/telperion-repo`

**Files** (all in `~/telperion-repo`):
- Create: `LICENSING.md`, `.github/workflows/ci.yml`
- Modify: `README.md` (rewrite it for a standalone engine: verbose, conversational), `pyproject.toml` (version
  `0.2.0.dev0`; the `[tool.pytest.ini_options]` testpaths stay), `CHANGELOG.md` (new top entry).

**Interfaces:**
- Produces: a CI workflow with one job, `test`, on Python 3.11 and 3.14. It uses the same pip set as Arda's
  `telperion-test.yml` and runs `pytest tests -q -rs`. That includes `tests/test_engine_boundary.py`, which keeps any lab
  import from coming back. The Arda-side tooling (`lab_manifest.py`, `extraction_*.py`, `extract_repo.sh`,
  `docs/extraction/`) was never kept (Task 1 `[drop]`), so there is nothing to delete.

- [ ] **Step 1: Write `.github/workflows/ci.yml`**

```yaml
name: telperion-ci
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python: ["3.11", "3.14"]
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: ${{ matrix.python }}
      - run: pip install -e . sympy pytest networkx numpy cvxpy "scs<3.3" pyyaml "python-flint==0.9.0" mpmath
      - run: python -X faulthandler -m pytest tests -q -rs
```
Copy the install line from Arda's `.github/workflows/telperion-test.yml:56`, then add `-e .` and `mpmath`. If that file pins a
different sympy matrix, mirror it.

- [ ] **Step 2: Write `LICENSING.md`**, modelled on `~/tenth-discriminant/LICENSING.md`. Read it first. It says:
  - the engine (`src/`, CLI, MCP, tooling) is BSL-1.1, see `LICENSE` and `CLA.md`, with the Change License Apache-2.0 three
    years after each release;
  - `examples/`, `docs/` and emitted certificates are Apache-2.0 (code) / CC-BY-4.0 (documents);
  - snapshots published before 2026-08-21 inside Arda are Apache-2.0;
  - contributions to the engine require the CLA.

- [ ] **Step 3: Rewrite `README.md`.** Keep its technical sections, and remove or redirect anything that describes Arda's BG
  or RH work. Add an opening that tells the reader:
  - what Telperion is (a certificate engine: sympy families -> exact validation -> kernel-checked Lean 4);
  - why it is now standalone;
  - how vendoring works (a pointer: "see VENDORING.md, added in step 7");
  - where the BG and RH applications live (Arda and the public repos, as consumers).

  Show the owner the README diff in the report.

- [ ] **Step 4: Update `pyproject.toml`** to version `0.2.0.dev0`. Add a top `CHANGELOG.md` entry, "0.2.0.dev0: standalone
  repository", listing what was extracted and what stayed in Arda, including the Arda-side extraction tooling.

- [ ] **Step 5: Commit** in `~/telperion-repo` as peterwmurphy, with the standard trailer:
  `git commit -m "standalone: CI, LICENSING, README, 0.2.0.dev0"`.

---

### Task 5: Test equivalence in the new repository

**Files:**
- Create (outside the repo): `~/telperion-tools/extract/new.xml`; `~/telperion-tools/extract/EQUIVALENCE.md`

- [ ] **Step 1: Run the suite in `~/telperion-repo`**

```bash
cd ~/telperion-repo && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -X faulthandler -m pytest tests -q -p no:cacheprovider --junitxml ~/telperion-tools/extract/new.xml
```

- [ ] **Step 2: Compare per test, against the dry-run outcomes** in `~/arda-telperion-step1/telperion/docs/extraction/BASELINE.json`
  (`dry`). Use `parse_junit` from Arda's `scripts/extraction_baseline.py`, imported by path. Every nodeid must have the same
  outcome. Write `EQUIVALENCE.md` with the counts
  and any differences.
  Expected: 0 differences. A difference is a defect. Report it as DONE_WITH_CONCERNS with the nodeid. Do not edit tests to
  make it pass.

- [ ] **Step 3: Owner gate (STOP).** Report the following:
  - `~/telperion-repo`'s commit count;
  - its tree size;
  - the gitleaks result;
  - `BASELINE.md`'s resolution table;
  - `EQUIVALENCE.md`;
  - the README diff.

  Creating `DrMurphyIsIn/telperion` on GitHub and pushing are the OWNER's decision, and they are not part of this plan.
