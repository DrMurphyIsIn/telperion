# Step 3: Kernel Policy as an Engine Check, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The engine ships a kernel-policy checker that every consumer runs in CI. It enforces two things:
- a Lean toolchain floor (v4.34.1), with a named exception list that can only shrink;
- judge configs that never turn nanoda off, except for re-judged heavy nodes, and that permit exactly the three standard
  axioms.

**Architecture:**
- **Pure policy module.** `telperion.checks.kernel_policy` holds toolchain parsing and comparison, project discovery, the
  exceptions file, and the judge-config rules. It has no I/O beyond reading files.
- **Judge bundling.** `missions/judge.py` calls the config rule on every challenge it renders, so a bad config cannot be
  produced.
- **CLI.** `telperion kernel-policy check` runs the policy against a consumer checkout.
- **Arda adoption.** Arda adopts the policy in step 7, when it switches to vendoring. Its exceptions file is generated then.

**Tech Stack:** Python 3.11+, tomllib, pytest. The repo is `~/telperion-repo`, the step 2 output. All paths below are
relative to its root.

**Spec:** `docs/superpowers/specs/2026-10-27-telperion-standalone-design.md`, section 5.1 and rollout step 3.
Owner rule (2026-10-27): heavy nodes keep nanoda off on hosted runners ONLY with a passing local re-judge.

## Global Constraints

- **Floor:** `v4.34.1`, the first release line carrying the v4.33.1 kernel soundness fixes #14806, #14807, #14808, #14582
  and #14849.
- **Toolchain strings:** `leanprover/lean4:vMAJ.MIN.PATCH[-rcN]`. An rc sorts below its release, so
  `v4.34.0-rc2 < v4.34.0 < v4.34.1 < v4.35.0-rc3`.
- **`CLEAN_AXIOMS`:** exactly `("propext", "Quot.sound", "Classical.choice")`, imported from `telperion.missions.judge`
  rather than redefined.
- **Exceptions file:** consumer-owned TOML, `[[exception]]` tables with `project`, `toolchain` and `reason`. It can only
  shrink:
  - a listed project at or above the floor is an error ("stale exception: remove it");
  - so is a listed project that no longer exists;
  - so is a listed toolchain that differs from the project's real one.
- **Git:** `~/telperion-repo` is owned by peterwmurphy, so run git there as that user. Commits carry
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`, with no Claude-Session trailer. Nothing is pushed.
- **Tests:** `PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest <files> -q -p no:cacheprovider`.

## Review Focus

1. **A toolchain string the parser has never seen.** Examples: `leanprover/lean4:nightly-2026-10-01`, a bare `v4.35.0`, or
   trailing whitespace. The expected outcome is a clear error, never a silent pass (Task 1
   `test_unparseable_toolchain_is_a_problem`).
2. **Lake build directories.** `lean-toolchain` files under `.lake/packages/**` belong to dependencies such as Mathlib. They
   must not be scanned (Task 1 `test_lake_packages_are_ignored`).
3. **A heavy node whose config has nanoda off.** It passes the config rule only when the caller says the node is heavy. The
   judge must pass the node's real flag, not `True` (Task 2 `test_build_bundle_rejects_nanoda_off_for_non_heavy`).
4. **A config permitting an extra axiom such as `sorryAx`.** It must fail, even with nanoda on (Task 2
   `test_extra_axiom_rejected`).
5. **An empty exceptions file versus a missing one.** Both mean "no exceptions". A missing file is not an error (Task 1
   `test_missing_exceptions_file_means_none`).

---

### Task 1: The policy module and the CLI

**Files:**
- Create: `src/telperion/checks/__init__.py` (empty docstring module) and `src/telperion/checks/kernel_policy.py`
- Modify: `src/telperion/cli.py`, adding a `kernel-policy` subcommand with a `check` action
- Test: `tests/test_kernel_policy.py`

**Interfaces:**
- Produces:
  - `FLOOR = "leanprover/lean4:v4.34.1"`;
  - `parse_toolchain(s: str) -> tuple[int, int, int, int, int]`, returning `(maj, min, patch, is_release, rc)`. It raises
    `ValueError` on an unknown form;
  - `below_floor(toolchain: str) -> bool`;
  - `find_projects(root: Path) -> list[tuple[str, str]]`, returning `(project_dir_rel, toolchain)` for each tracked
    `lean-toolchain` outside any `.lake/`;
  - `load_exceptions(path: Path) -> dict[str, dict]`;
  - `policy_problems(root: Path, exceptions: dict) -> list[str]`;
  - CLI: `telperion kernel-policy check [--root DIR] [--exceptions FILE]` prints the problems and exits 1 if there are any.
    The default exceptions file is `<root>/kernel_policy_exceptions.toml`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_kernel_policy.py
import subprocess
from pathlib import Path
import pytest
from telperion.checks import kernel_policy as kp


@pytest.mark.parametrize("a,b", [
    ("leanprover/lean4:v4.34.0-rc2", "leanprover/lean4:v4.34.0"),
    ("leanprover/lean4:v4.34.0", "leanprover/lean4:v4.34.1"),
    ("leanprover/lean4:v4.34.1", "leanprover/lean4:v4.35.0-rc3"),
    ("leanprover/lean4:v4.32.0", "leanprover/lean4:v4.33.0-rc2"),
])
def test_order(a, b):
    assert kp.parse_toolchain(a) < kp.parse_toolchain(b)


def test_floor():
    assert kp.below_floor("leanprover/lean4:v4.32.0")
    assert kp.below_floor("leanprover/lean4:v4.34.0-rc2")
    assert not kp.below_floor("leanprover/lean4:v4.34.1")
    assert not kp.below_floor("leanprover/lean4:v4.35.0-rc3\n")


def _repo(tmp_path, projects):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    for d, tc in projects.items():
        (tmp_path / d).mkdir(parents=True, exist_ok=True)
        (tmp_path / d / "lean-toolchain").write_text(tc + "\n")
    subprocess.run(["git", "-C", str(tmp_path), "add", "-A"], check=True)
    return tmp_path


def test_unparseable_toolchain_is_a_problem(tmp_path):
    root = _repo(tmp_path, {"a": "leanprover/lean4:nightly-2026-10-01"})
    assert any("cannot parse" in p for p in kp.policy_problems(root, {}))


def test_lake_packages_are_ignored(tmp_path):
    root = _repo(tmp_path, {"a": "leanprover/lean4:v4.35.0", "a/.lake/packages/mathlib": "leanprover/lean4:v4.20.0"})
    assert kp.find_projects(root) == [("a", "leanprover/lean4:v4.35.0")]


def test_below_floor_without_exception_fails_and_with_exception_passes(tmp_path):
    root = _repo(tmp_path, {"old": "leanprover/lean4:v4.32.0", "new": "leanprover/lean4:v4.35.0"})
    assert any("old" in p and "below the floor" in p for p in kp.policy_problems(root, {}))
    ex = {"old": {"toolchain": "leanprover/lean4:v4.32.0", "reason": "pre-fix island; nanoda required"}}
    assert kp.policy_problems(root, ex) == []


def test_stale_and_mismatched_exceptions_fail(tmp_path):
    root = _repo(tmp_path, {"p": "leanprover/lean4:v4.35.0", "q": "leanprover/lean4:v4.32.0"})
    ex = {"p": {"toolchain": "leanprover/lean4:v4.32.0", "reason": "x"},
          "q": {"toolchain": "leanprover/lean4:v4.33.0-rc2", "reason": "x"},
          "gone": {"toolchain": "leanprover/lean4:v4.32.0", "reason": "x"}}
    probs = "\n".join(kp.policy_problems(root, ex))
    assert "p" in probs and "stale exception" in probs
    assert "q" in probs and "toolchain mismatch" in probs
    assert "gone" in probs and "no such project" in probs


def test_missing_exceptions_file_means_none(tmp_path):
    assert kp.load_exceptions(tmp_path / "nope.toml") == {}
    (tmp_path / "e.toml").write_text("")
    assert kp.load_exceptions(tmp_path / "e.toml") == {}


def test_cli_exit_codes(tmp_path):
    import sys
    root = _repo(tmp_path, {"old": "leanprover/lean4:v4.32.0"})
    cmd = [sys.executable, "-m", "telperion.cli", "kernel-policy", "check", "--root", str(root)]
    env = {**__import__("os").environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1] / "src")}
    assert subprocess.run(cmd, env=env, capture_output=True).returncode == 1
    (root / "kernel_policy_exceptions.toml").write_text(
        '[[exception]]\nproject = "old"\ntoolchain = "leanprover/lean4:v4.32.0"\nreason = "nanoda required"\n')
    assert subprocess.run(cmd, env=env, capture_output=True).returncode == 0
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cd ~/telperion-repo && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_kernel_policy.py -q -p no:cacheprovider`
Expected: FAIL with `ModuleNotFoundError: telperion.checks`.

- [ ] **Step 3: Implement `src/telperion/checks/kernel_policy.py`**

```python
"""Kernel policy (spec 5.1): a Lean toolchain floor with a shrink-only exception list, and judge configs that
never turn the second kernel (nanoda) off except for re-judged heavy nodes.

Lean v4.33.1 fixed kernel soundness bugs (#14806 order-dependent defeq cache, #14807 is_prop on a stuck type,
#14808 recursor checks, #14582 non-uniform inductives, #14849 numeral size). v4.34.1 is the first line we pin
that carries them; older projects are allowed only by name, and only with nanoda as a second kernel.
"""
from __future__ import annotations

import re
import subprocess
import tomllib
from pathlib import Path

FLOOR = "leanprover/lean4:v4.34.1"
_TC = re.compile(r"^leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?$")


def parse_toolchain(s: str) -> tuple[int, int, int, int, int]:
    m = _TC.match(s.strip())
    if not m:
        raise ValueError(f"cannot parse Lean toolchain {s.strip()!r}")
    maj, mi, pa, rc = m.groups()
    return (int(maj), int(mi), int(pa), 0 if rc else 1, int(rc or 0))


def below_floor(toolchain: str) -> bool:
    return parse_toolchain(toolchain) < parse_toolchain(FLOOR)


def find_projects(root: Path) -> list[tuple[str, str]]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout.decode()
    found = []
    for p in sorted(x for x in out.split("\0") if x):
        parts = Path(p).parts
        if parts[-1] != "lean-toolchain" or ".lake" in parts:
            continue
        found.append((str(Path(p).parent), (root / p).read_text().strip()))
    return found


def load_exceptions(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    doc = tomllib.loads(path.read_text())
    return {e["project"]: {"toolchain": e["toolchain"], "reason": e["reason"]} for e in doc.get("exception", [])}


def policy_problems(root: Path, exceptions: dict) -> list[str]:
    problems: list[str] = []
    projects = dict(find_projects(root))
    for proj, tc in projects.items():
        try:
            low = below_floor(tc)
        except ValueError as e:
            problems.append(f"{proj}: {e}")
            continue
        ex = exceptions.get(proj)
        if low and ex is None:
            problems.append(f"{proj}: {tc} is below the floor {FLOOR} and is not on the exception list")
        elif ex is not None and not low:
            problems.append(f"{proj}: stale exception: {tc} meets the floor; remove it from the list")
        elif ex is not None and ex["toolchain"].strip() != tc:
            problems.append(f"{proj}: toolchain mismatch: list says {ex['toolchain']}, project has {tc}")
    for proj in sorted(set(exceptions) - set(projects)):
        problems.append(f"{proj}: stale exception: no such project")
    return problems
```
The stale-exception test asserts the text "no such project" for a vanished project. The function prints it as part of
`stale exception: no such project`, so both assertions hold.

In `cli.py`, add a `kernel-policy` subparser with a `check` action, `--root` (default `.`) and `--exceptions` (default
`<root>/kernel_policy_exceptions.toml`). Follow the existing subparser pattern; read how `mission` is registered. The
action prints each problem and returns 1 if any exist; otherwise it prints `kernel policy: OK (<n> projects, <k>
exceptions)` and returns 0.

- [ ] **Step 4: Run the tests**

Run: `cd ~/telperion-repo && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_kernel_policy.py -q -p no:cacheprovider`
Expected: all pass.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/checks/ src/telperion/cli.py tests/test_kernel_policy.py
git commit -m "checks: kernel policy -- Lean toolchain floor v4.34.1 with a shrink-only exception list

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: The judge refuses to render a non-conforming config

**Files:**
- Modify: `src/telperion/checks/kernel_policy.py`, adding `judge_config_problems`
- Modify: `src/telperion/missions/judge.py`, in `build_bundle`. Every place a `Challenge` is created (the per-node path and
  the two compose-part paths) validates its config.
- Test: `tests/test_kernel_policy.py` (append)

**Interfaces:**
- Produces: `judge_config_problems(config: dict, *, node_heavy: bool) -> list[str]`.
  - `config["permitted_axioms"]` must equal `list(CLEAN_AXIOMS)`, compared as sets with no extras.
  - `config["enable_nanoda"]` must be True unless `node_heavy`.
  - `build_bundle` raises `JudgeError` listing the problems.

- [ ] **Step 1: Write the failing tests** (append):

```python
from telperion.checks.kernel_policy import judge_config_problems


def test_extra_axiom_rejected():
    cfg = {"permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"], "enable_nanoda": True}
    assert any("sorryAx" in p for p in judge_config_problems(cfg, node_heavy=False))


def test_nanoda_off_only_for_heavy():
    cfg = {"permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": False}
    assert judge_config_problems(cfg, node_heavy=True) == []
    assert any("nanoda" in p for p in judge_config_problems(cfg, node_heavy=False))


def test_build_bundle_rejects_nanoda_off_for_non_heavy(monkeypatch):
    import telperion.missions.judge as judge
    real = judge.challenge_config if hasattr(judge, "challenge_config") else None
    assert real is not None, "judge.challenge_config is the config factory the bundle uses"

    def off(*a, **k):
        k["enable_nanoda"] = False
        return real(*a, **k)

    monkeypatch.setattr(judge, "challenge_config", off)
    with pytest.raises(judge.JudgeError, match="nanoda"):
        judge.build_bundle(Path(__file__).resolve().parents[1], "canonical", only=None)
```

The last test needs a judge-able island in the standalone repo. If no committed island exists there (step 2 ships no
missions campaigns), build a minimal one in tmp_path: a campaign with one proved non-heavy node and a trivial Lean
artifact. Model it on `tests/missions_fixtures.py`, and call `build_bundle(tmp_root, "<island>")`. Keep the monkeypatch
and the assertion. Check the real name of the config factory first: grep `def challenge_config\|comparator_config` in
`missions/judge.py` and `comparator.py`, and use the name the bundle actually calls.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_kernel_policy.py -q -p no:cacheprovider`
Expected: the three new tests FAIL. The first two fail on an ImportError; the bundle test fails because no error is
raised.

- [ ] **Step 3: Implement.** In `kernel_policy.py`:

```python
def judge_config_problems(config: dict, *, node_heavy: bool) -> list[str]:
    from telperion.missions.judge import CLEAN_AXIOMS
    problems = []
    got, want = list(config.get("permitted_axioms", [])), list(CLEAN_AXIOMS)
    if sorted(got) != sorted(want):
        extra, missing = sorted(set(got) - set(want)), sorted(set(want) - set(got))
        problems.append(f"permitted_axioms must be exactly {want}; extra {extra}, missing {missing}")
    if not config.get("enable_nanoda", False) and not node_heavy:
        problems.append("enable_nanoda is off for a node without heavy_certificates (spec 5.1: nanoda required)")
    return problems
```
In `judge.py`, right after each `Challenge` construction inside `build_bundle` and `compose_parts`, validate with the
node's real heavy flag. That is `node_heavy` in the per-node path; compose parts use the heavy flag of the node they
belong to. On any problem, raise `JudgeError(f"{slug}: " + "; ".join(problems))`. Keep the import local to avoid an
import cycle (`kernel_policy` imports `judge` lazily).

- [ ] **Step 4: Run the tests and the judge suites**

Run: `PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m pytest tests/test_kernel_policy.py tests/test_missions_judge.py tests/test_judge_heavy.py -q -p no:cacheprovider`
Expected: all pass. The existing judge tests prove that every real config already conforms.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/checks/kernel_policy.py src/telperion/missions/judge.py tests/test_kernel_policy.py
git commit -m "judge: refuse to render a config with extra axioms or nanoda off for a non-heavy node

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Self-application and CI

**Files:**
- Create: `kernel_policy_exceptions.toml` at the repository root. It is empty apart from a header comment unless the
  canonical examples include a project below the floor.
- Modify: `.github/workflows/ci.yml`, adding a `kernel-policy` job.
- Modify: `docs/COMPARATOR.md`, adding a "Kernel policy" section: the floor, why it exists, the exceptions format, and the
  heavy-node re-judge rule.

- [ ] **Step 1: Run the policy on the repo itself**

Run: `cd ~/telperion-repo && PYTHONPATH=src ~/telperion-tools/venv314/bin/python -m telperion.cli kernel-policy check`
Expected: either `kernel policy: OK`, or a list of canonical-example projects below the floor. For each one listed, add an
`[[exception]]` with reason `"canonical example pinned before the v4.33.1 kernel fixes; judged with nanoda"`, and say so
in the report. Do NOT upgrade a toolchain in this task.

- [ ] **Step 2: Add the CI job** to `.github/workflows/ci.yml`:

```yaml
  kernel-policy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: "3.12"
      - run: pip install -e . && telperion kernel-policy check
```

- [ ] **Step 3: Write the docs section**, then commit:

```bash
git add kernel_policy_exceptions.toml .github/workflows/ci.yml docs/COMPARATOR.md
git commit -m "ci: kernel-policy job; COMPARATOR.md documents the floor and the heavy-node rule

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

**Hand-off to step 7:** when Arda vendors this release, it generates its own `kernel_policy_exceptions.toml` from
`find_projects` (about 133 v4.32.0 projects, plus the v4.33.0-rc2 and v4.34.0-rc1 ones) and adds the same CI job. That
belongs to step 7's plan, not this one.
