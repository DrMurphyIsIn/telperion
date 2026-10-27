# Step 1: Engine/Lab Boundary inside Arda, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** No engine module imports any lab, checked statically and dynamically, so step 2 can cut the labs out of the new
repository cleanly. A manifest records exactly which sources and tests are lab material.

**Architecture:**
- The engine's five real imports of the RH lab all go through two pure helpers. They are repointed to engine-owned copies:
  - `_arb_ball_to_fractions` already exists in `telperion.arb_enclosure`;
  - `disc2_margin` moves to a new engine module, `telperion.jensen_margin`.
- The BG-only boundary test is generalised to a fixed `LABS` set.
- A generator script writes `docs/extraction/LAB_MANIFEST.json`, listing lab sources, lab tests and mission/example data
  directories. Step 2 consumes it.

**Tech Stack:** Python 3.11+ (tested on 3.14), pytest, `ast`, python-flint (optional; flint-gated tests skip without it).

**Spec:** `telperion/docs/superpowers/specs/2026-10-27-telperion-standalone-design.md` (commit 2781e3a6f), section 3 and
rollout step 1.

**Spec refinement (owner to confirm at plan review).**
- The spec calls for a `telperion.plugins` entry-point seam through which labs register emitters and negative-control adapters.
- Investigation (origin/main af4fde897, 2026-10-27) found that no lab registers anything into the engine:
  - The engine's only real lab imports are four uses of `rh_jensen.coefficients._arb_ball_to_fractions` (`arb_fakes.py:105`,
    `emit_robin_growth.py:81`, `emit_bagchi_recurrence.py:64`, `bragg_coeff.py:101,166`) and one use of
    `rh_jensen.jensen.disc2_margin` (`emit_jensen_polynomial_hyperbolicity.py:96`).
  - `weil_form_eval` appears only in docstrings.
  - `import telperion` loads no lab module today.
- So this plan does NOT build an entry-point seam (YAGNI). It removes the five imports by repointing them to engine-owned
  code.
- If a lab later needs to contribute to an engine registry, the seam is added then.

## Global Constraints

- `LABS = ("bg", "rh_jensen", "bg_upper_bound", "bg_bulk_discharge", "li_coeff", "weil_form_eval")`. These are module or
  package names directly under `src/telperion/`. The engine is everything else under `src/telperion/`.
- Behaviour must not change: every existing test that passes before this step passes after it.
- `_arb_ball_to_fractions` semantics: exact dyadic `mid` and `rad` from `man_exp()`, returning `(mid - rad, mid + rad)` as
  `Fraction`s. Both existing copies compute exactly this, as the controller verified on 2026-10-27.
- Git runs as the user (`sudo -u peterwmurphy git ...`), in worktree `~/arda-telperion-standalone`, branch
  `docs/telperion-standalone-spec`. Commits carry `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and NO
  Claude-Session trailer. Nothing is pushed.
- Tests: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest <files> -q -p no:cacheprovider`.
  Never run the whole `tests/` tree: some tests build Lean.
- Do not touch `telperion/missions/*/nodes`, `telperion/missions/judge/rejudge_queue.sh` or `~/telperion-tools`. The step 0
  re-judge queue is running from this worktree.

## Review Focus

1. **A lab module imported lazily inside a function.** The static check must walk every `Import`/`ImportFrom` node in the
   whole AST, not just top-level statements (Task 3 test `test_checker_flags_function_level_lab_import`).
2. **A relative `from . import rh_jensen` spelling.** It must be flagged like `from .rh_jensen import x` (Task 3 test
   `test_checker_flags_from_dot_import_lab`).
3. **Engine subpackages** (`missions/`, `negctrl_adapters/`, `evolve/`, `prove2me/`) are engine and must be scanned, not
   skipped (Task 3 test `test_engine_files_include_subpackages`).
4. **The re-export shims stay importable.** `from telperion.rh_jensen.jensen import disc2_margin` must keep working for the
   RH lab and its tests (Task 2 test `test_rh_jensen_reexports_disc2_margin`).
5. **The manifest misses a lab test that imports a lab only via `importlib` or a string.** The generator must also catch a
   literal `"telperion.<lab>"` string (Task 4 test `test_manifest_catches_string_reference`).

---

### Task 1: Repoint the engine's Arb helper imports to `arb_enclosure`

**Files:**
- Modify:
  - `telperion/src/telperion/arb_fakes.py:105`;
  - `telperion/src/telperion/emit_robin_growth.py:81-83`;
  - `telperion/src/telperion/emit_bagchi_recurrence.py:64-66`;
  - `telperion/src/telperion/bragg_coeff.py:101,166`.
- Test: `telperion/tests/test_arb_helper_equivalence.py`

**Interfaces:**
- Consumes: `telperion.arb_enclosure._arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]` (existing).
- Produces: no new API. The four engine modules no longer import `telperion.rh_jensen`.

- [ ] **Step 1: Write the failing test**

```python
# telperion/tests/test_arb_helper_equivalence.py
"""The engine's Arb->Fraction helper must equal the RH lab's copy (step 1 repoints engine imports to it)."""
import ast
from fractions import Fraction
from pathlib import Path
import pytest

flint = pytest.importorskip("flint")
SRC = Path(__file__).resolve().parents[1] / "src" / "telperion"
REPOINTED = ["arb_fakes.py", "emit_robin_growth.py", "emit_bagchi_recurrence.py", "bragg_coeff.py"]


@pytest.mark.parametrize("ball", [
    flint.arb(0), flint.arb(1), flint.arb(-3, 0.5), flint.arb("1/3"), flint.arb.pi(),
    flint.arb(2) ** 70, flint.arb(2) ** -70, flint.arb(-7, 2 ** -60),
])
def test_engine_helper_equals_lab_helper(ball):
    from telperion.arb_enclosure import _arb_ball_to_fractions as engine
    from telperion.rh_jensen.coefficients import _arb_ball_to_fractions as lab
    lo, hi = engine(ball)
    assert (lo, hi) == lab(ball)
    assert isinstance(lo, Fraction) and lo <= hi


@pytest.mark.parametrize("fname", REPOINTED)
def test_repointed_module_does_not_import_rh_jensen(fname):
    tree = ast.parse((SRC / fname).read_text())
    bad = [n for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)
           and "rh_jensen" in (n.module or "")]
    assert not bad, f"{fname} still imports rh_jensen at line {bad[0].lineno}"
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_arb_helper_equivalence.py -v -p no:cacheprovider`
Expected: the 8 equivalence cases PASS (the copies already agree). The 4 `test_repointed_module_does_not_import_rh_jensen`
cases FAIL, naming the line.

- [ ] **Step 3: Repoint the imports**

In each of the four files, replace every `from .rh_jensen.coefficients import _arb_ball_to_fractions` and every
`from telperion.rh_jensen.coefficients import _arb_ball_to_fractions` with:
```python
from .arb_enclosure import _arb_ball_to_fractions
```
In `emit_robin_growth.py` and `emit_bagchi_recurrence.py` the import sits in a `try/except ImportError` pair, with the
relative form first and the absolute form second. Collapse the pair to the single relative import above. Keep it in the same
place (inside the function), so the module still loads without flint. `arb_enclosure` itself guards flint with
`_FLINT_AVAILABLE`.

- [ ] **Step 4: Run the new test and every test of the four modules**

Run:
```bash
cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_arb_helper_equivalence.py $(grep -lE "arb_fakes|robin_growth|bagchi_recurrence|bragg_coeff" tests/*.py) -q -p no:cacheprovider
```
Expected: all pass. Report the count, and any skips caused by a missing flint.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/{arb_fakes,emit_robin_growth,emit_bagchi_recurrence,bragg_coeff}.py telperion/tests/test_arb_helper_equivalence.py
sudo -u peterwmurphy git commit -m "telperion: engine uses its own Arb->Fraction helper, not the rh_jensen lab's

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: Move `disc2_margin` into the engine

**Files:**
- Create: `telperion/src/telperion/jensen_margin.py`
- Modify:
  - `telperion/src/telperion/rh_jensen/jensen.py`: delete the `disc2_margin` body (from line 87) and re-export it;
  - `telperion/src/telperion/emit_jensen_polynomial_hyperbolicity.py:96`.
- Test: `telperion/tests/test_jensen_margin.py`

**Interfaces:**
- Produces: `telperion.jensen_margin.disc2_margin(box: list[tuple[Fraction, Fraction]]) -> Fraction`. It is the same code
  and docstring, moved verbatim. `telperion.rh_jensen.jensen.disc2_margin` is the same object, re-exported.

- [ ] **Step 1: Write the failing test**

```python
# telperion/tests/test_jensen_margin.py
from fractions import Fraction as F
import pytest


def test_engine_disc2_margin_positive_box():
    from telperion.jensen_margin import disc2_margin
    # c0=1, c1=3, c2=1  ->  D = 9 - 4 = 5
    assert disc2_margin([(F(1), F(1)), (F(3), F(3)), (F(1), F(1))]) == F(5)


def test_engine_disc2_margin_straddling_c1_uses_zero():
    from telperion.jensen_margin import disc2_margin
    assert disc2_margin([(F(1), F(1)), (F(-1), F(1)), (F(1), F(1))]) == F(-4)


def test_engine_disc2_margin_rejects_wrong_length():
    from telperion.jensen_margin import disc2_margin
    with pytest.raises(ValueError):
        disc2_margin([(F(1), F(1))])


def test_rh_jensen_reexports_disc2_margin():
    pytest.importorskip("flint")  # rh_jensen imports flint at module load
    from telperion.jensen_margin import disc2_margin as engine
    from telperion.rh_jensen.jensen import disc2_margin as lab
    assert lab is engine


def test_emitter_does_not_import_rh_jensen():
    import ast
    from pathlib import Path
    p = Path(__file__).resolve().parents[1] / "src/telperion/emit_jensen_polynomial_hyperbolicity.py"
    assert "rh_jensen" not in {(n.module or "") for n in ast.walk(ast.parse(p.read_text()))
                                if isinstance(n, ast.ImportFrom)}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_jensen_margin.py -v -p no:cacheprovider`
Expected: FAIL with `ModuleNotFoundError: telperion.jensen_margin`, and the last test fails on `rh_jensen.jensen`.

- [ ] **Step 3: Move the function**

Create `telperion/src/telperion/jensen_margin.py` with this header, followed by the function body copied VERBATIM from
`rh_jensen/jensen.py`, from line 87 (`def disc2_margin`) to the end of that function:
```python
"""Rigorous rational margin of the degree-2 Jensen discriminant (engine-owned; flint-free).

Moved from telperion.rh_jensen.jensen in step 1 of the standalone extraction so the engine's
`emit_jensen_polynomial_hyperbolicity` does not import the RH lab. rh_jensen re-exports it.
"""
from __future__ import annotations

from fractions import Fraction
```
In `rh_jensen/jensen.py`, delete the function body and add, next to the other imports:
```python
from telperion.jensen_margin import disc2_margin  # noqa: F401  (moved to the engine; re-exported)
```
In `emit_jensen_polynomial_hyperbolicity.py:96`, replace the lazy import with:
```python
        from .jensen_margin import disc2_margin
```
and drop its now-stale "dependency cycle" comment.

- [ ] **Step 4: Run the tests**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_jensen_margin.py tests/rh_jensen/test_jensen.py tests/rh_jensen/test_emit_jensen.py $(grep -l "jensen_polynomial_hyperbolicity" tests/*.py) -q -p no:cacheprovider`
Expected: all pass.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/jensen_margin.py telperion/src/telperion/rh_jensen/jensen.py telperion/src/telperion/emit_jensen_polynomial_hyperbolicity.py telperion/tests/test_jensen_margin.py
sudo -u peterwmurphy git commit -m "telperion: move disc2_margin into the engine (rh_jensen re-exports it)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Generalise the boundary test to every lab

**Files:**
- Create: `telperion/src/telperion/boundary.py`, which holds the checker so step 2's repository can reuse it in CI.
- Modify: `telperion/tests/test_core_boundary.py`. Keep its three existing BG tests unchanged and add the general ones.
- Test: `telperion/tests/test_core_boundary.py`

**Interfaces:**
- Produces:
  - `telperion.boundary.LABS: tuple[str, ...]`, equal to the Global Constraints value;
  - `telperion.boundary.engine_files(src_pkg: Path) -> list[Path]`, every `.py` under `src/telperion/` except lab
    packages or modules;
  - `telperion.boundary.lab_imports(path: Path) -> list[tuple[int, str]]`, giving `(lineno, spelling)` for every import of a
    lab anywhere in the file's AST.

- [ ] **Step 1: Write the failing tests** (append to `tests/test_core_boundary.py`):

```python
from telperion.boundary import LABS, engine_files, lab_imports


def test_labs_constant():
    assert LABS == ("bg", "rh_jensen", "bg_upper_bound", "bg_bulk_discharge", "li_coeff", "weil_form_eval")


def test_engine_files_include_subpackages():
    names = {p.relative_to(CORE_DIR).as_posix() for p in engine_files(CORE_DIR)}
    assert "missions/judge.py" in names and "negctrl_adapters/__init__.py" in names
    assert not any(n.startswith(("bg/", "rh_jensen/")) or n in {f"{l}.py" for l in LABS} for n in names)


@pytest.mark.parametrize("path", engine_files(CORE_DIR), ids=lambda p: p.relative_to(CORE_DIR).as_posix())
def test_engine_file_imports_no_lab(path):
    assert lab_imports(path) == [], f"{path.relative_to(CORE_DIR)} imports a lab: {lab_imports(path)}"


def test_checker_flags_function_level_lab_import(tmp_path):
    f = tmp_path / "m.py"
    f.write_text("def g():\n    from .rh_jensen.jensen import x\n")
    assert lab_imports(f) == [(2, "from .rh_jensen.jensen import ...")]


def test_checker_flags_from_dot_import_lab(tmp_path):
    f = tmp_path / "m.py"
    f.write_text("from . import li_coeff\nimport telperion.weil_form_eval\nfrom telperion import bg\n")
    assert [ln for ln, _ in lab_imports(f)] == [1, 2, 3]


def test_checker_ignores_lookalike_names(tmp_path):
    f = tmp_path / "m.py"
    f.write_text("from .bg_util import x\nfrom .bgx import y\nimport telperion.bragg_coeff\n")
    assert lab_imports(f) == []


def test_importing_engine_loads_no_lab_module():
    code = ("import sys, telperion; "
            f"labs = {tuple('telperion.' + l for l in LABS)!r}; "
            "print([m for m in sys.modules if m.startswith(labs)])")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True,
                         env={**os.environ, "PYTHONPATH": str(SRC)}, check=True).stdout.strip()
    assert out == "[]"
```
`test_checker_ignores_lookalike_names` needs matching by whole dotted component, not by prefix: `bg_util` is not the lab
`bg`.

- [ ] **Step 2: Run them to verify they fail**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_core_boundary.py -q -p no:cacheprovider`
Expected: FAIL at the import (`No module named 'telperion.boundary'`).

- [ ] **Step 3: Implement `telperion/src/telperion/boundary.py`**

```python
"""The engine/lab boundary: no engine module imports a lab (spec section 3; enforced in CI).

Labs are research packages that USE the engine. They move out of the standalone Telperion repo,
so the engine must never import them -- statically (any spelling, any nesting) or at runtime.
"""
from __future__ import annotations

import ast
from pathlib import Path
from typing import List, Tuple

LABS: Tuple[str, ...] = ("bg", "rh_jensen", "bg_upper_bound", "bg_bulk_discharge",
                         "li_coeff", "weil_form_eval")


def _is_lab_path(rel_parts: Tuple[str, ...]) -> bool:
    first = rel_parts[0]
    return first in LABS or (len(rel_parts) == 1 and first[:-3] in LABS)


def engine_files(src_pkg: Path) -> List[Path]:
    """Every .py under src/telperion except lab packages/modules (subpackages included)."""
    out = []
    for p in sorted(src_pkg.rglob("*.py")):
        rel = p.relative_to(src_pkg).parts
        if "__pycache__" in rel or _is_lab_path(rel):
            continue
        out.append(p)
    return out


def _names_lab(dotted: str) -> bool:
    parts = dotted.split(".")
    if parts and parts[0] == "telperion":
        parts = parts[1:]
    return bool(parts) and parts[0] in LABS


def lab_imports(path: Path) -> List[Tuple[int, str]]:
    tree = ast.parse(path.read_text(), filename=str(path))
    hits: List[Tuple[int, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if node.level and mod and _names_lab(mod):
                hits.append((node.lineno, f"from {'.' * node.level}{mod} import ..."))
            elif not node.level and _names_lab(mod) and mod.startswith("telperion."):
                hits.append((node.lineno, f"from {mod} import ..."))
            elif (node.level and not mod) or mod == "telperion":
                for a in node.names:
                    if a.name in LABS:
                        hits.append((node.lineno, f"from {'.' * node.level}{mod} import {a.name}"))
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name.startswith("telperion.") and _names_lab(a.name):
                    hits.append((node.lineno, f"import {a.name}"))
    return sorted(hits)
```
Make the expected strings in `test_checker_flags_function_level_lab_import` match exactly what this produces. If you change
the spelling format, change the test and the code together, never the test alone.

- [ ] **Step 4: Run the tests**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_core_boundary.py tests/test_arb_helper_equivalence.py tests/test_jensen_margin.py -q -p no:cacheprovider`
Expected: all pass. If `test_engine_file_imports_no_lab` fails for a file Tasks 1 and 2 did not cover, STOP and report it as
DONE_WITH_CONCERNS with the file and line. Do not silently add it to LABS.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/src/telperion/boundary.py telperion/tests/test_core_boundary.py
sudo -u peterwmurphy git commit -m "telperion: engine/lab boundary for every lab (static AST + runtime), not just bg

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: The lab manifest that step 2 consumes

**Files:**
- Create: `telperion/scripts/lab_manifest.py`
- Create (generated, committed): `telperion/docs/extraction/LAB_MANIFEST.json`
- Test: `telperion/tests/test_lab_manifest.py`

**Interfaces:**
- Consumes: `telperion.boundary.LABS`, `engine_files`, `lab_imports`.
- Produces: `build_manifest(telperion_root: Path) -> dict`, with these keys:
  - `"labs"`: `{lab: [source paths relative to telperion/]}`;
  - `"lab_tests"`: a sorted list of test paths that reference any lab by import or by the literal string `"telperion.<lab>"`,
    plus everything under `tests/rh_jensen/`;
  - `"engine_tests"`: every other `tests/**/test_*.py`;
  - `"mission_data"`: `{"stays_in_engine": [...], "moves": [...]}`. The moving campaigns are `missions/rh`,
    `missions/mirrormere`, `missions/anduril` and `missions/bg`. `missions/judge` stays (it is the framework's bundle
    directory). Any other `missions/*` directory is listed under `"unclassified"`.
  - `"generated_from"`: the git HEAD sha.

  CLI: `python scripts/lab_manifest.py --write` writes the JSON, and `--check` exits 1 if the committed JSON differs from a
  fresh build. `generated_from` is ignored in that comparison.

- [ ] **Step 1: Write the failing tests**

```python
# telperion/tests/test_lab_manifest.py
import json, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from lab_manifest import build_manifest  # noqa: E402


def test_manifest_partitions_tests():
    m = build_manifest(ROOT)
    every = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "tests").rglob("test_*.py"))
    assert sorted(m["lab_tests"] + m["engine_tests"]) == every
    assert not set(m["lab_tests"]) & set(m["engine_tests"])
    assert any(t.startswith("tests/rh_jensen/") for t in m["lab_tests"])


def test_manifest_catches_string_reference(tmp_path):
    t = tmp_path / "tests"
    t.mkdir()
    (t / "test_x.py").write_text('import importlib\nm = importlib.import_module("telperion.li_coeff")\n')
    (t / "test_y.py").write_text("def test_ok():\n    assert 1\n")
    (tmp_path / "src" / "telperion").mkdir(parents=True)
    (tmp_path / "missions").mkdir()
    m = build_manifest(tmp_path)
    assert m["lab_tests"] == ["tests/test_x.py"] and m["engine_tests"] == ["tests/test_y.py"]


def test_manifest_mission_data():
    m = build_manifest(ROOT)["mission_data"]
    assert set(m["moves"]) == {"missions/rh", "missions/mirrormere", "missions/anduril", "missions/bg"}
    assert "missions/judge" in m["stays_in_engine"]


def test_committed_manifest_is_current():
    r = subprocess.run([sys.executable, str(ROOT / "scripts/lab_manifest.py"), "--check"], cwd=ROOT,
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_lab_manifest.py -q -p no:cacheprovider`
Expected: FAIL with `ModuleNotFoundError: lab_manifest`.

- [ ] **Step 3: Implement `telperion/scripts/lab_manifest.py`**

```python
#!/usr/bin/env python3
"""Write/check docs/extraction/LAB_MANIFEST.json: what is lab material vs engine (step 1 -> step 2)."""
from __future__ import annotations

import argparse, json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from telperion.boundary import LABS, lab_imports  # noqa: E402

MOVING_CAMPAIGNS = ("missions/rh", "missions/mirrormere", "missions/anduril", "missions/bg")
OUT = Path("docs/extraction/LAB_MANIFEST.json")
_STRING_REF = re.compile(r"""["']telperion\.(%s)\b""" % "|".join(LABS))


def _is_lab_test(p: Path, root: Path) -> bool:
    rel = p.relative_to(root).as_posix()
    if rel.startswith("tests/rh_jensen/"):
        return True
    text = p.read_text(errors="replace")
    if _STRING_REF.search(text):
        return True
    try:
        if lab_imports(p):
            return True
    except SyntaxError:
        return False
    # test files import labs absolutely, e.g. `from telperion.rh_jensen.x import y`
    return bool(re.search(r"^\s*(from|import)\s+telperion\.(%s)\b" % "|".join(LABS), text, re.M))


def build_manifest(root: Path) -> dict:
    src = root / "src" / "telperion"
    labs = {}
    for lab in LABS:
        if (src / lab).is_dir():
            labs[lab] = sorted(p.relative_to(root).as_posix() for p in (src / lab).rglob("*.py")
                               if "__pycache__" not in p.parts)
        elif (src / f"{lab}.py").exists():
            labs[lab] = [f"src/telperion/{lab}.py"]
    tests = sorted((root / "tests").rglob("test_*.py")) if (root / "tests").exists() else []
    lab_tests = [p.relative_to(root).as_posix() for p in tests if _is_lab_test(p, root)]
    engine_tests = [p.relative_to(root).as_posix() for p in tests
                    if p.relative_to(root).as_posix() not in lab_tests]
    missions = sorted(d.relative_to(root).as_posix() for d in (root / "missions").iterdir()
                      if d.is_dir()) if (root / "missions").exists() else []
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True,
                          text=True).stdout.strip()
    return {
        "labs": labs,
        "lab_tests": lab_tests,
        "engine_tests": engine_tests,
        "mission_data": {
            "moves": [m for m in missions if m in MOVING_CAMPAIGNS],
            "stays_in_engine": [m for m in missions if m == "missions/judge"],
            "unclassified": [m for m in missions if m not in MOVING_CAMPAIGNS and m != "missions/judge"],
        },
        "generated_from": head,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    a = ap.parse_args()
    fresh = build_manifest(ROOT)
    path = ROOT / OUT
    if a.write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(fresh, indent=2, sort_keys=True) + "\n")
        print(f"wrote {OUT}: {len(fresh['lab_tests'])} lab tests, {len(fresh['engine_tests'])} engine tests")
        return 0
    old = json.loads(path.read_text()) if path.exists() else {}
    strip = lambda d: {k: v for k, v in d.items() if k != "generated_from"}
    if strip(old) != strip(fresh):
        print(f"{OUT} is stale: run scripts/lab_manifest.py --write", file=sys.stderr)
        return 1
    print(f"{OUT} is current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 4: Generate the manifest, then run the tests**

Run:
```bash
cd telperion && PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 scripts/lab_manifest.py --write
PYTHONPATH=src /opt/homebrew/opt/python@3.14/bin/python3.14 -m pytest tests/test_lab_manifest.py tests/test_core_boundary.py -q -p no:cacheprovider
```
Expected: the write line reports about 41 or more lab tests (the controller's 2026-10-27 scan found 41 top-level test files
referencing a lab, plus `tests/rh_jensen/`). The tests pass. Report the `"unclassified"` mission directories. The owner
decides those at step 2 review. Do not guess.

- [ ] **Step 5: Commit**

```bash
sudo -u peterwmurphy git add telperion/scripts/lab_manifest.py telperion/docs/extraction/LAB_MANIFEST.json telperion/tests/test_lab_manifest.py
sudo -u peterwmurphy git commit -m "telperion: lab manifest (sources, tests, mission data) for the standalone extraction

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```
