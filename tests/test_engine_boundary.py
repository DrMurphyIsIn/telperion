"""The engine/lab boundary, for every lab (not just bg): no engine module may import a
research lab -- statically (any spelling, any nesting) or at runtime.

Split out of tests/test_core_boundary.py in the step-1 lab-manifest fix round. That file
keeps the BG-specific tests, which genuinely `import telperion.bg` to verify the bg
namespace is a superset of the engine -- a real lab import, so the manifest correctly
classifies test_core_boundary.py as lab material. This file imports no lab anywhere (it
only checks, via AST, that OTHER files don't), so the manifest classifies it as engine,
which is what lets step 2 keep running the engine's own boundary tests after the labs are
cut out.
"""
import os
import subprocess
import sys
from pathlib import Path

import pytest

from telperion.boundary import LABS, engine_files, lab_imports

SRC = Path(__file__).resolve().parents[1] / "src"
CORE_DIR = SRC / "telperion"


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
