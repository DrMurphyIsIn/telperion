"""Helpers shared by test_nanoda_direct.py (engine) and test_nanoda_direct_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.nanoda_direct import ...` resolves, as `from missions_fixtures import ...` does.
"""
from __future__ import annotations

from pathlib import Path


def _stub_run(export_out="<export bytes>\n", nanoda_out="Checked 3 declarations with no errors\n",
              export_rc=0, nanoda_rc=0, export_err="", nanoda_err=""):
    """Review fix round 1 (2026-10-28), item 5: `run` returns (rc, stdout, stderr) -- stdout
    and stderr separately, so `run_direct` can write stdout-only to `export.txt` while still
    logging stderr (where a real Lean PANIC under LEAN_ABORT_ON_PANIC=1 would land)."""
    calls = []

    def run(cmd, *, cwd):
        calls.append((list(cmd), Path(cwd)))
        if cmd[0] == "lake":
            return export_rc, export_out, export_err
        return nanoda_rc, nanoda_out, nanoda_err
    return run, calls
