"""``python -m telperion`` must run the CLI (src/telperion/__main__.py mirrors the
``telperion`` console script in pyproject.toml's [project.scripts])."""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_module_help_exits_zero():
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT / "src")
    proc = subprocess.run(
        [sys.executable, "-m", "telperion", "--help"],
        capture_output=True, text=True, timeout=60, env=env)
    assert proc.returncode == 0, (
        f"python -m telperion --help failed (exit {proc.returncode}):\n"
        f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
