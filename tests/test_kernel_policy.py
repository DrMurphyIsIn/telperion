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
