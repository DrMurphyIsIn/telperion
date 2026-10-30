import argparse
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


# --- Fix round 1 ---------------------------------------------------------

def test_missing_toolchain_file_is_a_problem_not_a_crash(tmp_path):
    root = _repo(tmp_path, {"old": "leanprover/lean4:v4.32.0"})
    (root / "old" / "lean-toolchain").unlink()
    # find_projects must not crash
    kp.find_projects(root)
    probs = kp.policy_problems(root, {})
    assert any("old" in p and "lean-toolchain is tracked but missing on disk" in p for p in probs)


def test_cli_exit_1_on_missing_toolchain_file(tmp_path):
    import sys
    root = _repo(tmp_path, {"old": "leanprover/lean4:v4.32.0"})
    (root / "old" / "lean-toolchain").unlink()
    cmd = [sys.executable, "-m", "telperion.cli", "kernel-policy", "check", "--root", str(root)]
    env = {**__import__("os").environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1] / "src")}
    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    assert result.returncode == 1
    assert "missing on disk" in result.stdout


def test_load_exceptions_missing_key_raises(tmp_path):
    p = tmp_path / "e.toml"
    p.write_text('[[exception]]\ntoolchain = "leanprover/lean4:v4.32.0"\nreason = "x"\n')
    with pytest.raises(ValueError, match="missing 'project'"):
        kp.load_exceptions(p)


def test_load_exceptions_duplicate_project_raises(tmp_path):
    p = tmp_path / "e.toml"
    p.write_text(
        '[[exception]]\nproject = "a"\ntoolchain = "leanprover/lean4:v4.32.0"\nreason = "x"\n'
        '[[exception]]\nproject = "a"\ntoolchain = "leanprover/lean4:v4.32.0"\nreason = "y"\n'
    )
    with pytest.raises(ValueError, match="duplicate project 'a'"):
        kp.load_exceptions(p)


def test_load_exceptions_bad_toml_raises(tmp_path):
    p = tmp_path / "e.toml"
    p.write_text("not [ valid toml =")
    with pytest.raises(ValueError, match="not valid TOML"):
        kp.load_exceptions(p)


def test_cli_exit_1_on_malformed_exceptions_file(tmp_path):
    import sys
    root = _repo(tmp_path, {"old": "leanprover/lean4:v4.32.0"})
    (root / "kernel_policy_exceptions.toml").write_text(
        '[[exception]]\ntoolchain = "leanprover/lean4:v4.32.0"\nreason = "x"\n')
    cmd = [sys.executable, "-m", "telperion.cli", "kernel-policy", "check", "--root", str(root)]
    env = {**__import__("os").environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1] / "src")}
    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    assert result.returncode == 1
    assert "missing 'project'" in result.stdout


def test_cli_check_calls_find_projects_once_on_ok_path(tmp_path, monkeypatch):
    from telperion import cli
    root = _repo(tmp_path, {"new": "leanprover/lean4:v4.35.0"})
    calls = {"n": 0}
    orig = kp.find_projects

    def counting(r):
        calls["n"] += 1
        return orig(r)

    monkeypatch.setattr(kp, "find_projects", counting)
    args = argparse.Namespace(root=str(root), exceptions=None)
    rc = cli.cmd_kernel_policy_check(args)
    assert rc == 0
    assert calls["n"] == 1


# --- shrink-only enforcement (Task 0) ------------------------------------

_OLD = "leanprover/lean4:v4.32.0"
_NEW = "leanprover/lean4:v4.35.0"


def _exceptions_text(entries: dict[str, str]) -> str:
    return "".join(
        f'[[exception]]\nproject = "{proj}"\ntoolchain = "{tc}"\nreason = "x"\n'
        for proj, tc in entries.items()
    )


def test_shrink_added_entry_fails():
    base = _exceptions_text({"old": _OLD})
    current = {"old": {"toolchain": _OLD, "reason": "x"}, "new": {"toolchain": _OLD, "reason": "x"}}
    probs = kp.shrink_problems(base, current)
    assert any("exception added: new" in p for p in probs)
    assert not any("old" in p for p in probs)


def test_shrink_lowered_toolchain_fails():
    base = _exceptions_text({"p": _NEW})
    current = {"p": {"toolchain": _OLD, "reason": "x"}}
    probs = kp.shrink_problems(base, current)
    assert any("exception toolchain lowered: p" in p for p in probs)


def test_shrink_removed_entry_passes():
    base = _exceptions_text({"p": _OLD, "q": _OLD})
    current = {"p": {"toolchain": _OLD, "reason": "x"}}
    assert kp.shrink_problems(base, current) == []


def test_shrink_raised_toolchain_passes():
    base = _exceptions_text({"p": _OLD})
    current = {"p": {"toolchain": _NEW, "reason": "x"}}
    assert kp.shrink_problems(base, current) == []


def test_shrink_base_none_treats_every_entry_as_added():
    current = {"p": {"toolchain": _OLD, "reason": "x"}, "q": {"toolchain": _NEW, "reason": "x"}}
    probs = kp.shrink_problems(None, current)
    assert any("exception added: p" in p for p in probs)
    assert any("exception added: q" in p for p in probs)
    assert len(probs) == 2


def test_cli_base_head_catches_added_exception(tmp_path):
    import os
    import sys

    root = _repo(tmp_path, {"old": _OLD})
    (root / "kernel_policy_exceptions.toml").write_text(_exceptions_text({"old": _OLD}))
    subprocess.run(["git", "-C", str(root), "add", "-A"], check=True)
    subprocess.run(["git", "-C", str(root), "-c", "user.email=t@t", "-c", "user.name=t",
                    "commit", "-q", "-m", "base"], check=True)
    (root / "new").mkdir()
    (root / "new" / "lean-toolchain").write_text(_OLD + "\n")
    (root / "kernel_policy_exceptions.toml").write_text(_exceptions_text({"old": _OLD, "new": _OLD}))
    subprocess.run(["git", "-C", str(root), "add", "-A"], check=True)

    cmd = [sys.executable, "-m", "telperion.cli", "kernel-policy", "check",
           "--root", str(root), "--base", "HEAD"]
    env = {**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1] / "src")}
    result = subprocess.run(cmd, env=env, capture_output=True, text=True)
    assert result.returncode == 1
    assert "exception added: new" in result.stdout


from telperion.checks.kernel_policy import judge_config_problems


def test_extra_axiom_rejected():
    cfg = {"permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"], "enable_nanoda": True}
    assert any("sorryAx" in p for p in judge_config_problems(cfg, node_heavy=False))


def test_nanoda_off_only_for_heavy():
    cfg = {"permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": False}
    assert judge_config_problems(cfg, node_heavy=True) == []
    assert any("nanoda" in p for p in judge_config_problems(cfg, node_heavy=False))


def test_build_bundle_rejects_nanoda_off_for_non_heavy(monkeypatch, tmp_path):
    import sys
    import telperion.missions.judge as judge
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from test_missions_judge import ARTIFACT_NS, STATEMENT_NS, _island
    real = judge.challenge_config if hasattr(judge, "challenge_config") else None
    assert real is not None, "judge.challenge_config is the config factory the bundle uses"

    def off(*a, **k):
        k["enable_nanoda"] = False
        return real(*a, **k)

    tel = _island(tmp_path, artifact=ARTIFACT_NS, statement=STATEMENT_NS)
    monkeypatch.setattr(judge, "challenge_config", off)
    with pytest.raises(judge.JudgeError, match="nanoda"):
        judge.build_bundle(tel, "isl", only=None)
