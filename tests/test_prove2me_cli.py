"""CLI wiring: p2m subcommands parse and dispatch; no network in tests."""
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.cli import main  # noqa: E402


def test_p2m_coverage_runs_offline(capsys):
    assert main(["p2m", "coverage"]) == 0
    out = capsys.readouterr().out
    assert "unmatched_registry_classes" in out


def test_p2m_status_empty_ledger(tmp_path, capsys):
    assert main(["p2m", "status", "--workspace", str(tmp_path)]) == 0
    assert "attempts: 0" in capsys.readouterr().out


def test_p2m_lift_scaffolds_from_args(tmp_path, capsys):
    rc = main(["p2m", "lift", "mile9", "--statement",
               "theorem solution : (1 : ℚ) = 1",
               "--name", "M9", "--workspace", str(tmp_path)])
    assert rc == 0
    fam = tmp_path / "attempts" / "M9" / "family.py"
    assert fam.exists() and "mile9" in fam.read_text()


# Minimal valid family.py for the dry-run e2e test.
# Uses a trivial x >= 0 target (certifiable) so certify()+emit() succeed.
# The FORMAL_STATEMENT is a distinct statement not present in the emitted
# Lean, so run_attempt hits the I3 "theorem solution" check and returns
# CertifyRefused — no lake, no network.
_MINIMAL_FAMILY_PY = '''\
import sympy as sp
from telperion import GridSpec, InequalityFamily
from telperion.workflow import ValidationReport

MILESTONE_ID = "mile9"
FORMAL_STATEMENT = "theorem solution : (1 : \\u211a) = 1"


def family() -> InequalityFamily:
    x = sp.Symbol("x", nonnegative=True)
    return InequalityFamily(
        name="M9",
        symbols=(x,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "solution",
        target=lambda pt: x,
    )


def validation() -> ValidationReport:
    return ValidationReport.from_asserts([("trivial", lambda: None)])
'''


def test_p2m_attempt_dry_run_certify_refused(tmp_path, capsys):
    """End-to-end: importlib load -> certify -> emit -> fallback QueueItem ->
    run_attempt returns CertifyRefused (I3: no 'theorem solution' in emitted
    Lean for a trivial x >= 0 family) — zero network, zero lake."""
    # Write the lift family directly (bypasses scaffold stub complexities).
    attempt_dir = tmp_path / "attempts" / "M9"
    attempt_dir.mkdir(parents=True)
    (attempt_dir / "family.py").write_text(_MINIMAL_FAMILY_PY)

    rc = main(["p2m", "attempt", "mile9", "--name", "M9",
               "--no-submit", "--workspace", str(tmp_path)])

    # CertifyRefused is not a success verdict -> exit 1
    assert rc == 1
    out = capsys.readouterr().out
    assert "CertifyRefused" in out

    # Ledger must record the CertifyRefused entry
    ledger_path = tmp_path / "telperion_ledger.jsonl"
    assert ledger_path.exists(), "ledger was not written"
    import json
    records = [json.loads(ln) for ln in ledger_path.read_text().splitlines() if ln.strip()]
    assert records, "ledger is empty"
    assert records[-1]["verdict"] == "CertifyRefused"
    assert records[-1]["milestone_id"] == "mile9"


# --- F8: lift overwrites are caught by CLI ---

def test_p2m_lift_returns_1_on_overwrite(tmp_path, capsys):
    """A second `p2m lift` for the same name returns exit 1 and prints the error."""
    rc = main(["p2m", "lift", "mile9", "--statement",
               "theorem solution : (1 : ℚ) = 1",
               "--name", "M9", "--workspace", str(tmp_path)])
    assert rc == 0
    rc2 = main(["p2m", "lift", "mile9", "--statement",
                "theorem solution : (1 : ℚ) = 1",
                "--name", "M9", "--workspace", str(tmp_path)])
    assert rc2 == 1
    out = capsys.readouterr().out
    assert "already exists" in out


# --- F6b: lake_build runs cache get then build ---

def test_lake_build_runs_cache_get_then_build(tmp_path):
    """lake_build issues `lake exe cache get` before `lake build`."""
    from telperion.prove2me.attempt import lake_build, BuildFailed
    calls = []

    def fake_runner(cmd, **kw):
        calls.append(list(cmd))
        class R:
            returncode = 0
            stdout = b""
            stderr = b""
        return R()

    lake_build(tmp_path, runner=fake_runner)
    assert len(calls) == 2
    assert calls[0] == ["lake", "exe", "cache", "get"]
    assert calls[1] == ["lake", "build"]


def test_lake_build_raises_build_failed_on_timeout(tmp_path):
    """TimeoutExpired from either lake call is wrapped as BuildFailed."""
    from telperion.prove2me.attempt import lake_build, BuildFailed

    def fake_runner_timeout(cmd, **kw):
        raise subprocess.TimeoutExpired(cmd, 3600)

    with pytest.raises(BuildFailed, match="timed out"):
        lake_build(tmp_path, runner=fake_runner_timeout)


# --- F6c: p2m sync subcommand calls git clone ---

def test_p2m_sync_calls_git_clone(tmp_path, monkeypatch):
    """p2m sync <url> clones the repo via subprocess.run."""
    git_calls = []

    def fake_run(cmd, **kw):
        git_calls.append(list(cmd))
        # Simulate a fresh clone: create .git directory so ensure_layout doesn't re-clone
        if cmd[:2] == ["git", "clone"]:
            target = Path(cmd[-1])
            target.mkdir(parents=True, exist_ok=True)
            (target / ".git").mkdir(exist_ok=True)

    monkeypatch.setattr("telperion.prove2me.workspace.subprocess.run", fake_run)
    ws_root = tmp_path / "mywsp"
    rc = main(["p2m", "sync", "https://example.com/prove2me.git",
               "--workspace", str(ws_root)])
    assert rc == 0
    clone_calls = [c for c in git_calls if c[:2] == ["git", "clone"]]
    assert clone_calls, "git clone should have been invoked"
    assert "https://example.com/prove2me.git" in clone_calls[0]


# --- F5: PROOF_BODY composition in attempt ---

# Family with PROOF_BODY defined; FORMAL_STATEMENT matches what the composed
# submission will contain verbatim. lake_build is monkeypatched green;
# run_attempt short-circuits at I3 (no 'theorem solution' in raw emitted Lean)
# unless PROOF_BODY composition adds it.  We test the CLI path by providing a
# family that has PROOF_BODY and checking the ledger reflects it reached
# further than CertifyRefused (DryRun, since --no-submit is set and lake is
# mocked green).
_FAMILY_WITH_PROOF_BODY = '''\
import sympy as sp
from telperion import GridSpec, InequalityFamily
from telperion.workflow import ValidationReport

MILESTONE_ID = "mile9"
FORMAL_STATEMENT = "theorem solution : (1 : \\u211a) + 1 = 2"
PROOF_BODY = "by norm_num"


def family() -> InequalityFamily:
    x = sp.Symbol("x", nonnegative=True)
    return InequalityFamily(
        name="M9pb",
        symbols=(x,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "solution",
        target=lambda pt: x,
    )


def validation() -> ValidationReport:
    return ValidationReport.from_asserts([("trivial", lambda: None)])
'''


def test_p2m_attempt_proof_body_composition_reaches_dry_run(tmp_path, monkeypatch, capsys):
    """When PROOF_BODY is defined, composed lean_source contains FORMAL_STATEMENT
    verbatim -> I3 passes -> DryRun (lake mocked green, --no-submit)."""
    attempt_dir = tmp_path / "attempts" / "M9pb"
    attempt_dir.mkdir(parents=True)
    (attempt_dir / "family.py").write_text(_FAMILY_WITH_PROOF_BODY)

    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)

    rc = main(["p2m", "attempt", "mile9", "--name", "M9pb",
               "--no-submit", "--workspace", str(tmp_path)])

    out = capsys.readouterr().out
    # DryRun -> exit 0
    assert rc == 0, f"expected DryRun (exit 0) but got rc={rc}; output: {out}"
    assert "DryRun" in out

    import json
    ledger_path = tmp_path / "telperion_ledger.jsonl"
    records = [json.loads(ln) for ln in ledger_path.read_text().splitlines() if ln.strip()]
    assert records[-1]["verdict"] == "DryRun"
