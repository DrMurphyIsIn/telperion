"""CLI wiring: p2m subcommands parse and dispatch; no network in tests."""
import sys
from pathlib import Path

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
