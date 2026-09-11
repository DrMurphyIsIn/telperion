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
