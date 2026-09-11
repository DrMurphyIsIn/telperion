"""Append-only jsonl attempt ledger: no-repeat rule + emitter win rates."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.ledger import AttemptLedger, AttemptRecord  # noqa: E402


def rec(milestone="m1", verdict="Proved", emitters=("SOSEmitter",)):
    return AttemptRecord(
        milestone_id=milestone, mission_id="mi1", emitters=tuple(emitters),
        lift_hash="abc123", verdict=verdict, server_output="", wall_s=1.5,
        submission_id="s1", date="2026-09-11",
    )


def test_append_and_reload_roundtrip(tmp_path):
    p = tmp_path / "ledger.jsonl"
    led = AttemptLedger(p)
    led.append(rec())
    led2 = AttemptLedger(p)          # fresh read from disk
    assert led2.records() == [rec()]
    assert led2.attempted("m1") and not led2.attempted("m2")


def test_win_rate_per_emitter(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="Proved"))
    led.append(rec(milestone="m2", verdict="Rejected"))
    led.append(rec(milestone="m3", verdict="Proved", emitters=("WZEmitter",)))
    assert led.win_rate("SOSEmitter") == 0.5
    assert led.win_rate("WZEmitter") == 1.0
    assert led.win_rate("NeverUsedEmitter") is None


def test_rejected_paths_listed_for_no_repeat(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="Rejected"))
    assert [r.verdict for r in led.rejected("m1")] == ["Rejected"]


def test_dry_runs_do_not_count_as_attempted(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="DryRun"))
    assert not led.attempted("m1")
    assert led.win_rate("SOSEmitter") is None
