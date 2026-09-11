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


# --- F2: SubmittedUnknown and PollTimeout taxonomy ---

def test_submitted_unknown_counts_as_attempted_not_in_win_rate(tmp_path):
    """SubmittedUnknown counts as attempted (no-repeat) but is excluded from
    win_rate denominators — same as DryRun exclusion from win_rate but
    unlike DryRun it DOES count for attempted()."""
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="SubmittedUnknown"))
    assert led.attempted("m1"), "SubmittedUnknown must count as attempted"
    assert led.win_rate("SOSEmitter") is None, \
        "SubmittedUnknown must be excluded from win_rate denominator"


def test_poll_timeout_counts_as_attempted_not_in_win_rate(tmp_path):
    """PollTimeout has the same semantics as SubmittedUnknown."""
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="PollTimeout"))
    assert led.attempted("m1"), "PollTimeout must count as attempted"
    assert led.win_rate("SOSEmitter") is None, \
        "PollTimeout must be excluded from win_rate denominator"


def test_win_rate_excludes_all_unscored_verdicts(tmp_path):
    """win_rate denominator excludes DryRun, SubmittedUnknown, PollTimeout."""
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="Proved"))          # win
    led.append(rec(milestone="m2", verdict="DryRun"))
    led.append(rec(milestone="m3", verdict="SubmittedUnknown"))
    led.append(rec(milestone="m4", verdict="PollTimeout"))
    # Only the Proved record should be in denominator => 1/1 = 1.0
    assert led.win_rate("SOSEmitter") == 1.0


def test_corrupted_trailing_jsonl_line_skipped(tmp_path):
    """Interrupted append (truncated trailing line) is skipped; earlier records survive."""
    p = tmp_path / "ledger.jsonl"
    # Write two valid records and one truncated (interrupted write)
    import json
    from telperion.prove2me.ledger import AttemptRecord
    rec1 = rec(milestone="m1", verdict="Proved")
    rec2 = rec(milestone="m2", verdict="Disproved")
    with p.open("w") as f:
        f.write(json.dumps({
            "milestone_id": rec1.milestone_id,
            "mission_id": rec1.mission_id,
            "emitters": list(rec1.emitters),
            "lift_hash": rec1.lift_hash,
            "verdict": rec1.verdict,
            "server_output": rec1.server_output,
            "wall_s": rec1.wall_s,
            "submission_id": rec1.submission_id,
            "date": rec1.date,
        }) + "\n")
        f.write(json.dumps({
            "milestone_id": rec2.milestone_id,
            "mission_id": rec2.mission_id,
            "emitters": list(rec2.emitters),
            "lift_hash": rec2.lift_hash,
            "verdict": rec2.verdict,
            "server_output": rec2.server_output,
            "wall_s": rec2.wall_s,
            "submission_id": rec2.submission_id,
            "date": rec2.date,
        }) + "\n")
        # Truncated third line (simulating interrupted write)
        f.write('{"milestone_id": "m3", "mis')

    # Load should skip corrupted line and return only 2 valid records
    led = AttemptLedger(p)
    assert len(led.records()) == 2
    assert led.records()[0].milestone_id == "m1"
    assert led.records()[1].milestone_id == "m2"
