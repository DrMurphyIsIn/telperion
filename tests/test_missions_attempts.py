"""Attempts ledger: append-only work log with corrupt-line tolerance."""
import sys
from pathlib import Path
from datetime import datetime

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.missions.attempts import Attempt, AttemptLog  # noqa: E402


def test_attempt_frozen_valid_verdict():
    """Attempt is a frozen dataclass with verdict validation."""
    a = Attempt(node="BG.master", session="s1", route="direct",
                verdict="Proved", detail="phi <= 1", date="2026-09-11")
    assert a.node == "BG.master"
    assert a.verdict == "Proved"
    # Frozen: cannot mutate
    with pytest.raises(AttributeError):
        a.node = "other"


def test_attempt_rejects_invalid_verdict():
    """Invalid verdict raises ValueError at construction."""
    with pytest.raises(ValueError, match="verdict.*must be one of"):
        Attempt(node="BG.x", session="s1", route="direct",
                verdict="Invalid", detail="", date="2026-09-11")


def test_roundtrip_via_ledger(tmp_path):
    """AttemptLog round-trips records: append, read back, equality."""
    log_path = tmp_path / "attempts.jsonl"
    log = AttemptLog(log_path)

    # Append two attempts
    a1 = Attempt(node="BG.master", session="s1", route="direct",
                 verdict="Proved", detail="phi <= 1", date="2026-09-11")
    a2 = Attempt(node="BG.sub", session="s2", route="reduction",
                 verdict="Refuted", detail="counterexample: n=3", date="2026-09-11")
    log.append(a1)
    log.append(a2)

    # Fresh log, read back
    log2 = AttemptLog(log_path)
    records = log2.records()
    assert len(records) == 2
    assert records[0] == a1
    assert records[1] == a2


def test_for_node_filter(tmp_path):
    """for_node(slug) returns attempts for that node only."""
    log_path = tmp_path / "attempts.jsonl"
    log = AttemptLog(log_path)

    a1 = Attempt(node="BG.master", session="s1", route="direct",
                 verdict="Proved", detail="phi", date="2026-09-11")
    a2 = Attempt(node="BG.sub", session="s2", route="direct",
                 verdict="NoGo", detail="too hard", date="2026-09-11")
    a3 = Attempt(node="BG.master", session="s3", route="reduction",
                 verdict="Stalled", detail="waiting", date="2026-09-12")

    log.append(a1)
    log.append(a2)
    log.append(a3)

    # Filter by node slug
    master_attempts = log.for_node("BG_master")
    assert len(master_attempts) == 2
    assert all(a.node == "BG.master" for a in master_attempts)
    assert master_attempts[0].verdict == "Proved"
    assert master_attempts[1].verdict == "Stalled"

    sub_attempts = log.for_node("BG_sub")
    assert len(sub_attempts) == 1
    assert sub_attempts[0].verdict == "NoGo"


def test_nogo_digest_excludes_stalled_includes_nogo(tmp_path):
    """nogo_digest(slug) includes NoGo details, excludes Stalled, no duplicates."""
    log_path = tmp_path / "attempts.jsonl"
    log = AttemptLog(log_path)

    a1 = Attempt(node="BG.master", session="s1", route="direct",
                 verdict="NoGo", detail="too hard", date="2026-09-11")
    a2 = Attempt(node="BG.master", session="s2", route="reduction",
                 verdict="NoGo", detail="too hard", date="2026-09-12")
    a3 = Attempt(node="BG.master", session="s3", route="other",
                 verdict="Stalled", detail="waiting for input", date="2026-09-12")

    log.append(a1)
    log.append(a2)
    log.append(a3)

    digest = log.nogo_digest("BG_master")
    # Should include NoGo details, no repeats, exclude Stalled
    assert "too hard" in digest
    assert digest.count("too hard") == 1  # No repeats
    assert "waiting for input" not in digest  # Stalled excluded


def test_truncated_trailing_line_skipped(tmp_path):
    """Truncated JSONL line (incomplete record) is skipped with policy comment."""
    log_path = tmp_path / "attempts.jsonl"

    # Write a valid record + incomplete record
    log_path.write_text(
        '{"node": "BG.master", "session": "s1", "route": "direct", '
        '"verdict": "Proved", "detail": "phi", "date": "2026-09-11"}\n'
        '{"node": "BG.sub", "session": "s2"'  # Incomplete, no closing }
    )

    # Load should skip the broken line and succeed with just the first record
    log = AttemptLog(log_path)
    records = log.records()
    assert len(records) == 1
    assert records[0].node == "BG.master"
