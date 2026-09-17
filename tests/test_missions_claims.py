"""Claims: TTL, claim/release, claim-over, load fresh claims."""
import shutil
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.schema import ClaimError  # noqa: E402
from telperion.missions.claims import (  # noqa: E402
    claim, release, is_stale, load_claims, load_fresh_claims,
)
from telperion.missions.registry import load_campaign  # noqa: E402

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def copy_demo(tmp_path: Path) -> Path:
    """Copy the demo fixture into tmp_path and return the campaign root."""
    dest = tmp_path / "demo"
    shutil.copytree(DEMO_FIXTURE, dest)
    return dest


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_claim_writes_fresh_claim_file(tmp_path):
    """claim() writes a fresh claim to <root>/claims/<slug>.toml."""
    root = copy_demo(tmp_path)
    now = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)

    claimed = claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, note="Testing", _now=now)

    assert claimed.node == "Demo.lemma_a"  # Full node name stored in claim
    assert claimed.session == "session_1"
    assert claimed.ttl_hours == 24
    assert claimed.note == "Testing"
    assert claimed.superseded == ""

    # Verify file was written (keyed by slug)
    claim_file = root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()


def test_claim_rejects_fresh_claim_by_another_session(tmp_path):
    """claim() raises ClaimError if another session holds a fresh claim."""
    root = copy_demo(tmp_path)
    now = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)

    # Session 1 claims the node
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now)

    # Session 2 tries to claim the same node -> ClaimError
    with pytest.raises(ClaimError):
        claim(root, "Demo_lemma_a", "session_2", ttl_hours=24, _now=now)


def test_claim_rejects_unclaimed_open_node(tmp_path):
    """claim() raises ClaimError if node is not open."""
    root = copy_demo(tmp_path)
    now = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)

    # Demo_goal is draft (not open)
    with pytest.raises(ClaimError):
        claim(root, "Demo_goal", "session_1", ttl_hours=24, _now=now)


def test_claim_over_stale_claim_records_superseded(tmp_path):
    """claim() over a stale claim (age >= ttl) records superseded and writes new file."""
    root = copy_demo(tmp_path)
    now_t0 = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)
    now_t1 = now_t0 + timedelta(hours=25)  # 25 hours later

    # Session 1 claims at t0 with ttl=24h
    claim1 = claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)

    # At t1, session 2 claims the same node (first claim is now stale)
    claim2 = claim(root, "Demo_lemma_a", "session_2", ttl_hours=24, _now=now_t1)

    # New claim must record the old session in superseded
    assert claim2.superseded == "session_1"
    assert claim2.session == "session_2"

    # Verify file was overwritten with new claim
    claim_file = root / "claims" / "Demo_lemma_a.toml"
    from telperion.missions.schema import load_claim
    reloaded = load_claim(claim_file)
    assert reloaded.session == "session_2"
    assert reloaded.superseded == "session_1"


def test_release_by_owner_deletes_file(tmp_path):
    """release() by the claiming session removes the claim file."""
    root = copy_demo(tmp_path)
    now = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)

    # Session 1 claims
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now)
    claim_file = root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()

    # Session 1 releases
    release(root, "Demo_lemma_a", "session_1")
    assert not claim_file.exists()


def test_release_by_stranger_raises_claimerror(tmp_path):
    """release() by a different session raises ClaimError."""
    root = copy_demo(tmp_path)
    now = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)

    # Session 1 claims
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now)

    # Session 2 tries to release -> ClaimError
    with pytest.raises(ClaimError):
        release(root, "Demo_lemma_a", "session_2")


def test_load_fresh_claims_filters_stale(tmp_path):
    """load_fresh_claims() returns only fresh claims, filtering out stale ones."""
    root = copy_demo(tmp_path)
    now_t0 = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)
    now_t0_b = now_t0 + timedelta(seconds=1)  # Slight offset for second claim
    now_t1 = now_t0 + timedelta(hours=25)  # 25 hours later (past ttl=24h)

    # Create a fresh claim at t0
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)

    # Manually add another claim file with a different timestamp
    # (We can't use another demo node because only Demo_lemma_a is open)
    # Release the first claim and create two with different times
    release(root, "Demo_lemma_a", "session_1")

    # Create first claim with 24h TTL at t0
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)

    # At t0, claim is fresh
    fresh_t0 = load_fresh_claims(root, _now=now_t0)
    assert len(fresh_t0) == 1
    assert "Demo_lemma_a" in fresh_t0

    # At t1 (25h later), claim is stale
    fresh_t1 = load_fresh_claims(root, _now=now_t1)
    assert len(fresh_t1) == 0
    assert "Demo_lemma_a" not in fresh_t1


def test_is_stale_boundary_at_ttl(tmp_path):
    """is_stale() treats age == ttl as stale (not fresh)."""
    root = copy_demo(tmp_path)
    now_t0 = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)
    now_t1 = now_t0 + timedelta(hours=24)  # Exactly at ttl boundary

    claim_obj = claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)

    # At t0 + 24h, the claim should be considered stale
    assert is_stale(claim_obj, _now=now_t1) is True

    # One second before the boundary, it should be fresh
    now_t1_minus_1s = now_t1 - timedelta(seconds=1)
    assert is_stale(claim_obj, _now=now_t1_minus_1s) is False


def test_release_after_claimover_by_new_holder(tmp_path):
    """After claim-over, only the new holder can release the claim."""
    root = copy_demo(tmp_path)
    now_t0 = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)
    now_t1 = now_t0 + timedelta(hours=25)  # Stale

    # Session 1 claims at t0
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)
    claim_file = root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()

    # Session 2 claims-over at t1 (claim 1 is now stale)
    claim2 = claim(root, "Demo_lemma_a", "session_2", ttl_hours=24, _now=now_t1)
    assert claim2.superseded == "session_1"

    # Session 2 (new holder) can release
    release(root, "Demo_lemma_a", "session_2")
    assert not claim_file.exists()


def test_release_after_claimover_by_displaced_raises(tmp_path):
    """After claim-over, the displaced session cannot release."""
    root = copy_demo(tmp_path)
    now_t0 = datetime(2026, 9, 11, 12, 0, 0, tzinfo=timezone.utc)
    now_t1 = now_t0 + timedelta(hours=25)  # Stale

    # Session 1 claims at t0
    claim(root, "Demo_lemma_a", "session_1", ttl_hours=24, _now=now_t0)

    # Session 2 claims-over at t1
    claim(root, "Demo_lemma_a", "session_2", ttl_hours=24, _now=now_t1)

    # Session 1 (displaced) tries to release -> ClaimError
    with pytest.raises(ClaimError):
        release(root, "Demo_lemma_a", "session_1")
