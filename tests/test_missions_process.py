"""Step 5 Task 1: campaign statement freeze (`FREEZE.toml`), `mission freeze`/`unfreeze`,
and the drift check (`freeze_problems`)."""
from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path
from typing import Sequence

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, load_node, save_manifest, save_node,
)
from telperion.missions.statements import statement_body, write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status  # noqa: E402
from telperion.missions.process import (  # noqa: E402
    _dump_freeze, _load_freeze, freeze, freeze_grant_problem, freeze_history_problems,
    freeze_path, freeze_problems, unfreeze,
)
from telperion.cli import main  # noqa: E402


# ---------------------------------------------------------------------------
# git fixture helpers (fix round 1, Controller Ruling 5)
# ---------------------------------------------------------------------------

def _git_init(root: Path) -> None:
    r = subprocess.run(["git", "-C", str(root), "init", "-q"], capture_output=True, text=True)
    assert r.returncode == 0, r.stderr


def _git_commit(root: Path, message: str, *, add: Sequence[str] = (".",)) -> None:
    """Stage and commit under a LOCAL test identity (`-c user.name=...`), never the
    global/system git config."""
    r = subprocess.run(["git", "-C", str(root), "add", *add], capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    r = subprocess.run(
        ["git", "-C", str(root), "-c", "user.name=Test User",
         "-c", "user.email=test@example.com", "commit", "-q", "-m", message],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, r.stderr


def _hand_edit_freeze(root: Path, mutate) -> None:
    """Load FREEZE.toml, let `mutate` change the parsed dict in place, write it back --
    simulates a hand-edit of the record (the same threat model `freeze_problems` and
    `freeze_history_problems` exist to catch)."""
    doc = _load_freeze(root)
    mutate(doc)
    freeze_path(root).write_text(_dump_freeze(doc))


def _campaign(root: Path, names=("Node_A", "Node_B")) -> MissionManifest:
    """A tiny campaign: two draft nodes, each with a statement file written through the
    normal tooling (`statements.write_statement`), and nothing else -- enough for
    freeze/unfreeze/freeze_problems, which only look at statement bodies."""
    manifest = MissionManifest(
        name="Demo.goal", title="Demo Campaign", description="synthetic",
        goal_node=names[0], environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    (root / "nodes").mkdir(parents=True, exist_ok=True)
    save_manifest(manifest, root / "mission.toml")
    for i, name in enumerate(names):
        node = Node(name=name, title=f"title of {name}", kind="lemma", status="draft",
                    depends_on=(), statement_module=f"Statements.{name}")
        save_node(node, root / "nodes" / f"{name}.toml")
        write_statement(root, node, f"theorem thm_{name} : {i} = {i}", manifest)
    return manifest


# ---------------------------------------------------------------------------
# freeze
# ---------------------------------------------------------------------------

def test_freeze_records_hashes(tmp_path):
    # Pre-cutoff `frozen` date: this test is about the hash bookkeeping, not the git-history
    # policy (freeze_history_problems fails closed on a post-cutoff FREEZE.toml with no git
    # repo backing it -- see the dedicated tests below).
    root = tmp_path / "demo"
    _campaign(root)
    doc = freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")

    assert doc["version"] == 1
    assert doc["frozen"] == "2026-10-01"
    assert doc["identity"] == "alice@example.com"
    assert doc["session"] == "s1"
    campaign = load_campaign(root)
    assert set(doc["statements"]) == set(campaign.nodes)
    for slug, node in campaign.nodes.items():
        expected = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
        assert doc["statements"][slug] == expected
    assert freeze_path(root).exists()
    assert freeze_problems(root) == []


def test_freeze_refuses_when_already_frozen(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    with pytest.raises(ValueError, match="already frozen"):
        freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")


def test_freeze_requires_identity_and_session(tmp_path):
    from telperion.missions.provenance import ProvenanceError
    root = tmp_path / "demo"
    _campaign(root)
    with pytest.raises(ProvenanceError):
        freeze(root, identity="", session="s1", date="2026-10-28")
    with pytest.raises(ProvenanceError):
        freeze(root, identity="alice@example.com", session="", date="2026-10-28")


# ---------------------------------------------------------------------------
# drift
# ---------------------------------------------------------------------------

def test_statement_drift_detected(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)

    problems = freeze_problems(root)
    assert any("statement drift" in p and "Node_A" in p for p in problems)


def test_deleted_statement_file_flagged(tmp_path):
    """Fix round 1, finding C2: a node recorded in FREEZE.toml whose statement file has
    since been deleted used to be silently skipped by every check (`if not
    statement_path(...).exists(): continue`) -- exactly the node an attacker would most
    want to erase evidence for."""
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")

    node = load_campaign(root).nodes["Node_A"]
    from telperion.missions.statements import statement_path
    statement_path(root, node).unlink()

    problems = freeze_problems(root)
    assert any("Node_A" in p and "no longer exists" in p for p in problems)


def test_duplicate_unfreeze_entries_with_hidden_self_readback_flagged(tmp_path):
    """Fix round 1, finding I: two [[unfreeze]] entries for the same version used to be
    resolved last-wins, so a forged self-read-back could hide behind a later, clean
    duplicate for the same version."""
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")

    def _rewrite(doc):
        doc["version"] = 2
        doc["unfreeze"] = [
            {"version": 2, "date": "2026-10-29", "author": "alice@example.com",
             "reason": "self-serve", "readback_identity": "alice@example.com"},
            {"version": 2, "date": "2026-10-29", "author": "alice@example.com",
             "reason": "cleaned up", "readback_identity": "bob@example.com"},
        ]

    _hand_edit_freeze(root, _rewrite)

    problems = freeze_problems(root)
    assert any("self-read-back" in p for p in problems)
    assert any("2 [[unfreeze]] entries for version 2" in p for p in problems)


# ---------------------------------------------------------------------------
# unfreeze
# ---------------------------------------------------------------------------

def test_unfreeze_bumps_and_clears_drift(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")  # pre-cutoff

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)
    assert freeze_problems(root) != []

    doc = unfreeze(root, author="alice@example.com", reason="statement revised",
                   readback_identity="bob@example.com", date="2026-10-29")

    assert doc["version"] == 2
    assert doc["unfreeze"] == [{
        "version": 2, "date": "2026-10-29", "author": "alice@example.com",
        "reason": "statement revised", "readback_identity": "bob@example.com",
    }]
    # Re-hashed ALL statements, not only the drifted one.
    campaign = load_campaign(root)
    for slug, node in campaign.nodes.items():
        expected = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
        assert doc["statements"][slug] == expected
    assert freeze_problems(root) == []


def test_unfreeze_without_freeze_fails(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    with pytest.raises(ValueError, match="FREEZE"):
        unfreeze(root, author="alice@example.com", reason="r",
                readback_identity="bob@example.com", date="2026-10-29")


def test_self_readback_rejected(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")  # pre-cutoff

    # Case-folded comparison, same as provenance.independence_of.
    with pytest.raises(ValueError):
        unfreeze(root, author="alice@example.com", reason="whatever",
                readback_identity="Alice@Example.com", date="2026-10-29")
    # Nothing was written on refusal.
    assert freeze_problems(root) == []


def test_rewritten_freeze_without_unfreeze_fails(tmp_path):
    """The brief's literal adversarial scenario: hand-edit FREEZE.toml to `version = 2`
    WITH NEW HASHES (as if the statements had genuinely changed) and no `[[unfreeze]]`
    entry -- a materially stronger case than merely bumping the version string while
    leaving the (still-accurate) hashes alone."""
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")

    def _rewrite(doc):
        doc["version"] = 2
        doc["statements"] = {slug: "f" * 64 for slug in doc["statements"]}

    _hand_edit_freeze(root, _rewrite)

    problems = freeze_problems(root)
    assert any("version 2" in p and "unfreeze" in p for p in problems)


# ---------------------------------------------------------------------------
# freeze_history_problems (fix round 1, Controller Ruling 5)
#
# C1: a statement edited via the normal tool, then FREEZE.toml hand-rewritten to match,
# with `version` left unchanged, defeats every check above (none of them compare against
# anything but the current statement files and the current FREEZE.toml). Only the file's
# git history can catch that.
# ---------------------------------------------------------------------------

def test_freeze_history_hash_rewrite_at_unchanged_version_committed_flagged(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "initial freeze")

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)
    new_hash = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
    _hand_edit_freeze(root, lambda d: d["statements"].__setitem__("Node_A", new_hash))
    _git_commit(root, "rewrite the recorded hash to hide the edit")

    problems = freeze_problems(root)
    assert any("without a version bump" in p for p in problems)


def test_freeze_history_hash_rewrite_at_unchanged_version_uncommitted_flagged(tmp_path):
    """The same tamper as above, left uncommitted: the working tree is itself the final
    state the history walk compares against the last commit, so this is caught the same
    way -- committing is not what makes the drift visible."""
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "initial freeze")

    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, "theorem thm_Node_A : 99 = 99", manifest)
    new_hash = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
    _hand_edit_freeze(root, lambda d: d["statements"].__setitem__("Node_A", new_hash))
    # left uncommitted on purpose

    problems = freeze_problems(root)
    assert any("without a version bump" in p for p in problems)


def test_freeze_history_version_jump_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "initial freeze")

    _hand_edit_freeze(root, lambda d: d.update(version=3))
    _git_commit(root, "jump straight to version 3")

    problems = freeze_problems(root)
    assert any("jumped from 1 to 3" in p for p in problems)


def test_freeze_history_edited_earlier_unfreeze_entry_flagged(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "initial freeze")

    write_statement(root, load_campaign(root).nodes["Node_A"],
                    "theorem thm_Node_A : 99 = 99", manifest)
    unfreeze(root, author="alice@example.com", reason="first revision",
             readback_identity="bob@example.com", date="2026-10-29")
    _git_commit(root, "legitimate unfreeze to v2")

    # Tamper with the ALREADY-COMMITTED v2 entry's reason text; version stays at 2.
    _hand_edit_freeze(root, lambda d: d["unfreeze"][0].__setitem__("reason", "rewritten"))
    _git_commit(root, "quietly edit the v2 unfreeze entry")

    problems = freeze_problems(root)
    assert any("append-only" in p for p in problems)


def test_freeze_history_legitimate_unfreeze_committed_clean(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "initial freeze")

    write_statement(root, load_campaign(root).nodes["Node_A"],
                    "theorem thm_Node_A : 99 = 99", manifest)
    unfreeze(root, author="alice@example.com", reason="statement revised",
             readback_identity="bob@example.com", date="2026-10-29")
    _git_commit(root, "legitimate unfreeze")

    assert freeze_problems(root) == []
    assert freeze_history_problems(root) == []


def test_freeze_history_not_a_git_repo_post_cutoff_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")  # >= CUTOFF

    problems = freeze_problems(root)
    assert any("not inside a git repository" in p for p in problems)


def test_freeze_history_not_a_git_repo_pre_cutoff_ok(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")  # < CUTOFF

    assert freeze_history_problems(root) == []


def test_freeze_history_never_committed_post_cutoff_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")  # >= CUTOFF
    # FREEZE.toml exists on disk but no commit has ever touched it.

    problems = freeze_problems(root)
    assert any("never been committed" in p for p in problems)


# ---------------------------------------------------------------------------
# the grant gate
# ---------------------------------------------------------------------------

def test_post_cutoff_node_needs_freeze_to_grant(tmp_path):
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))  # passing [checks]; freeze is separate

    with pytest.raises(GateError, match="frozen"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"

    assert freeze_grant_problem(root, node) != ""


def test_post_cutoff_grant_refused_by_tampered_freeze_history(tmp_path):
    """Controller Ruling 6 (fix round 2): a post-cutoff node may not be granted while ANY
    `freeze_problems(root)` problem exists -- even one about a DIFFERENT node in the same
    campaign, and even when the node actually being granted has passing checks of its own.
    The reviewer's C1 tamper (a statement edited, FREEZE.toml's recorded hash hand-rewritten
    to match, version left unchanged), committed, on the UNGRANTED node Extra -- the grant
    of Demo_ck, which is otherwise clean, must still be refused."""
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    manifest = load_campaign(root).manifest
    extra = Node(name="Extra", title="an extra node", kind="lemma", status="draft",
                depends_on=(), statement_module="Statements.Extra")
    save_node(extra, root / "nodes" / "Extra.toml")
    write_statement(root, extra, "theorem thm_extra : True", manifest)

    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "initial freeze")

    write_statement(root, load_campaign(root).nodes["Extra"],
                    "theorem thm_extra : False", manifest)
    new_hash = hashlib.sha256(
        statement_body(root, load_campaign(root).nodes["Extra"]).encode("utf-8")
    ).hexdigest()
    _hand_edit_freeze(root, lambda d: d["statements"].__setitem__("Extra", new_hash))
    _git_commit(root, "tamper with Extra's recorded hash to hide the edit")

    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))  # Demo_ck's own checks pass cleanly

    with pytest.raises(GateError, match="freeze") as exc_info:
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert "without a version bump" in str(exc_info.value)
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_post_cutoff_grant_passes_with_clean_committed_freeze(tmp_path):
    """The converse of the tamper test above: a post-cutoff node in a campaign that is
    frozen, committed, and untampered is granted normally."""
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "initial freeze")

    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))

    granted = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"


def test_freeze_problems_clean_for_post_cutoff_committed_freeze(tmp_path):
    """The post-cutoff happy path, pinned: a freeze dated on/after CUTOFF, in a git
    repository, with the freeze itself committed, is clean -- freeze_history_problems'
    fail-closed checks (no git repo / never committed) are about absence of evidence, not
    about a post-cutoff date by itself."""
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")  # >= CUTOFF
    _git_commit(root, "initial freeze")

    assert freeze_problems(root) == []


def test_pre_cutoff_campaign_without_freeze_ok(tmp_path):
    from test_missions_checks import _grant_campaign

    root = _grant_campaign(tmp_path, created="2026-10-01")
    assert not freeze_path(root).exists()
    assert freeze_problems(root) == []

    node = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                        session="gate-session")
    assert node.status == "proved"


def test_open_post_cutoff_node_without_freeze_not_flagged(tmp_path):
    """A draft/open post-cutoff node has not been granted yet, so there is nothing to
    freeze; only a PROVED post-cutoff node makes a missing FREEZE.toml a problem."""
    from test_missions_checks import _grant_campaign

    root = _grant_campaign(tmp_path, created="2026-10-29")
    assert freeze_problems(root) == []


def test_proved_post_cutoff_campaign_with_freeze_removed_flagged(tmp_path):
    """`freeze_grant_problem` already refuses to grant a post-cutoff node without a
    FREEZE.toml recording it; a proved node with none on disk means the record was
    removed after the fact (the hand-edit case `verify_campaign` re-checks)."""
    from test_missions_checks import _art_sha, _grant_campaign, _grant, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    assert _grant(root).status == "proved"
    assert freeze_path(root).exists()

    freeze_path(root).unlink()

    problems = freeze_problems(root)
    assert any("FREEZE.toml" in p and "Demo_ck" in p for p in problems)


# ---------------------------------------------------------------------------
# CUTOFF single source of truth (Controller Ruling 1)
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# CLI: `mission freeze` / `mission unfreeze`
# ---------------------------------------------------------------------------

def test_cli_freeze_then_unfreeze(tmp_path, capsys):
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 0
    assert freeze_path(mroot / "demo").exists()
    # Fix round 1, Ruling 5: the CLI tells the user to commit the freeze (an uncommitted
    # FREEZE.toml has no git history for freeze_history_problems to check).
    assert "commit" in capsys.readouterr().out


    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 1
    assert "already frozen" in capsys.readouterr().out

    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo",
              "--author", "alice@example.com", "--reason", "r",
              "--readback-identity", "alice@example.com"])
    assert rc == 1
    assert "readback_identity" in capsys.readouterr().out

    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo",
              "--author", "alice@example.com", "--reason", "r",
              "--readback-identity", "bob@example.com"])
    assert rc == 0
    doc = _load_freeze_for_test(mroot / "demo")
    assert doc["version"] == 2


def test_cli_freeze_unknown_campaign(tmp_path):
    mroot = tmp_path / "missions"
    mroot.mkdir()
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "nope",
              "--identity", "a@x", "--session", "s1"])
    assert rc == 1


def _load_freeze_for_test(root: Path) -> dict:
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    return tomllib.loads(freeze_path(root).read_text())


def test_cutoff_is_single_source_of_truth():
    from telperion.missions.process import CUTOFF
    from telperion.missions.provenance import CHECKS_CUTOFF

    assert CHECKS_CUTOFF == CUTOFF
    assert CHECKS_CUTOFF is CUTOFF
