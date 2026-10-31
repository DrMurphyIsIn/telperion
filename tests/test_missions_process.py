"""Step 5 Task 1: campaign statement freeze (`FREEZE.toml`), `mission freeze`/`unfreeze`,
and the drift check (`freeze_problems`)."""
from __future__ import annotations

import dataclasses
import datetime
import hashlib
import subprocess
import sys
from pathlib import Path
from typing import Sequence

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    Author, MissionManifest, Node, Proof, load_node, save_manifest, save_node,
)
from telperion.missions.statements import statement_body, write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status  # noqa: E402
from telperion.missions.process import (  # noqa: E402
    DEVIATIONS_TEMPLATE, _dump_freeze, _load_freeze, crosscheck_axioms, deviations_grant_problem,
    deviations_path, deviations_readback_path, freeze, freeze_grant_problem,
    freeze_history_problems, freeze_path, freeze_problems, parse_deviations, parse_print_axioms,
    render_audit_file, unfreeze, write_deviations_readback,
)
from telperion.cli import main  # noqa: E402
from test_missions_checks import FROZEN_FP  # noqa: E402  (step 5 Task 6: the frozen statement fingerprints)


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
# freeze_history_problems hardening (fix round 3, Controller Ruling 7)
#
# NEW-3 (rename sandwich): the walk used to look up every candidate SHA by TODAY's path
# (`git show <sha>:FREEZE.toml`), silently skipping any commit where that lookup failed --
# which is exactly what happens while the file sits at a different path. NEW-2 (shallow
# clone): CI's typical default truncates history by construction, which the walk did not
# detect at all. Both let an illegitimate edit hide; see the module docstring for NEW-1
# (history rewrite), which is documented rather than fixed -- it is inherent to local git.
# ---------------------------------------------------------------------------

def test_freeze_history_rename_sandwich_detected(tmp_path):
    """The reviewer's exact repro: c1 freezes (v1, H1); c2 renames FREEZE.toml away; c3,
    still renamed, is a LEGITIMATE v1->v2 bump (H1->H2, a real [[unfreeze]] entry); c4,
    still renamed, is an ILLEGITIMATE second edit with version left at 2 (H2->H3, no new
    entry) -- the same shape as the original C1 tamper, laundered underneath c3's
    legitimate bump; c5 renames the file back. Comparing only c1 (v1, H1) to c5 (v2, H3) --
    what a lookup-by-today's-path walk sees -- makes this look like one clean bump. Walking
    every commit and refusing to continue past the one where the path disappears (c2) is
    what catches it."""
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)

    doc1 = freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "c1: initial freeze (v1)")

    subprocess.run(["git", "-C", str(root), "mv", "FREEZE.toml", "FREEZE2.toml"],
                  check=True, capture_output=True, text=True)
    _git_commit(root, "c2: rename FREEZE.toml away")

    write_statement(root, load_campaign(root).nodes["Node_A"],
                    "theorem thm_Node_A : 11 = 11", manifest)
    h2 = hashlib.sha256(
        statement_body(root, load_campaign(root).nodes["Node_A"]).encode("utf-8")
    ).hexdigest()
    doc2 = dict(doc1)
    doc2["version"] = 2
    doc2["statements"] = dict(doc1["statements"], Node_A=h2)
    doc2["unfreeze"] = [{"version": 2, "date": "2026-10-29", "author": "alice@example.com",
                         "reason": "legitimate revision", "readback_identity": "bob@example.com"}]
    (root / "FREEZE2.toml").write_text(_dump_freeze(doc2))
    _git_commit(root, "c3: legitimate v1 -> v2 bump while renamed")

    write_statement(root, load_campaign(root).nodes["Node_A"],
                    "theorem thm_Node_A : 22 = 22", manifest)
    h3 = hashlib.sha256(
        statement_body(root, load_campaign(root).nodes["Node_A"]).encode("utf-8")
    ).hexdigest()
    doc3 = dict(doc2)
    doc3["statements"] = dict(doc2["statements"], Node_A=h3)
    # version left at 2; no new [[unfreeze]] entry -- the illegitimate edit.
    (root / "FREEZE2.toml").write_text(_dump_freeze(doc3))
    _git_commit(root, "c4: illegitimate edit, version left at 2")

    subprocess.run(["git", "-C", str(root), "mv", "FREEZE2.toml", "FREEZE.toml"],
                  check=True, capture_output=True, text=True)
    _git_commit(root, "c5: rename back")

    problems = freeze_problems(root)
    assert any("deleted or moved in history" in p for p in problems)


def test_freeze_history_symlink_in_past_commit_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    doc1 = freeze(root, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(root, "c1: initial freeze")

    freeze_path(root).unlink()
    freeze_path(root).symlink_to("mission.toml")
    _git_commit(root, "c2: FREEZE.toml recorded as a symlink")

    # Restored to an ordinary file (same content) so the CURRENT working tree is NOT a
    # symlink -- isolating the history walk's own mode check from the separately tested
    # working-tree check below.
    freeze_path(root).unlink()
    freeze_path(root).write_text(_dump_freeze(doc1))
    _git_commit(root, "c3: restored to an ordinary file")

    problems = freeze_problems(root)
    assert any("symlink" in p and "mode 120000" in p for p in problems)


def test_freeze_history_symlink_in_working_tree_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")  # post-cutoff
    freeze_path(root).unlink()
    freeze_path(root).symlink_to("mission.toml")

    problems = freeze_problems(root)
    assert any("is a symlink in the working tree" in p for p in problems)


def test_freeze_history_symlink_in_working_tree_flagged_even_pre_cutoff(tmp_path):
    """Unlike every other freeze_history_problems check, a working-tree symlink is NOT
    gated by cutoff: `_load_freeze` reads through it, so even the `frozen` field every
    other check relies on to decide whether it applies cannot be trusted here."""
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")  # pre-cutoff
    freeze_path(root).unlink()
    freeze_path(root).symlink_to("mission.toml")

    problems = freeze_problems(root)
    assert any("is a symlink in the working tree" in p for p in problems)


def test_freeze_history_shallow_clone_flagged(tmp_path):
    src = tmp_path / "source"
    manifest = _campaign(src)
    _git_init(src)
    freeze(src, identity="alice@example.com", session="s1", date="2026-10-28")
    _git_commit(src, "c1: initial freeze")

    write_statement(src, load_campaign(src).nodes["Node_A"],
                    "theorem thm_Node_A : 7 = 7", manifest)
    unfreeze(src, author="alice@example.com", reason="revision",
             readback_identity="bob@example.com", date="2026-10-29")
    _git_commit(src, "c2: unfreeze to v2")

    dest = tmp_path / "clone"
    r = subprocess.run(
        ["git", "clone", "--quiet", "--depth", "1", f"file://{src}", str(dest)],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, r.stderr

    problems = freeze_problems(dest)
    assert any("shallow clone" in p for p in problems)


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
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
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
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")
    deviations_path(root).write_text(DEVIATIONS_TEMPLATE)  # Step 5 Task 3's ledger gate
    write_deviations_readback(root, identity="auditor@example.com",  # fix round 1's read-back gate
                              session="auditor-session", date="2026-10-29")

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


# ---------------------------------------------------------------------------
# Fix round 4 (Controller Ruling 8): one guarded FREEZE.toml loader for every reader, and a
# single-pass history walk (`git log --raw` + `git cat-file --batch`)
# ---------------------------------------------------------------------------

def _git(root: Path, *args: str) -> str:
    r = subprocess.run(
        ["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@example.invalid",
         *args],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, r.stderr
    return r.stdout


def _symlink_freeze(root: Path, target: str) -> None:
    freeze_path(root).unlink()
    freeze_path(root).symlink_to(target)


def _non_utf8_target(root: Path) -> str:
    (root / "poison.bin").write_bytes(b'version = 1\nfrozen = "\xff\xfe\xfd"\n')
    return "poison.bin"


def _post_cutoff_frozen_grant_campaign(parent: Path, campaign: str = "campaign") -> Path:
    """`_grant_campaign`'s post-cutoff node with passing checks, frozen and committed --
    grantable as it stands, so a refusal can only come from what a test then does to
    FREEZE.toml."""
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(parent, created="2026-10-29", campaign=campaign)
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")
    deviations_path(root).write_text(DEVIATIONS_TEMPLATE)  # Step 5 Task 3's ledger gate
    write_deviations_readback(root, identity="auditor@example.com",  # fix round 1's read-back gate
                              session="auditor-session", date="2026-10-29")
    return root


def test_freeze_problems_symlink_to_mission_toml_reports_only_the_refusal(tmp_path):
    """Re-review 2's first repro: a symlink to another valid TOML file used to be read
    THROUGH by freeze_problems' own load, producing a spurious 'not recorded' line from
    mission.toml's fields ahead of the refusal."""
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _symlink_freeze(root, "mission.toml")

    assert freeze_problems(root) == [
        "FREEZE.toml is a symlink in the working tree; refusing to trust it."]


def test_freeze_problems_symlink_to_non_utf8_does_not_raise(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _symlink_freeze(root, _non_utf8_target(root))

    problems = freeze_problems(root)
    assert problems == ["FREEZE.toml is a symlink in the working tree; refusing to trust it."]


@pytest.mark.parametrize("target", ["mission.toml", "poison"])
def test_freeze_grant_problem_refuses_symlinked_freeze(tmp_path, target):
    root = _post_cutoff_frozen_grant_campaign(tmp_path)
    _symlink_freeze(root, _non_utf8_target(root) if target == "poison" else "mission.toml")
    node = load_node(root / "nodes" / "Demo_ck.toml")

    assert "is a symlink in the working tree" in freeze_grant_problem(root, node)
    with pytest.raises(GateError, match="symlink"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


@pytest.mark.parametrize("content, expect", [
    (b'version = 1\nfrozen = "\xff"\n', "not valid UTF-8"),
    (b"version = = 1\n", "not valid TOML"),
    (b'version = "two"\nfrozen = "2026-10-29"\n', "version"),
    (b'version = 1\nfrozen = "2026-10-29"\nstatements = "x"\n', "statements"),
    (b'version = 1\nfrozen = "2026-10-29"\nunfreeze = [1, 2]\n', "unfreeze"),
    (b"x = 1\n" + b"#" * (1 << 20), "larger than"),
], ids=["non-utf8", "bad-toml", "version-type", "statements-type", "unfreeze-type", "oversize"])
def test_unreadable_freeze_is_a_problem_not_an_exception(tmp_path, content, expect):
    root = _post_cutoff_frozen_grant_campaign(tmp_path)
    freeze_path(root).write_bytes(content)
    node = load_node(root / "nodes" / "Demo_ck.toml")

    problems = freeze_problems(root)
    assert len(problems) == 1 and expect in problems[0], problems
    assert expect in freeze_grant_problem(root, node)
    assert freeze_history_problems(root) == problems
    with pytest.raises(ValueError, match="FREEZE.toml"):
        unfreeze(root, author="alice@example.com", reason="r",
                 readback_identity="bob@example.com", date="2026-10-30")


def test_freeze_as_directory_in_working_tree_is_a_problem(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    freeze_path(root).unlink()
    freeze_path(root).mkdir()

    problems = freeze_problems(root)
    assert len(problems) == 1 and "not a regular file" in problems[0]


def test_freeze_refuses_over_a_dangling_symlink(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze_path(root).symlink_to("nowhere.toml")
    with pytest.raises(ValueError, match="already"):
        freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")


def test_cli_verify_symlinked_non_utf8_freeze_is_clean_error(tmp_path, capsys):
    mroot = tmp_path / "missions"
    root = _post_cutoff_frozen_grant_campaign(mroot, campaign="demo")
    _symlink_freeze(root, _non_utf8_target(root))

    rc = main(["mission", "--missions-root", str(mroot), "verify", "demo"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "symlink" in out and "Traceback" not in out


def test_cli_grant_symlinked_non_utf8_freeze_is_clean_error(tmp_path, capsys):
    mroot = tmp_path / "missions"
    root = _post_cutoff_frozen_grant_campaign(mroot, campaign="demo")
    _symlink_freeze(root, _non_utf8_target(root))

    rc = main(["mission", "--missions-root", str(mroot), "grant", "Demo_ck",
               "--campaign", "demo", "--identity", "gate@test", "--session", "gate-session"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "symlink" in out and "Traceback" not in out
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


@pytest.mark.parametrize("command", ["verify", "grant"])
def test_cli_verify_and_grant_turn_any_exception_into_a_clean_error(tmp_path, capsys,
                                                                     monkeypatch, command):
    """Belt and braces behind the guarded loader: whatever a freeze read (or anything else
    under verify/grant) raises, the CLI reports it and exits non-zero, never a traceback."""
    import telperion.missions.verify as verify_mod

    def boom(*_a, **_k):
        raise UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")

    mroot = tmp_path / "missions"
    _post_cutoff_frozen_grant_campaign(mroot, campaign="demo")
    monkeypatch.setattr(verify_mod, "verify_campaign" if command == "verify" else "grant_status",
                        boom)
    argv = ["mission", "--missions-root", str(mroot), command]
    argv += (["demo"] if command == "verify" else
             ["Demo_ck", "--campaign", "demo", "--identity", "gate@test",
              "--session", "gate-session"])
    rc = main(argv)
    out = capsys.readouterr().out
    assert rc == 1
    assert "UnicodeDecodeError" in out


def test_freeze_history_gitlink_has_a_clear_message(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    head = _git(root, "rev-parse", "HEAD").strip()
    _git(root, "rm", "-q", "--cached", "FREEZE.toml")
    _git(root, "update-index", "--add", "--cacheinfo", f"160000,{head},FREEZE.toml")
    _git(root, "commit", "-q", "-m", "c2: FREEZE.toml replaced by a gitlink")
    c2 = _git(root, "rev-parse", "HEAD").strip()

    assert f"FREEZE.toml is a gitlink/submodule at {c2[:12]}" in " ".join(freeze_problems(root))


def test_freeze_history_directory_at_path_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze_path(root).mkdir()
    (freeze_path(root) / "inner").write_text("x\n")
    _git_commit(root, "c1: FREEZE.toml is a directory")
    (freeze_path(root) / "inner").unlink()
    freeze_path(root).rmdir()
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c2: an ordinary FREEZE.toml replaces it")

    problems = freeze_problems(root)
    assert any("FREEZE.toml" in p and "history" in p for p in problems), problems


def test_freeze_history_delete_then_readd_flagged(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    freeze_path(root).unlink()
    _git_commit(root, "c2: delete it", add=("-A",))
    freeze(root, identity="mallory@example.com", session="s2", date="2026-10-30")
    _git_commit(root, "c3: a fresh 'version 1'")

    assert any("deleted or moved in history" in p for p in freeze_problems(root))


def _tamper_hash(root: Path, manifest, text: str) -> None:
    """The C1 tamper: edit Node_A's statement and rewrite its recorded hash to match, at an
    unchanged version."""
    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, text, manifest)
    h = hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()
    _hand_edit_freeze(root, lambda d: d["statements"].__setitem__("Node_A", h))


def test_freeze_history_merge_bringing_a_tamper_from_a_side_branch_flagged(tmp_path):
    """The merge's tree is identical to its SECOND parent at FREEZE.toml (the side branch
    brought the whole change) and differs from its first; `git log --first-parent -- path`
    must still list it."""
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    main_branch = _git(root, "symbolic-ref", "--short", "HEAD").strip()

    _git(root, "checkout", "-q", "-b", "side")
    _tamper_hash(root, manifest, "theorem thm_Node_A : 5 = 5")
    _git_commit(root, "side: tamper")
    _git(root, "checkout", "-q", main_branch)
    (root / "unrelated.txt").write_text("x\n")
    _git_commit(root, "main: unrelated")
    _git(root, "merge", "-q", "--no-ff", "side", "-m", "merge side")

    assert any("without a version bump" in p for p in freeze_problems(root))


def test_freeze_history_merge_bringing_a_legitimate_unfreeze_clean(tmp_path):
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    main_branch = _git(root, "symbolic-ref", "--short", "HEAD").strip()

    _git(root, "checkout", "-q", "-b", "side")
    write_statement(root, load_campaign(root).nodes["Node_A"], "theorem thm_Node_A : 6 = 6",
                    manifest)
    unfreeze(root, author="alice@example.com", reason="revision",
             readback_identity="bob@example.com", date="2026-10-30")
    _git_commit(root, "side: legitimate unfreeze")
    _git(root, "checkout", "-q", main_branch)
    (root / "unrelated.txt").write_text("x\n")
    _git_commit(root, "main: unrelated")
    _git(root, "merge", "-q", "--no-ff", "side", "-m", "merge side")

    assert freeze_problems(root) == []


def test_freeze_history_evil_merge_flagged(tmp_path):
    """A merge whose FREEZE.toml matches NEITHER parent (the tamper is made while resolving
    the merge itself)."""
    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    main_branch = _git(root, "symbolic-ref", "--short", "HEAD").strip()

    _git(root, "checkout", "-q", "-b", "side")
    (root / "side.txt").write_text("s\n")
    _git_commit(root, "side: unrelated")
    _git(root, "checkout", "-q", main_branch)
    _git(root, "merge", "-q", "--no-ff", "--no-commit", "side")
    _tamper_hash(root, manifest, "theorem thm_Node_A : 8 = 8")
    _git_commit(root, "evil merge")

    assert any("without a version bump" in p for p in freeze_problems(root))


def _append_noise_commits(root: Path, n: int) -> None:
    """*n* further first-parent commits on HEAD that never touch FREEZE.toml, written in ONE
    `git fast-import` pass -- a `git commit` per commit would make the fixture itself the
    slow part."""
    branch = _git(root, "symbolic-ref", "HEAD").strip()
    head = _git(root, "rev-parse", "HEAD").strip()
    chunks = []
    for i in range(n):
        data = f"{i}\n".encode()
        chunks.append(
            f"commit {branch}\ncommitter t <t@example.invalid> {1761700000 + i} +0000\n"
            f"data 5\nnoise\n".encode()
            + (f"from {head}\n".encode() if i == 0 else b"")
            + f"M 100644 inline noise.txt\ndata {len(data)}\n".encode() + data + b"\n")
    r = subprocess.run(["git", "-C", str(root), "fast-import", "--quiet"],
                       input=b"".join(chunks), capture_output=True)
    assert r.returncode == 0, r.stderr


def test_freeze_history_walk_is_single_pass_over_500_commits(tmp_path, monkeypatch):
    """Ruling 8 (b): round 3 ran one `git ls-tree` per first-parent commit (~29 s for 2,000
    commits, on every post-cutoff grant). The walk's git calls must not grow with history
    length, and 500 commits must take well under 5 s."""
    import time

    import telperion.missions.process as process_mod

    root = tmp_path / "demo"
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: initial freeze")
    _append_noise_commits(root, 250)
    write_statement(root, load_campaign(root).nodes["Node_A"], "theorem thm_Node_A : 4 = 4",
                    manifest)
    unfreeze(root, author="alice@example.com", reason="revision",
             readback_identity="bob@example.com", date="2026-10-30")
    _git_commit(root, "unfreeze to v2", add=("FREEZE.toml", "lean"))
    _append_noise_commits(root, 248)
    assert int(_git(root, "rev-list", "--count", "HEAD")) == 500

    calls = []
    real_run = subprocess.run

    def counting_run(argv, *a, **k):
        calls.append(list(argv))
        return real_run(argv, *a, **k)

    monkeypatch.setattr(process_mod.subprocess, "run", counting_run)
    t0 = time.monotonic()
    problems = freeze_history_problems(root)
    elapsed = time.monotonic() - t0

    assert problems == []
    assert len(calls) <= 8, [c[3:5] for c in calls[:12]]
    assert elapsed < 5.0


def test_freeze_history_non_utf8_blob_is_a_problem_not_an_exception(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze_path(root).write_bytes(b'version = 1\nfrozen = "\xff"\n')
    _git_commit(root, "c1: a FREEZE.toml that is not UTF-8")
    c1 = _git(root, "rev-parse", "HEAD").strip()
    freeze_path(root).unlink()
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c2: an ordinary freeze over it")

    assert freeze_problems(root) == [
        f"FREEZE.toml could not be read at commit {c1[:12]}: it is not valid UTF-8."]


def test_freeze_history_campaign_dir_with_glob_characters(tmp_path):
    """The path handed to `git log` is literal (`--literal-pathspecs`): a campaign at
    `c[1]/` is not confused with a sibling `c1/` whose FREEZE.toml has its own history."""
    repo = tmp_path / "repo"
    root, sibling = repo / "c[1]", repo / "c1"
    manifest = _campaign(root)
    _campaign(sibling)
    _git_init(repo)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    freeze(sibling, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(repo, "c1: both frozen")
    freeze_path(sibling).unlink()
    _git_commit(repo, "c2: the sibling's freeze deleted", add=("-A",))

    assert freeze_problems(root) == []
    _tamper_hash(root, manifest, "theorem thm_Node_A : 9 = 9")
    _git_commit(repo, "c3: tamper")
    assert any("without a version bump" in p for p in freeze_problems(root))


def test_freeze_history_campaign_in_a_subdirectory_of_the_repo(tmp_path):
    """Every real campaign lives at `missions/<name>/`, not at the repository root. Round 3
    ran the walk's git commands from the campaign root with a top-level-relative path, found
    no history, and reported every such post-cutoff campaign as never committed."""
    repo = tmp_path / "repo"
    root = repo / "missions" / "demo"
    manifest = _campaign(root)
    _git_init(repo)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(repo, "c1: initial freeze")

    assert freeze_problems(root) == []
    _tamper_hash(root, manifest, "theorem thm_Node_A : 3 = 3")
    _git_commit(repo, "c2: tamper")
    assert any("without a version bump" in p for p in freeze_problems(root))


# ---------------------------------------------------------------------------
# Fix round 5 (Controller Ruling 9): every git call through one sanitised helper -- no
# replace objects, no inherited GIT_* environment -- and grafts/alternates refused
# ---------------------------------------------------------------------------

def _frozen_then_tampered(root: Path) -> str:
    """c1: an honest freeze; c2: the C1 tamper (hash rewritten, no version bump). Returns
    c1's sha. Baseline: freeze_problems flags c2."""
    manifest = _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: honest freeze")
    c1 = _git(root, "rev-parse", "HEAD").strip()
    _tamper_hash(root, manifest, "theorem thm_Node_A : 12 = 12")
    _git_commit(root, "c2: tamper, no version bump")
    assert any("without a version bump" in p for p in freeze_problems(root))
    return c1


def test_freeze_history_ignores_git_replace_refs(tmp_path):
    """Re-review 3: `git replace <c1> <fabricated root with c2's tree>` made the genesis
    LOOK like it always had the tampered hash, and freeze_problems returned []."""
    root = tmp_path / "demo"
    c1 = _frozen_then_tampered(root)
    tree = _git(root, "rev-parse", "HEAD^{tree}").strip()
    fake = _git(root, "commit-tree", tree, "-m", "fabricated genesis").strip()
    _git(root, "replace", c1, fake)
    assert "fabricated genesis" in _git(root, "log", "--format=%s")  # the replace is live

    assert any("without a version bump" in p for p in freeze_problems(root))


def test_freeze_history_ignores_inherited_git_dir(tmp_path, monkeypatch):
    """Re-review 3: GIT_DIR in the environment pointed the history walk at a decoy repo
    whose only commit already carries the tampered hash, while the working-tree read saw the
    real file -- freeze_problems returned []."""
    import shutil

    root = tmp_path / "demo"
    _frozen_then_tampered(root)
    decoy = tmp_path / "decoy"
    shutil.copytree(root, decoy, ignore=shutil.ignore_patterns(".git"))
    _git_init(decoy)
    _git_commit(decoy, "decoy: the tampered state as an honest genesis")
    assert freeze_problems(decoy) == []  # the decoy is self-consistent on its own

    for var, value in (("GIT_DIR", str(decoy / ".git")),
                       ("GIT_OBJECT_DIRECTORY", str(decoy / ".git" / "objects")),
                       ("GIT_INDEX_FILE", str(tmp_path / "nowhere"))):
        monkeypatch.setenv(var, value)
    assert any("without a version bump" in p for p in freeze_problems(root))


def test_freeze_history_refuses_grafts(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: honest freeze")
    (root / ".git" / "info").mkdir(exist_ok=True)
    (root / ".git" / "info" / "grafts").write_text("")

    problems = freeze_problems(root)
    assert any("info/grafts" in p for p in problems), problems


@pytest.mark.parametrize("name", ["alternates", "http-alternates"])
def test_freeze_history_refuses_alternates(tmp_path, name):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    _git_commit(root, "c1: honest freeze")
    other = tmp_path / "other"
    other.mkdir()
    _git_init(other)
    info = root / ".git" / "objects" / "info"
    info.mkdir(parents=True, exist_ok=True)
    (info / name).write_text(str(other / ".git" / "objects") + "\n")

    problems = freeze_problems(root)
    assert any(f"objects/info/{name}" in p for p in problems), problems


def test_pre_cutoff_campaign_not_penalised_for_grafts(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")
    _git_commit(root, "c1: honest freeze")
    (root / ".git" / "info").mkdir(exist_ok=True)
    (root / ".git" / "info" / "grafts").write_text("")
    assert freeze_problems(root) == []


# ---------------------------------------------------------------------------
# Step 5 Task 2: Audit.lean generation and its #print-axioms vs closure-audit cross-check
# ---------------------------------------------------------------------------

def _proved_node(root: Path, manifest: MissionManifest, name: str, *, stmt_suffix: str = "True"
                 ) -> Node:
    """A PROVED node with a statement and a matching artifact -- the same shape as
    `test_missions_checks._grant_campaign`'s `Demo_ck`: the artifact text is the statement
    text immediately followed by a proof body, so `guard_anchors.resolve_theorem` binds
    `thm_<name>` to it cleanly."""
    stmt_text = f"theorem thm_{name} : {stmt_suffix}"
    node = Node(name=name, title=f"title of {name}", kind="lemma", status="proved",
               depends_on=(), statement_module=f"Statements.{name}",
               proof=Proof(artifact=f"proof/{name}.lean", artifact_kind="lean_module",
                          via="direct"))
    save_node(node, root / "nodes" / f"{name}.toml")
    write_statement(root, node, stmt_text, manifest)
    art = root / "proof" / f"{name}.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text(f"{stmt_text} := trivial\n")
    return node


def _audit_campaign(root: Path) -> MissionManifest:
    """Two PROVED nodes (Node_A, Node_B) and one DRAFT node (Node_C, no proof/statement
    matching needed) -- enough to check `render_audit_file` lists proved nodes only."""
    manifest = MissionManifest(
        name="Demo.goal", title="Demo Campaign", description="synthetic",
        goal_node="Node_A", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    (root / "nodes").mkdir(parents=True, exist_ok=True)
    save_manifest(manifest, root / "mission.toml")
    _proved_node(root, manifest, "Node_A")
    _proved_node(root, manifest, "Node_B")
    draft = Node(name="Node_C", title="still open", kind="lemma", status="draft",
                depends_on=(), statement_module="Statements.Node_C")
    save_node(draft, root / "nodes" / "Node_C.toml")
    write_statement(root, draft, "theorem thm_Node_C : True", manifest)
    return manifest


def test_render_lists_proved_only(tmp_path):
    root = tmp_path / "demo"
    _audit_campaign(root)

    text = render_audit_file(root)

    # Generated-file header.
    assert "GENERATED" in text.splitlines()[0] and "DO NOT EDIT" in text

    # Both proved nodes' theorems are printed, sorted by slug (Node_A before Node_B).
    idx_a = text.index("#print axioms thm_Node_A")
    idx_b = text.index("#print axioms thm_Node_B")
    assert idx_a < idx_b

    # One import per distinct artifact module, de-duplicated and sorted; off-island
    # fixtures resolve to the artifact's own file stem (Node_A.lean -> Node_A).
    assert "import Node_A" in text
    assert "import Node_B" in text

    # The draft node's theorem is not printed at all.
    assert "thm_Node_C" not in text


def test_render_audit_file_sorted_and_deduplicated_imports(tmp_path):
    root = tmp_path / "demo"
    _audit_campaign(root)

    text = render_audit_file(root)
    imports = [ln for ln in text.splitlines() if ln.startswith("import ")]
    assert imports == sorted(set(imports))


def test_parse_single_line():
    out = "'T' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    assert parse_print_axioms(out) == {
        "T": {"propext", "Classical.choice", "Quot.sound"},
    }


def test_wrapped_axioms():
    out = (
        "'T' depends on axioms: [propext,\n"
        " Classical.choice,\n"
        " Quot.sound]\n"
    )
    assert parse_print_axioms(out) == {
        "T": {"propext", "Classical.choice", "Quot.sound"},
    }


def test_no_axioms():
    out = "'T' does not depend on any axioms\n"
    assert parse_print_axioms(out) == {"T": set()}


def test_parse_print_axioms_dotted_and_guillemet_names():
    out = (
        "'Foo.bar' depends on axioms: [propext]\n"
        "'Foo.«bar baz».qux' does not depend on any axioms\n"
    )
    parsed = parse_print_axioms(out)
    assert parsed["Foo.bar"] == {"propext"}
    assert parsed["Foo.«bar baz».qux"] == set()


def test_parse_print_axioms_duplicate_conflicting_sets_raises():
    out = (
        "'T' depends on axioms: [propext]\n"
        "'T' depends on axioms: [propext, sorryAx]\n"
    )
    with pytest.raises(ValueError, match="T"):
        parse_print_axioms(out)


def test_parse_print_axioms_duplicate_same_set_ok():
    out = (
        "'T' depends on axioms: [propext]\n"
        "'T' depends on axioms: [propext]\n"
    )
    assert parse_print_axioms(out) == {"T": {"propext"}}


def test_crosscheck_flags_stale_cache_case():
    print_axioms = {"T": {"propext"}}
    closure_axioms = {"T": ["propext", "sorryAx"]}

    problems = crosscheck_axioms(print_axioms, closure_axioms)

    assert len(problems) == 1
    assert "T" in problems[0] and "sorryAx" in problems[0]


def test_crosscheck_equal_ok():
    print_axioms = {"T": {"propext", "Classical.choice"}}
    closure_axioms = {"T": ["propext", "Classical.choice"]}

    assert crosscheck_axioms(print_axioms, closure_axioms) == []


def test_crosscheck_missing_from_one_side_is_a_problem():
    only_print = crosscheck_axioms({"T": {"propext"}}, {})
    assert len(only_print) == 1 and "T" in only_print[0]

    only_closure = crosscheck_axioms({}, {"T": ["propext"]})
    assert len(only_closure) == 1 and "T" in only_closure[0]


# ---------------------------------------------------------------------------
# CLI: `mission audit-file` / `mission audit-crosscheck`
# ---------------------------------------------------------------------------

def test_cli_audit_file_writes_lean_file(tmp_path, capsys):
    mroot = tmp_path / "missions"
    _audit_campaign(mroot / "demo")

    rc = main(["mission", "--missions-root", str(mroot), "audit-file", "demo"])
    assert rc == 0
    out_path = mroot / "demo" / "lean" / "Audit.lean"
    assert out_path.exists()
    text = out_path.read_text()
    assert "#print axioms thm_Node_A" in text
    assert "#print axioms thm_Node_B" in text


def test_cli_audit_crosscheck_ok_and_mismatch(tmp_path, capsys):
    import json

    print_axioms_out = tmp_path / "print_axioms.txt"
    print_axioms_out.write_text("'T' depends on axioms: [propext]\n")
    closure_json = tmp_path / "closure.json"
    closure_json.write_text(json.dumps({
        "verdict": "PASS", "ok": True,
        "targets": [{"name": "T", "kind": "theorem", "statement": "", "axioms": ["propext"]}],
    }))

    rc = main(["mission", "audit-crosscheck",
              "--print-axioms-out", str(print_axioms_out),
              "--closure-json", str(closure_json)])
    assert rc == 0

    closure_json.write_text(json.dumps({
        "verdict": "PASS", "ok": True,
        "targets": [{"name": "T", "kind": "theorem", "statement": "",
                    "axioms": ["propext", "sorryAx"]}],
    }))
    rc = main(["mission", "audit-crosscheck",
              "--print-axioms-out", str(print_axioms_out),
              "--closure-json", str(closure_json)])
    assert rc == 1
    assert "sorryAx" in capsys.readouterr().out


# ---------------------------------------------------------------------------
# Step 5 Task 2 fix round 1 (Controller Ruling 10)
#
# C1: Lean source injection via an unsanitized module/theorem name in the generated
# `import`/`#print axioms` lines. C2: the #print-axioms parser corrupts on a trailing
# prime (the single most common Lean naming idiom) and on an unterminated axiom list.
# Important: `_artifact_module` must go through `provenance.lake_workspace`, not a
# parallel re-derivation of the island root. Minors: CLI input size cap/decode errors,
# and `crosscheck_axioms` type-checks the closure JSON's axiom entries.
# ---------------------------------------------------------------------------

def _evil_island_node(tmp_path: Path, evil_component: str, *, slug: str = "Evil") -> Path:
    """A real judge island (`<tel>/examples/isl_evil/lean/<evil_component>/Bar.lean`) and a
    campaign whose proved node's `[proof] artifact` names that file -- the reviewer's
    exact C1 repro shape: a path component a campaign author controls (and legitimately
    writes to disk), flowing straight into `_artifact_module`'s `import` line with none of
    `judge.module_name_of`'s own sanitisation (it performs none at all). Returns the
    campaign root."""
    tel = tmp_path / "telperion"
    island_lean = tel / "examples" / "isl_evil" / "lean"
    island_lean.mkdir(parents=True)
    (island_lean / "lakefile.toml").write_text('name = "IslEvil"\n\n[[lean_lib]]\nname = "Bar"\n')
    evil_dir = island_lean / evil_component
    evil_dir.mkdir(parents=True)
    stmt_text = f"theorem thm_{slug} : True"
    (evil_dir / "Bar.lean").write_text(f"{stmt_text} := trivial\n")

    camp = tel / "missions" / "demo"
    (camp / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.goal", title="Demo", description="synthetic", goal_node=slug,
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    save_manifest(manifest, camp / "mission.toml")
    rel = "/".join(["..", "..", "examples", "isl_evil", "lean", evil_component, "Bar.lean"])
    node = Node(name=slug, title="t", kind="lemma", status="proved", depends_on=(),
               statement_module=f"Statements.{slug}",
               proof=Proof(artifact=rel, artifact_kind="lean_module", via="direct"))
    save_node(node, camp / "nodes" / f"{slug}.toml")
    write_statement(camp, node, stmt_text, manifest)
    return camp


@pytest.mark.parametrize("evil_component", [
    'evil\n#eval IO.println "pwned-by-campaign-author"\n--',
    "has space",
    "«guillemet»",
], ids=["newline-eval", "space", "guillemet"])
def test_render_audit_file_refuses_unsafe_module_component(tmp_path, evil_component):
    """C1 (Critical): a module name derived from an unsafe artifact-path component --
    one that is not a plain Lean identifier -- must never be emitted into the generated
    `import` line; `render_audit_file` must raise rather than write it."""
    camp = _evil_island_node(tmp_path, evil_component)

    with pytest.raises(ValueError, match="not a plain Lean identifier"):
        render_audit_file(camp)


def test_validate_theorem_name_rejects_newline():
    """C1 (Critical), theorem-name side. `guard_anchors.resolve_theorem`'s own matching
    cannot actually produce a newline-bearing name (its regexes are word/`\\S+`-anchored
    throughout), so this is tested directly against the validator rather than through a
    contrived end-to-end artifact -- defense in depth, keeping the theorem side no less
    guarded than the module side."""
    from telperion.missions.process import _validate_theorem_name

    with pytest.raises(ValueError, match="control character"):
        _validate_theorem_name("thm_evil\n#eval 1", slug="X")

    _validate_theorem_name("thm_fine'", slug="X")  # a trailing prime is fine: no raise


def test_parse_print_axioms_trailing_prime():
    """C2 (Critical): a theorem name ending in its own `'` (the single most common Lean
    naming idiom) must be captured whole, not truncated at the embedded quote."""
    out = "'h'' depends on axioms: [propext]\n'foo''' does not depend on any axioms\n"
    parsed = parse_print_axioms(out)
    assert parsed == {"h'": {"propext"}, "foo''": set()}


def test_parse_print_axioms_unterminated_list_before_another_theorem_raises():
    """C2 (Critical): an unterminated bracket must never silently absorb a LATER
    theorem's own header line -- it must raise, naming the theorem whose list never
    closed, and 'T2' must never be allowed to simply vanish from the result."""
    out = ("'T1' depends on axioms: [propext, Classical.choice\n"
           "note: unrelated diagnostic line\n"
           "'T2' depends on axioms: [propext]\n")
    with pytest.raises(ValueError, match="unterminated axiom list for 'T1'"):
        parse_print_axioms(out)


def test_parse_print_axioms_unterminated_list_at_eof_raises():
    out = "'T1' depends on axioms: [propext, Classical.choice\n"
    with pytest.raises(ValueError, match="unterminated axiom list for 'T1'"):
        parse_print_axioms(out)


def test_parse_print_axioms_crlf():
    out = "'T' depends on axioms: [propext,\r\n Classical.choice]\r\n"
    assert parse_print_axioms(out) == {"T": {"propext", "Classical.choice"}}


def test_parse_print_axioms_interleaved_warnings_ignored():
    out = ("warning: something\n"
           "'T1' depends on axioms: [propext]\n"
           "info: unrelated\n"
           "'T2' does not depend on any axioms\n")
    assert parse_print_axioms(out) == {"T1": {"propext"}, "T2": set()}


def test_parse_print_axioms_guillemet_names_still_work():
    out = ("'Foo.bar' depends on axioms: [propext]\n"
          "'Foo.«bar baz».qux' does not depend on any axioms\n")
    parsed = parse_print_axioms(out)
    assert parsed["Foo.bar"] == {"propext"}
    assert parsed["Foo.«bar baz».qux"] == set()


def test_parse_print_axioms_malformed_header_raises():
    """A line that LOOKS like a header (starts with `'`, mentions "depends on axioms")
    but does not fully match the anchored pattern (here: missing the colon) must raise,
    not be silently skipped as an unrelated line."""
    out = "'T' depends on axioms [propext]\n"
    with pytest.raises(ValueError, match="unrecognised"):
        parse_print_axioms(out)


def test_parse_print_axioms_header_split_across_lines_raises():
    """Fix round 2 (Ruling 11): a `#print axioms` header split between its closing quote
    and "depends on axioms" (e.g. by a terminal/log line-wrap unrelated to Lean's own
    bracket-wrapping, which never splits the header itself -- only the axiom LIST) must
    raise, not be silently dropped as two unrelated-looking lines (the bare `'T'` line
    didn't itself contain "depends on axioms", so the earlier check let it through)."""
    out = "'T'\n depends on axioms: [propext]\n"
    with pytest.raises(ValueError, match="unrecognised"):
        parse_print_axioms(out)


def test_crosscheck_axioms_type_checks_closure_entries():
    with pytest.raises(ValueError, match="T"):
        crosscheck_axioms({"T": {"propext"}}, {"T": "propext"})  # a str, not a list
    with pytest.raises(ValueError, match="T"):
        crosscheck_axioms({"T": {"propext"}}, {"T": [1, 2]})     # not strings


def test_artifact_module_uses_lake_workspace_for_sub_workspace(tmp_path):
    """Important finding 3: `_artifact_module` must go through `provenance.lake_workspace`
    (the zzl_aux shape: a smaller sub-workspace, `srcDir = ".."`, declares the SAME module
    with far fewer libs) rather than a parallel re-derivation of the island root -- and
    must not crash when `lake_workspace` picks that smaller sub-workspace, whose own
    source root (via its `srcDir`) is the island root, not itself."""
    from telperion.missions.process import _artifact_module
    from telperion.missions.provenance import lake_workspace

    tel = tmp_path / "telperion"
    lean = tel / "examples" / "isl_subws" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text(
        'name = "isl_subws"\n\n[[lean_lib]]\nname = "O1"\n[[lean_lib]]\nname = "Target"\n')
    stmt_text = "theorem thm_SubWs : True"
    (lean / "Target.lean").write_text(f"{stmt_text} := trivial\n")
    sub_dir = lean / "sub_aux"
    sub_dir.mkdir()
    (sub_dir / "lakefile.toml").write_text(
        'name = "sub_aux"\nsrcDir = ".."\n\n[[lean_lib]]\nname = "Target"\n')

    camp = tel / "missions" / "demo"
    (camp / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.goal", title="Demo", description="synthetic", goal_node="SubWs",
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
        sources=(),
    )
    save_manifest(manifest, camp / "mission.toml")
    node = Node(name="SubWs", title="t", kind="lemma", status="proved", depends_on=(),
               statement_module="Statements.SubWs",
               proof=Proof(artifact="../../examples/isl_subws/lean/Target.lean",
                          artifact_kind="lean_module", via="direct"))
    save_node(node, camp / "nodes" / "SubWs.toml")
    write_statement(camp, node, stmt_text, manifest)

    # Sanity: lake_workspace really does pick the smaller sub-workspace here.
    assert lake_workspace(camp, node) == sub_dir.resolve()

    assert _artifact_module(camp, node) == "Target"

    text = render_audit_file(camp)
    assert "import Target" in text
    assert "#print axioms thm_SubWs" in text


def test_cli_audit_crosscheck_oversized_print_axioms_file_rejected(tmp_path, capsys):
    """Minor finding: the CLI's input reads are size-capped."""
    from telperion.cli import _AUDIT_CROSSCHECK_INPUT_MAX_BYTES

    print_axioms_out = tmp_path / "print_axioms.txt"
    print_axioms_out.write_bytes(b"x" * (_AUDIT_CROSSCHECK_INPUT_MAX_BYTES + 1))
    closure_json = tmp_path / "closure.json"
    closure_json.write_text('{"targets": []}')

    rc = main(["mission", "audit-crosscheck",
              "--print-axioms-out", str(print_axioms_out),
              "--closure-json", str(closure_json)])
    assert rc == 2
    assert "larger than" in capsys.readouterr().out


def test_cli_audit_crosscheck_non_utf8_print_axioms_file_rejected(tmp_path, capsys):
    """Minor finding: a clean error on decode failure, never a traceback."""
    print_axioms_out = tmp_path / "print_axioms.txt"
    print_axioms_out.write_bytes(b"\xff\xfe\xfd")
    closure_json = tmp_path / "closure.json"
    closure_json.write_text('{"targets": []}')

    rc = main(["mission", "audit-crosscheck",
              "--print-axioms-out", str(print_axioms_out),
              "--closure-json", str(closure_json)])
    assert rc == 2
    out = capsys.readouterr().out
    assert "not valid UTF-8" in out and "Traceback" not in out


def test_cli_audit_crosscheck_malformed_closure_axioms_rejected(tmp_path, capsys):
    """Minor finding: a malformed closure JSON's `axioms` entry is a clean CLI error, not
    a `TypeError` from deep inside `crosscheck_axioms`."""
    import json

    print_axioms_out = tmp_path / "print_axioms.txt"
    print_axioms_out.write_text("'T' depends on axioms: [propext]\n")
    closure_json = tmp_path / "closure.json"
    closure_json.write_text(json.dumps({
        "targets": [{"name": "T", "kind": "theorem", "statement": "", "axioms": "propext"}],
    }))

    rc = main(["mission", "audit-crosscheck",
              "--print-axioms-out", str(print_axioms_out),
              "--closure-json", str(closure_json)])
    assert rc == 2
    out = capsys.readouterr().out
    assert "malformed closure audit data" in out and "Traceback" not in out


def test_parse_print_axioms_split_header_primed_name_raises():
    """A split header whose name ends in a prime (`'h''`) must raise too (lead, Ruling 11)."""
    out = "'h''\n depends on axioms: [propext]\n"
    with pytest.raises(ValueError, match="unrecognised"):
        parse_print_axioms(out)


def test_process_runs_git_only_through_the_sanitised_helper():
    """Structural (Ruling 9): no subprocess call in process.py outside `_git`, so no git
    invocation can skip --no-replace-objects or the sanitised environment."""
    import ast

    import telperion.missions.process as process_mod

    tree = ast.parse(Path(process_mod.__file__).read_text())
    offenders = []

    def visit(node, inside_git):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            inside_git = node.name == "_git"
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in ("subprocess", "os") and not inside_git
                and node.func.attr in ("run", "Popen", "call", "check_call", "check_output",
                                       "system", "popen", "spawnv", "execv", "execvp")):
            offenders.append(node.lineno)
        for child in ast.iter_child_nodes(node):
            visit(child, inside_git)

    visit(tree, False)
    assert offenders == []
    assert any(isinstance(n, ast.FunctionDef) and n.name == "_git" for n in tree.body)


# ---------------------------------------------------------------------------
# Step 5 Task 3: the deviation ledger (DEVIATIONS.md)
# ---------------------------------------------------------------------------

def test_none_spellings():
    for ok in ("none", "None", "NONE."):
        assert parse_deviations(f"<!-- header -->\n{ok}\n") == []
    for bad in ("N/A", "n/a"):
        with pytest.raises(ValueError, match="write `none`"):
            parse_deviations(f"<!-- header -->\n{bad}\n")
    with pytest.raises(ValueError, match="write `none`"):
        parse_deviations("<!-- header -->\n")


def test_entries_parse():
    text = (
        "<!-- header -->\n"
        "\n"
        "- 2026-10-28 | statement drops the finite-support hypothesis | implied by the "
        "proof's own domain restriction\n"
        "- 2026-10-29 | renamed the bound variable | matches the paper's notation\n"
    )
    assert parse_deviations(text) == [
        {"date": "2026-10-28", "what": "statement drops the finite-support hypothesis",
         "why": "implied by the proof's own domain restriction"},
        {"date": "2026-10-29", "what": "renamed the bound variable",
         "why": "matches the paper's notation"},
    ]


def test_bad_entry_line_number():
    text = (
        "<!-- header -->\n"
        "- 2026-10-28 | ok | ok reason\n"
        "- not-a-date | bad | bad\n"
    )
    with pytest.raises(ValueError, match="DEVIATIONS.md:3"):
        parse_deviations(text)


def test_invalid_calendar_date_raises():
    with pytest.raises(ValueError, match="DEVIATIONS.md:2"):
        parse_deviations("<!-- header -->\n- 2026-02-30 | bad date | reason\n")


@pytest.mark.parametrize("entry", [
    "- 2026-10-28 |  | reason\n",
    "- 2026-10-28 | what |  \n",
])
def test_empty_what_or_why_raises(entry):
    with pytest.raises(ValueError, match="DEVIATIONS.md:2"):
        parse_deviations("<!-- header -->\n" + entry)


def test_unterminated_header_comment_raises():
    with pytest.raises(ValueError, match="DEVIATIONS.md:1"):
        parse_deviations("<!-- never closed\nnone\n")


def test_template_parses_as_none():
    assert parse_deviations(DEVIATIONS_TEMPLATE) == []


def test_post_cutoff_grant_requires_ledger(tmp_path):
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")

    with pytest.raises(GateError, match="DEVIATIONS.md"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"
    assert "DEVIATIONS.md" in deviations_grant_problem(root, node)

    deviations_path(root).write_text(DEVIATIONS_TEMPLATE)
    write_deviations_readback(root, identity="auditor@example.com",  # fix round 1's read-back gate
                              session="auditor-session", date="2026-10-29")

    granted = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"


def test_deviations_symlink_refused_as_clean_problem(tmp_path):
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")
    deviations_path(root).symlink_to("mission.toml")

    assert "symlink" in deviations_grant_problem(root, node)
    with pytest.raises(GateError, match="symlink"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_cli_grant_non_utf8_deviations_is_clean_error(tmp_path, capsys):
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    mroot = tmp_path / "missions"
    root = _grant_campaign(mroot, created="2026-10-29", campaign="demo")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")
    deviations_path(root).write_bytes(b"\xff\xfe\xfd")

    rc = main(["mission", "--missions-root", str(mroot), "grant", "Demo_ck",
              "--campaign", "demo", "--identity", "gate@test", "--session", "gate-session"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "DEVIATIONS.md" in out and "Traceback" not in out
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_cli_freeze_writes_deviations_template_when_missing(tmp_path):
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 0
    dpath = deviations_path(mroot / "demo")
    assert dpath.exists()
    assert parse_deviations(dpath.read_text()) == []


def test_cli_freeze_does_not_overwrite_existing_deviations(tmp_path):
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")
    dpath = deviations_path(mroot / "demo")
    dpath.parent.mkdir(parents=True, exist_ok=True)
    dpath.write_text("- 2026-10-01 | custom | already written\n")

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo",
              "--identity", "alice@example.com", "--session", "s1"])
    assert rc == 0
    assert "custom" in dpath.read_text()


# ---------------------------------------------------------------------------
# Step 5 Task 3, fix round 1 (a): content sharing a line with the header comment's `<!--`
# / `-->` markers is parsed, not silently dropped.
# ---------------------------------------------------------------------------

def test_same_line_comment_entry_mixed_with_none_raises():
    """The reviewer's repro: a real entry hiding after the header's closing `-->` on the
    SAME physical line used to vanish entirely (the ledger parsed as plain `none`). It
    must now be seen -- and a body holding both `none` and a real entry is malformed."""
    text = "<!-- header --> - 2026-10-28 | hidden entry | sneaky\nnone\n"
    with pytest.raises(ValueError, match="DEVIATIONS.md:2"):
        parse_deviations(text)


def test_same_line_comment_entry_parses_without_none():
    text = "<!-- header --> - 2026-10-28 | real entry | because it matters\n"
    assert parse_deviations(text) == [
        {"date": "2026-10-28", "what": "real entry", "why": "because it matters"},
    ]


def test_content_before_comment_opener_parses():
    """Symmetric with the "after `-->`" case: text before the opening `<!--` on that same
    line is kept too, not discarded along with the comment that follows it."""
    text = "- 2026-10-28 | what | why <!-- trailing note -->\n"
    assert parse_deviations(text) == [
        {"date": "2026-10-28", "what": "what", "why": "why"},
    ]


# ---------------------------------------------------------------------------
# Step 5 Task 3, fix round 1 (b): DEVIATIONS.md must be READ BACK (spec 7.3), not merely
# parsed -- `mission deviations-readback` writes DEVIATIONS.readback.toml, and the grant
# gate requires it, current, and from an auditor who is not the node's own author.
# ---------------------------------------------------------------------------

#: Distinguishes "no *author* argument given" (keep `_grant_campaign`'s own default
#: `[author]`) from "*author* explicitly passed as `None`" (strip it off entirely, for the
#: fix-round-2 "no [author] at all" repro) -- a plain `None` default could not tell the two
#: apart, since both would look identical to the function.
_AUTHOR_UNSET = object()


def _ready_for_deviations_readback(tmp_path: Path, *, author=_AUTHOR_UNSET) -> Path:
    """A post-cutoff Demo_ck: passing [checks], a clean committed freeze, and a
    DEVIATIONS.md template on disk -- grantable except for fix round 1's new
    DEVIATIONS.readback.toml requirement, which every test below exercises.
    `_grant_campaign` already gives the node an `[author]` block by default (fix round
    2); passing *author* here overrides it with a specific one (so a self-read-back check
    has something chosen to compare against), and passing `author=None` explicitly strips
    it off entirely (fix round 2's own "no [author] at all" repro)."""
    from test_missions_checks import _art_sha, _grant_campaign, _rec, _with_checks

    root = _grant_campaign(tmp_path, created="2026-10-29")
    p = root / "nodes" / "Demo_ck.toml"
    node = load_node(p)
    if author is not _AUTHOR_UNSET:
        node = dataclasses.replace(node, author=author)
        save_node(node, p)
    _with_checks(root, _rec(_art_sha(root, node)))
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29",
           fingerprints=FROZEN_FP)
    _git_commit(root, "initial freeze")
    deviations_path(root).write_text(DEVIATIONS_TEMPLATE)
    return root


def test_deviations_grant_requires_readback(tmp_path):
    root = _ready_for_deviations_readback(tmp_path)

    with pytest.raises(GateError, match="DEVIATIONS.readback.toml"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"

    write_deviations_readback(root, identity="auditor@example.com",
                              session="auditor-session", date="2026-10-29")

    granted = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"


def test_deviations_readback_stale_sha_blocks_grant(tmp_path):
    root = _ready_for_deviations_readback(tmp_path)
    write_deviations_readback(root, identity="auditor@example.com",
                              session="auditor-session", date="2026-10-29")
    # The ledger changes AFTER the read-back was recorded; its sha256 no longer matches.
    deviations_path(root).write_text(
        "<!-- header -->\n- 2026-10-29 | edited after read-back | drift\n"
    )

    with pytest.raises(GateError, match="changed since its read-back"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_deviations_self_readback_by_identity_blocked(tmp_path):
    author = Author(identity="author@example.com", session="author-session", date="2026-10-29")
    root = _ready_for_deviations_readback(tmp_path, author=author)
    # Same identity as the author, a DIFFERENT session: still a self-audit.
    write_deviations_readback(root, identity="author@example.com",
                              session="someone-elses-session", date="2026-10-29")

    with pytest.raises(GateError, match="own author"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_deviations_self_readback_by_session_blocked(tmp_path):
    author = Author(identity="author@example.com", session="author-session", date="2026-10-29")
    root = _ready_for_deviations_readback(tmp_path, author=author)
    # Same session as the author, a DIFFERENT identity: still a self-audit.
    write_deviations_readback(root, identity="someone-else@example.com",
                              session="author-session", date="2026-10-29")

    with pytest.raises(GateError, match="own author"):
        grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                     session="gate-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_deviations_readback_independent_of_author_passes(tmp_path):
    author = Author(identity="author@example.com", session="author-session", date="2026-10-29")
    root = _ready_for_deviations_readback(tmp_path, author=author)
    write_deviations_readback(root, identity="auditor@example.com",
                              session="auditor-session", date="2026-10-29")

    granted = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"


def test_cli_deviations_readback_writes_file(tmp_path, capsys):
    mroot = tmp_path / "missions"
    root = mroot / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")
    deviations_path(root).write_text(DEVIATIONS_TEMPLATE)

    rc = main(["mission", "--missions-root", str(mroot), "deviations-readback", "demo",
              "--identity", "auditor@example.com", "--session", "auditor-session"])
    assert rc == 0
    assert deviations_readback_path(root).exists()
    assert "read back" in capsys.readouterr().out


def test_cli_deviations_readback_refuses_malformed_ledger(tmp_path, capsys):
    mroot = tmp_path / "missions"
    root = mroot / "demo"
    _campaign(root)
    deviations_path(root).write_text("N/A\n")

    rc = main(["mission", "--missions-root", str(mroot), "deviations-readback", "demo",
              "--identity", "auditor@example.com", "--session", "auditor-session"])
    assert rc == 1
    assert "DEVIATIONS.md" in capsys.readouterr().out
    assert not deviations_readback_path(root).exists()


# ---------------------------------------------------------------------------
# Step 5 Task 3, fix round 1 (c): a deviation cannot be dated in the future.
# ---------------------------------------------------------------------------

def test_future_dated_entry_rejected():
    with pytest.raises(ValueError, match="is after today"):
        parse_deviations("<!-- header -->\n- 2026-12-01 | future thing | why\n",
                         today=datetime.date(2026, 10, 30))


def test_entry_dated_today_is_allowed():
    assert parse_deviations("<!-- header -->\n- 2026-10-30 | today's thing | why\n",
                            today=datetime.date(2026, 10, 30)) == [
        {"date": "2026-10-30", "what": "today's thing", "why": "why"},
    ]


# ---------------------------------------------------------------------------
# Step 5 Task 3, fix round 2 (Ruling 13): a post-cutoff node with no [author] block
# silently defeats BOTH independent-read-back checks (the node-level
# `readback_is_self_audit` and `deviations_grant_problem`'s own auditor check) -- refuse
# the grant outright instead.
# ---------------------------------------------------------------------------

def test_post_cutoff_grant_without_author_refused(tmp_path):
    """The reviewer's exact repro: with no [author] block at all, a single identity can
    write the read-back AND perform the grant, and neither self-audit check has anything
    to compare it against -- so, before this fix, nothing refused it."""
    root = _ready_for_deviations_readback(tmp_path, author=None)
    write_deviations_readback(root, identity="solo@example.com", session="solo-session",
                              date="2026-10-29")

    with pytest.raises(GateError, match=r"\[author\]"):
        grant_status(load_campaign(root), "Demo_ck", identity="solo@example.com",
                     session="solo-session")
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"
    assert "[author]" in deviations_grant_problem(root, load_node(root / "nodes" / "Demo_ck.toml"))


def test_pre_cutoff_grant_without_author_unchanged(tmp_path):
    """The new [author]-required check is scoped to post-cutoff nodes only
    (`checks_required`); a pre-cutoff node with no [author] block must grant exactly as it
    always has."""
    from test_missions_checks import _grant_campaign

    root = _grant_campaign(tmp_path, created="2026-10-01")  # pre-cutoff
    p = root / "nodes" / "Demo_ck.toml"
    save_node(dataclasses.replace(load_node(p), author=None), p)

    granted = grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                           session="gate-session")
    assert granted.status == "proved"


# ---------------------------------------------------------------------------
# Step 5 Task 4: the provenance-header lint (spec 7.4).
#
# A `.lean` file is "ported" if its first 30 lines carry a `ported`/`adapted`/`copied
# from` mention inside a Lean comment, or if it is named in `<root>/PORTED.toml`'s
# `files = [...]`. Every ported file must then also carry, in its first 30 lines, a
# line matching `^-- Provenance: repo=... file=... commit=<40 lowercase hex>$`.
# `provenance_problems` is imported locally per test (rather than at module scope) so
# this RED stage fails on the missing behaviour itself -- an ImportError raised inside
# the test body -- without breaking collection of every other test already in this
# file.
# ---------------------------------------------------------------------------

def test_ported_without_header_flagged(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem foo : True := trivial\n"
    )
    problems = provenance_problems(root)
    assert any("Foo.lean" in p for p in problems)


def test_header_ok(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "-- Provenance: repo=upstream file=Bar.lean commit=" + "a" * 40 + "\n"
        "theorem foo : True := trivial\n"
    )
    assert provenance_problems(root) == []


def test_short_commit_rejected(tmp_path):
    """A 7-hex commit (the common 'short SHA' people paste by habit) is not 40
    lowercase hex digits, so the header does not satisfy spec 7.4 even though a line
    shaped like one is present."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "-- Provenance: repo=upstream file=Bar.lean commit=abc1234\n"
        "theorem foo : True := trivial\n"
    )
    problems = provenance_problems(root)
    assert any("Foo.lean" in p for p in problems)


def test_late_mention_not_ported(tmp_path):
    """A 'ported from' mention past line 30 does not make the file "ported" at all --
    only the first 30 lines count -- so no header is required and nothing is flagged."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    lines = [f"-- line {i}\n" for i in range(1, 200)]
    lines.append("-- adapted from upstream/Bar.lean\n")
    (root / "Foo.lean").write_text("".join(lines))
    assert provenance_problems(root) == []


def test_ported_toml_listed_file_needs_header(tmp_path):
    """A file named in PORTED.toml is ported regardless of whether it carries its own
    'ported from' mention -- it still needs the provenance header."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text("theorem foo : True := trivial\n")
    (root / "PORTED.toml").write_text('files = ["Foo.lean"]\n')
    problems = provenance_problems(root)
    assert any("Foo.lean" in p for p in problems)


def test_ported_toml_missing_file(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "PORTED.toml").write_text('files = ["Missing.lean"]\n')
    problems = provenance_problems(root)
    assert any("Missing.lean" in p and "does not exist" in p for p in problems)


def test_cli_exit_codes(tmp_path, capsys):
    root = tmp_path
    (root / "Clean.lean").write_text("theorem foo : True := trivial\n")
    rc = main(["lint-provenance", str(root)])
    assert rc == 0
    capsys.readouterr()

    (root / "Bad.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem bar : True := trivial\n"
    )
    rc = main(["lint-provenance", str(root)])
    assert rc == 1
    assert "Bad.lean" in capsys.readouterr().out


def test_verify_campaign_includes_provenance_problems_post_cutoff(tmp_path):
    """`verify_campaign` wires `provenance_problems` in for a campaign frozen ON OR
    AFTER `CUTOFF` -- read through `campaign_is_post_cutoff`'s guarded loader, never
    FREEZE.toml directly."""
    from telperion.missions.verify import verify_campaign

    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-29")  # >= CUTOFF
    (root / "Bad.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem bar : True := trivial\n"
    )
    report = verify_campaign(root)
    assert any("Bad.lean" in e for e in report.errors)


def test_verify_campaign_excludes_provenance_problems_pre_cutoff(tmp_path):
    """The same lint is NOT applied to a campaign frozen BEFORE `CUTOFF` -- a legacy
    campaign is not retroactively held to a requirement that did not exist yet when its
    files were ported."""
    from telperion.missions.verify import verify_campaign

    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")  # < CUTOFF
    (root / "Bad.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem bar : True := trivial\n"
    )
    report = verify_campaign(root)
    assert not any("Bad.lean" in e for e in report.errors)


# ---------------------------------------------------------------------------
# Step 5 Task 4, fix round 1 (Controller Ruling 14, review of commit 7a7df30).
#
# Critical: a `.lean` file reachable only through a symlink -- to a file inside the
# campaign root or (the reviewer's exploit) entirely outside it -- that is NOT declared
# in PORTED.toml used to be completely invisible to the lint: `_read_lean_head_safe`
# refuses to follow it, so the auto-detection scan in `ported_files` simply `continue`d
# past it, and since it was never added to `found`, `provenance_problems`'s own loop
# never visited it either. `provenance_problems` now reports EVERY `.lean` symlink the
# walk meets, unconditionally, whether or not it turns out to be "ported" at all.
#
# Minors (same round): multiple provenance-header-shaped lines in the leading block;
# `lint-provenance` on a missing/non-directory path; PORTED.toml's escape rejections,
# each exercised directly rather than only by inspection; CRLF line endings and
# trailing whitespace on an otherwise-valid header.
# ---------------------------------------------------------------------------

def test_symlinked_lean_file_outside_root_flagged(tmp_path):
    """The reviewer's exact repro. A `.lean` file only the auto-scan would ever see,
    reached through a symlink pointing OUTSIDE the campaign root and never declared in
    PORTED.toml, must be flagged -- and flagged exactly once, regardless of what its
    (unreadable) content actually is."""
    from telperion.missions.process import provenance_problems

    root = tmp_path / "campaign"
    root.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "Vendor.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem v : True := trivial\n"
    )
    (root / "VendorAlias.lean").symlink_to(outside / "Vendor.lean")

    problems = provenance_problems(root)
    hits = [p for p in problems if "VendorAlias.lean" in p]
    assert len(hits) == 1
    assert "symlink" in hits[0]


def test_symlinked_lean_file_inside_root_also_flagged(tmp_path):
    """The same unconditional report applies to a `.lean` symlink whose target stays
    INSIDE the campaign root -- the auto-scan still cannot read through it to decide
    whether it is ported, so it is flagged the same way."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Real.lean").write_text("theorem r : True := trivial\n")
    (root / "Alias.lean").symlink_to(root / "Real.lean")

    problems = provenance_problems(root)
    hits = [p for p in problems if "Alias.lean" in p]
    assert len(hits) == 1
    assert "symlink" in hits[0]


def test_multiple_provenance_headers_flagged(tmp_path):
    """Two provenance-header-shaped lines in the same leading block are a problem even
    when one of them is individually valid: spec 7.4 asks for exactly one, and
    accepting the first (or any) while silently ignoring a second, different header
    would mask a confusing or contradictory pair from a human reviewer."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "-- Provenance: repo=upstream file=Bar.lean commit=" + "a" * 40 + "\n"
        "-- Provenance: repo=evil file=Evil.lean commit=short1234\n"
        "theorem foo : True := trivial\n"
    )
    problems = provenance_problems(root)
    assert any("multiple provenance headers" in p for p in problems)


def test_cli_lint_provenance_missing_dir_exit_2(tmp_path, capsys):
    missing = tmp_path / "does-not-exist"
    rc = main(["lint-provenance", str(missing)])
    assert rc == 2
    assert str(missing) in capsys.readouterr().out


def test_cli_lint_provenance_not_a_directory_exit_2(tmp_path, capsys):
    plain_file = tmp_path / "plain.txt"
    plain_file.write_text("not a directory\n")
    rc = main(["lint-provenance", str(plain_file)])
    assert rc == 2
    assert str(plain_file) in capsys.readouterr().out


def test_ported_toml_rejects_dotdot(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "PORTED.toml").write_text('files = ["../x.lean"]\n')
    problems = provenance_problems(root)
    assert any("../x.lean" in p and "contains" in p for p in problems)


def test_ported_toml_rejects_absolute_path(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "PORTED.toml").write_text('files = ["/etc/passwd"]\n')
    problems = provenance_problems(root)
    assert any("/etc/passwd" in p and "absolute" in p for p in problems)


def test_ported_toml_rejects_symlink_out_via_file(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path / "campaign"
    root.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "Secret.lean").write_text("theorem s : True := trivial\n")
    (root / "link.lean").symlink_to(outside / "Secret.lean")
    (root / "PORTED.toml").write_text('files = ["link.lean"]\n')

    problems = provenance_problems(root)
    assert any("link.lean" in p and "outside" in p for p in problems)


def test_ported_toml_rejects_symlink_out_via_dir_component(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path / "campaign"
    root.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "X.lean").write_text("theorem x : True := trivial\n")
    (root / "vendored").symlink_to(outside)
    (root / "PORTED.toml").write_text('files = ["vendored/X.lean"]\n')

    problems = provenance_problems(root)
    assert any("vendored/X.lean" in p and "outside" in p for p in problems)


def test_ported_toml_duplicate_entry_deduped(tmp_path):
    from telperion.missions.process import ported_files, provenance_problems

    root = tmp_path
    (root / "Foo.lean").write_text("theorem foo : True := trivial\n")
    (root / "PORTED.toml").write_text('files = ["Foo.lean", "Foo.lean"]\n')

    assert ported_files(root) == [Path("Foo.lean")]
    problems = provenance_problems(root)
    assert sum(1 for p in problems if "Foo.lean" in p and "provenance header" in p) == 1


def test_ported_toml_rejects_non_string_entry(tmp_path):
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "PORTED.toml").write_text('files = ["Foo.lean", 5]\n')
    problems = provenance_problems(root)
    assert any("not a list of strings" in p for p in problems)


def test_crlf_header_with_trailing_whitespace_accepted(tmp_path):
    """A CRLF-terminated file, and trailing whitespace after the commit token, must
    not make an otherwise-valid header fail closed."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    content = (
        "-- ported from upstream/Bar.lean\r\n"
        "-- Provenance: repo=upstream file=Bar.lean commit=" + "a" * 40 + "   \r\n"
        "theorem foo : True := trivial\r\n"
    )
    (root / "Foo.lean").write_bytes(content.encode("utf-8"))
    assert provenance_problems(root) == []


# ---------------------------------------------------------------------------
# Step 5 Task 4, fix round 2 (Controller Ruling 15, review of commit 99fbf20).
#
# Fix round 1 closed the symlinked-FILE bypass, but the same evasion still works one
# level up: `_walk_lean_files` never follows a symlinked DIRECTORY (`os.walk`'s own
# `followlinks=False`), but it did so SILENTLY -- a `.lean` file reachable only through
# one was simply never walked into at all, so it never even reached the symlinked-FILE
# check fix round 1 added. `provenance_problems` now reports every symlinked directory
# the walk meets too, excluding `.git/`, `.lake/`, build dirs (and anything nested
# under one, since the walk never descends into those at all either way).
# ---------------------------------------------------------------------------

def test_symlinked_directory_outside_root_flagged(tmp_path):
    """The lead's exact repro: a `.lean` file hidden behind a symlinked DIRECTORY
    pointing OUTSIDE the campaign root, not declared in PORTED.toml. The directory
    symlink itself must be flagged; the file behind it, never walked into, is not
    (and cannot be) separately named."""
    from telperion.missions.process import provenance_problems

    root = tmp_path / "campaign"
    root.mkdir()
    outside = tmp_path / "out"
    outside.mkdir()
    (outside / "Vendor.lean").write_text(
        "-- ported from upstream/Bar.lean\n"
        "theorem v : True := trivial\n"
    )
    (root / "vendor").symlink_to(outside, target_is_directory=True)

    problems = provenance_problems(root)
    hits = [p for p in problems if p.startswith("vendor/")]
    assert len(hits) == 1
    assert "symlinked directory" in hits[0]
    assert not any("Vendor.lean" in p for p in problems)


def test_symlinked_directory_inside_root_flagged(tmp_path):
    """The same report applies to a directory symlink whose target stays INSIDE the
    campaign root -- the walk still never follows it, so it is flagged the same way."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / "real_dir").mkdir()
    (root / "real_dir" / "Foo.lean").write_text("theorem foo : True := trivial\n")
    (root / "alias_dir").symlink_to(root / "real_dir", target_is_directory=True)

    problems = provenance_problems(root)
    hits = [p for p in problems if p.startswith("alias_dir/")]
    assert len(hits) == 1
    assert "symlinked directory" in hits[0]


def test_symlinked_directory_under_lake_not_reported(tmp_path):
    """A symlinked directory nested under `.lake/` must stay silent -- the walk never
    descends into `.lake/` at all, skip-listed or not, so it never even sees it."""
    from telperion.missions.process import provenance_problems

    root = tmp_path
    (root / ".lake").mkdir()
    outside = tmp_path / "cache"
    outside.mkdir()
    (root / ".lake" / "vendor").symlink_to(outside, target_is_directory=True)

    problems = provenance_problems(root)
    assert not any("vendor" in p for p in problems)


# ---------------------------------------------------------------------------
# Step 5 Task 6: frozen statement fingerprints (FREEZE.toml [fingerprints]) -- recorded by
# freeze/unfreeze, kept by the same git-history walk as [statements], and read by the gate.
# ---------------------------------------------------------------------------

FP_A, FP_B, FP_C = "a" * 64, "b" * 64, "c" * 64


def _frozen_with_fps(root: Path, fps=None, date: str = "2026-10-29") -> None:
    _campaign(root)
    _git_init(root)
    freeze(root, identity="alice@example.com", session="s1", date=date,
           fingerprints={"Node_A": FP_A, "Node_B": FP_B} if fps is None else fps)
    _git_commit(root, "initial freeze")


def test_freeze_records_fingerprints_and_frozen_fingerprint_reads_them(tmp_path):
    from telperion.missions.process import frozen_fingerprint
    root = tmp_path / "demo"
    _frozen_with_fps(root)
    text = freeze_path(root).read_text()
    assert '[fingerprints]\n"Node_A" = "' + FP_A + '"\n"Node_B" = "' + FP_B + '"' in text
    doc = _load_freeze_for_test(root)
    assert doc["fingerprints"] == {"Node_A": FP_A, "Node_B": FP_B}
    nodes = load_campaign(root).nodes
    assert frozen_fingerprint(root, nodes["Node_A"]) == FP_A
    assert freeze_problems(root) == []


def test_freeze_without_fingerprints_writes_no_table(tmp_path):
    from telperion.missions.process import frozen_fingerprint
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")
    assert "[fingerprints]" not in freeze_path(root).read_text()
    assert frozen_fingerprint(root, load_campaign(root).nodes["Node_A"]) is None


@pytest.mark.parametrize("fps,why", [({"Nope": FP_A}, "no statement file"),
                                     ({"Node_A": "A" * 64}, "64 lowercase hex"),
                                     ({"Node_A": "a" * 63}, "64 lowercase hex")])
def test_freeze_refuses_bad_fingerprints_and_writes_nothing(tmp_path, fps, why):
    root = tmp_path / "demo"
    _campaign(root)
    with pytest.raises(ValueError, match=why):
        freeze(root, identity="alice@example.com", session="s1", date="2026-10-29", fingerprints=fps)
    assert not freeze_path(root).exists()


def test_unfreeze_records_exactly_the_given_fingerprints(tmp_path):
    root = tmp_path / "demo"
    _frozen_with_fps(root)
    doc = unfreeze(root, author="alice@example.com", reason="r", readback_identity="bob@example.com",
                   date="2026-10-30", fingerprints={"Node_A": FP_C})
    assert doc["fingerprints"] == {"Node_A": FP_C}                  # never carried forward
    _git_commit(root, "unfreeze with a new fingerprint")
    assert freeze_problems(root) == []                              # a version bump may change them
    doc = unfreeze(root, author="alice@example.com", reason="r2", readback_identity="bob@example.com",
                   date="2026-10-30")
    assert "fingerprints" not in _load_freeze_for_test(root) and doc["fingerprints"] == {}


def test_freeze_problems_flags_hand_edited_fingerprint_entries(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01",
           fingerprints={"Node_A": FP_A})
    _hand_edit_freeze(root, lambda d: d["fingerprints"].update({"Ghost": FP_B, "Node_B": "XYZ"}))
    problems = freeze_problems(root)
    assert any("'Ghost', which has no [statements] entry" in p for p in problems), problems
    assert any("'Node_B' that is not 64 lowercase hex" in p for p in problems), problems


def test_freeze_with_a_non_table_fingerprints_is_untrusted(tmp_path):
    root = tmp_path / "demo"
    _campaign(root)
    freeze(root, identity="alice@example.com", session="s1", date="2026-10-01")
    freeze_path(root).write_text('fingerprints = "x"\n' + freeze_path(root).read_text())   # a top-level key
    assert freeze_problems(root) == [
        "FREEZE.toml has a `fingerprints` that is not a table of string fingerprints; refusing to "
        "trust it."]


@pytest.mark.parametrize("mutate,why", [
    (lambda d: d["fingerprints"].__setitem__("Node_A", FP_C), "changed or were removed without a version bump"),
    (lambda d: d["fingerprints"].pop("Node_A"), "changed or were removed without a version bump"),
])
def test_freeze_history_fingerprint_change_at_unchanged_version_flagged(tmp_path, mutate, why):
    root = tmp_path / "demo"
    _frozen_with_fps(root)
    _hand_edit_freeze(root, mutate)
    _git_commit(root, "rewrite a frozen fingerprint")
    problems = freeze_problems(root)
    assert any("statement fingerprint(s) 'Node_A'" in p and why in p for p in problems), problems


def test_freeze_history_fingerprint_added_for_a_frozen_node_flagged(tmp_path):
    """A fingerprint appearing later, at the same version, for a node frozen earlier: whoever
    adds it chooses what a later [checks] record must match. Refused, committed or not."""
    root = tmp_path / "demo"
    _frozen_with_fps(root, fps={})
    _hand_edit_freeze(root, lambda d: d.__setitem__("fingerprints", {"Node_A": FP_A}))
    problems = freeze_problems(root)
    assert any("'Node_A'" in p and "added for already-frozen node(s)" in p for p in problems), problems
    _git_commit(root, "add a fingerprint without a version bump")
    assert any("added for already-frozen node(s)" in p for p in freeze_problems(root))


def test_freeze_history_fingerprint_added_with_its_new_node_allowed(tmp_path):
    """The [statements] rule's exception, mirrored: a node new in the transition may arrive with
    its fingerprint."""
    from telperion.missions.process import freeze_history_problems
    root = tmp_path / "demo"
    _frozen_with_fps(root, fps={})
    _hand_edit_freeze(root, lambda d: (d["statements"].__setitem__("Node_C", "0" * 64),
                                       d.__setitem__("fingerprints", {"Node_C": FP_C})))
    assert freeze_history_problems(root) == []


def test_freeze_history_fingerprints_changed_by_unfreeze_clean(tmp_path):
    root = tmp_path / "demo"
    _frozen_with_fps(root)
    unfreeze(root, author="alice@example.com", reason="re-fingerprint", readback_identity="bob@example.com",
             date="2026-10-30", fingerprints={"Node_A": FP_C, "Node_B": FP_B})
    _git_commit(root, "unfreeze")
    assert freeze_problems(root) == []


def _stmt_target(tmp_path: Path, body: str):
    from telperion.missions.process import statement_fingerprint_target
    root = tmp_path / "demo"
    manifest = _campaign(root, names=("Node_A",))
    node = load_campaign(root).nodes["Node_A"]
    write_statement(root, node, body, manifest)
    return statement_fingerprint_target(root, load_campaign(root).nodes["Node_A"])


@pytest.mark.parametrize("body,want", [
    ("import Mathlib\n\ntheorem thm_a : 1 + 1 = 2", ("thm_a", "type")),
    ("lemma thm_a' : True", ("thm_a'", "type")),
    ("import Mathlib\n\ndef Stmt : Prop := ∀ n : ℕ, n + 0 = n", ("Stmt", "value")),
    ("def Stmt.{u} : Prop := ∀ (α : Sort u) (a : α), a = a", ("Stmt", "value")),
    ("noncomputable abbrev Stmt:Prop := True", ("Stmt", "value")),
    # the LAST declaration, namespace-qualified; comments and strings blanked
    ("namespace Demo\ndef helper : ℕ := 3\n-- theorem fake : False\ntheorem main : helper = 3 := by sorry\nend Demo",
     ("Demo.main", "type")),
    ("namespace Demo\ntheorem main : True := by sorry\nend Demo\ndef S : Prop := True", ("Demo.main", "type")),
    ("namespace Demo\ntheorem _root_.top : True", ("top", "type")),
    ('def s : String := "\ntheorem fake : False := sorry\n"\ndef S : Prop := True', ("S", "value")),
    # a theorem wins over a later def: the frozen fingerprint is of the theorem the gate's needle is read from
    ("def S : Prop := True\ntheorem main : S := by sorry\ndef after : Prop := False", ("main", "type")),
    ("theorem poly.{u} (α : Sort u) (a : α) : a = a", ("poly", "type")),
])
def test_statement_fingerprint_target(tmp_path, body, want):
    assert _stmt_target(tmp_path, body) == want


@pytest.mark.parametrize("body,why", [
    ("private theorem t : True", "private"),
    ("def «my stmt» : Prop := True", "not a plain dotted Lean identifier"),
    ("example : True", "declares no theorem, lemma, def or abbrev"),
    # the gate's statement_decl does not blank strings, so it would read `fake` as the statement
    ('theorem real : True\ndef s : String := " theorem fake : False"', "ambiguous statement file"),
])
def test_statement_fingerprint_target_refusals(tmp_path, body, why):
    with pytest.raises(ValueError, match=why):
        _stmt_target(tmp_path, body)


def test_compute_statement_fingerprints_calls_lean_per_node_in_its_mode(tmp_path):
    from telperion.missions.process import compute_statement_fingerprints
    root = tmp_path / "demo"
    manifest = _campaign(root)
    write_statement(root, load_campaign(root).nodes["Node_B"], "def StmtB : Prop := True", manifest)
    calls = []

    def fake(project, text, target, *, mode, **kw):
        calls.append((project, target, mode, "DO NOT EDIT" in text, kw))
        return {"thm_Node_A": FP_A, "StmtB": FP_B}[target]

    out = compute_statement_fingerprints(root, fingerprint_text=fake, timeout=7)
    assert out == {"Node_A": FP_A, "Node_B": FP_B}
    assert calls == [(root / "lean", "thm_Node_A", "type", True, {"timeout": 7}),
                     (root / "lean", "StmtB", "value", True, {"timeout": 7})]

    def broken(project, text, target, *, mode, **kw):
        raise ValueError("refused (...): StmtB value-mode-not-prop")
    with pytest.raises(ValueError, match="node 'Node_A': statement fingerprint of 'thm_Node_A' \\(type mode\\)"):
        compute_statement_fingerprints(root, fingerprint_text=broken)


def test_cli_freeze_and_unfreeze_with_fingerprints(tmp_path, capsys, monkeypatch):
    from telperion.missions import process as proc
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")
    seen = []

    def fake(root, **kw):
        seen.append(kw)
        return {"Node_A": FP_A, "Node_B": FP_B}
    monkeypatch.setattr(proc, "compute_statement_fingerprints", fake)
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo", "--identity", "alice@example.com",
               "--session", "s1", "--fingerprints", "--trusted-env", "/pinned", "--timeout", "9", "--wrapper", ""])
    out = capsys.readouterr().out
    assert rc == 0 and "2 statement fingerprint(s) recorded" in out, out
    assert seen == [{"trusted_env": Path("/pinned"), "wrapper": [], "timeout": 9}]
    assert _load_freeze_for_test(mroot / "demo")["fingerprints"] == {"Node_A": FP_A, "Node_B": FP_B}

    # an already-frozen campaign is refused before any Lean runs
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo", "--identity", "alice@example.com",
               "--session", "s1", "--fingerprints"])
    assert rc == 1 and "already frozen" in capsys.readouterr().out and len(seen) == 1

    # so is a self-read-back unfreeze
    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo", "--author", "alice@example.com",
               "--reason", "r", "--readback-identity", "Alice@example.com", "--fingerprints"])
    assert rc == 1 and "readback_identity" in capsys.readouterr().out and len(seen) == 1

    rc = main(["mission", "--missions-root", str(mroot), "unfreeze", "demo", "--author", "alice@example.com",
               "--reason", "r", "--readback-identity", "bob@example.com", "--fingerprints"])
    assert rc == 0 and "2 statement fingerprint(s) recorded" in capsys.readouterr().out and len(seen) == 2
    assert _load_freeze_for_test(mroot / "demo")["fingerprints"] == {"Node_A": FP_A, "Node_B": FP_B}


def test_cli_freeze_fingerprint_failure_writes_nothing(tmp_path, capsys, monkeypatch):
    from telperion.missions import process as proc
    mroot = tmp_path / "missions"
    _campaign(mroot / "demo")

    def fail(root, **kw):
        raise ValueError("node 'Node_B': statement fingerprint of 'thm_Node_B' (type mode) failed: refused")
    monkeypatch.setattr(proc, "compute_statement_fingerprints", fail)
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo", "--identity", "alice@example.com",
               "--session", "s1", "--fingerprints"])
    assert rc == 1 and "Node_B" in capsys.readouterr().out
    assert not freeze_path(mroot / "demo").exists()
