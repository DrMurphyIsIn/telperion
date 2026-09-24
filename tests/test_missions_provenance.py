"""Provenance governance (2026-09-23): authorship, independent read-backs, grant digests.

What these pin, in the order a node lives through it:

  * `mission add` records `[author] {identity, session, date}` and refuses without both;
  * `mission audit` records a STRUCTURED auditor, refuses the author's session or identity,
    refuses a read-back that is too short or only the title, and writes nothing on refusal;
  * `mission grant` writes `[grant]` with the artifact/statement digests, gate version and
    who ran it, and refuses a hand-written self-audit;
  * `mission verify` fails when an artifact or statement changes under a `[grant]` block,
    fails a proved node whose read-back is a self-audit, and warns when a recorded
    Comparator verdict no longer matches the artifact;
  * the migration marks legacy read-backs `unverified`, idempotently, changing no status;
  * `mission provenance-report` lists the proved nodes nobody independent has vouched for;
  * the schema round-trips the new tables and carries a legacy file through unchanged.

conjecture1_proved = False.
"""
from __future__ import annotations

import dataclasses
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions import provenance as prov  # noqa: E402
from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    Author, ComparatorRecord, Grant, MissionManifest, Node, Proof, Readback, SchemaError,
    dumps_toml, load_node, loads_toml, save_node,
)
from telperion.missions.statements import write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status, verify_campaign  # noqa: E402

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"

LONG = (
    "For every natural number n the equation n = n holds; the statement has no hypotheses, "
    "quantifies over the naturals only, and its conclusion is a closed propositional equality "
    "with no definitional unfolding that could make it vacuous. Rendered by the auditor."
)

AUTHOR = dict(identity="author@example.test", session="s-author")
AUDITOR = dict(identity="auditor@example.test", session="s-auditor")
GATE = dict(identity="gate@example.test", session="s-gate")


@pytest.fixture(autouse=True)
def _no_ambient_provenance(monkeypatch):
    """Every identity in these tests is explicit: no session from the environment and no
    git identity from the developer's global config."""
    monkeypatch.delenv(prov.SESSION_ENV, raising=False)
    monkeypatch.setattr(prov, "git_identity", lambda cwd=None: "")


def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal", title="Demo Campaign", description="synthetic",
        goal_node="Demo_goal", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )


def _demo(tmp_path: Path) -> tuple[Path, Path]:
    mroot = tmp_path / "missions"
    mroot.mkdir()
    croot = mroot / "demo"
    shutil.copytree(DEMO_FIXTURE, croot)
    return mroot, croot


def _cli(mroot: Path, *args: str) -> int:
    return main(["mission", "--missions-root", str(mroot), *args])


def _add(mroot: Path, name="New.lemma_x", **who) -> int:
    who = {**AUTHOR, **who}
    return _cli(mroot, "add", "demo", name, "--title", "New lemma X", "--kind", "lemma",
                "--statement", "import Mathlib\ntheorem new_x : 1 = 1",
                "--identity", who["identity"], "--session", who["session"])


def _audit(mroot: Path, slug="New_lemma_x", text=LONG, **who) -> int:
    who = {**AUDITOR, **who}
    return _cli(mroot, "audit", slug, "--campaign", "demo", "--text", text,
                "--identity", who["identity"], "--session", who["session"])


def _open_with_proof(croot: Path, slug: str, statement: str, artifact_text: str,
                     author=None, readback=None) -> Node:
    """An open node whose statement file and artifact are on disk, ready to grant."""
    node = Node(
        name=slug.replace("_", ".", 1), title=f"title of {slug}", kind="lemma", status="open",
        depends_on=(), statement_module=f"Statements.{slug}",
        proof=Proof(f"proof/{slug}.lean", "lean_module", "direct", False),
        readback=readback or Readback(text=LONG, auditor="someone", date="2026-09-23"),
        author=author, created="2026-09-23", updated="2026-09-23",
    )
    save_node(node, croot / "nodes" / f"{slug}.toml")
    # #617: every statement file must open with an `import` line (the battery checks it).
    write_statement(croot, node, "import Mathlib\n" + statement, _manifest())
    art = croot / "proof" / f"{slug}.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text(artifact_text)
    return node


# ---------------------------------------------------------------------------
# add: authorship
# ---------------------------------------------------------------------------

def test_add_records_author(tmp_path):
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    node = load_node(croot / "nodes" / "New_lemma_x.toml")
    assert node.author is not None
    assert (node.author.identity, node.author.session) == (AUTHOR["identity"], AUTHOR["session"])
    assert node.author.date == node.created
    text = (croot / "nodes" / "New_lemma_x.toml").read_text()
    assert "[author]" in text


@pytest.mark.parametrize("missing", ["identity", "session"])
def test_add_refuses_without_identity_or_session(tmp_path, missing, capsys):
    mroot, croot = _demo(tmp_path)
    rc = _add(mroot, **{missing: ""})
    assert rc == 1
    assert missing in capsys.readouterr().out
    assert not (croot / "nodes" / "New_lemma_x.toml").exists()


def test_add_session_from_environment(tmp_path, monkeypatch):
    mroot, croot = _demo(tmp_path)
    monkeypatch.setenv(prov.SESSION_ENV, "env-session")
    rc = _cli(mroot, "add", "demo", "Env.lemma", "--title", "t", "--kind", "lemma",
              "--statement", "import Mathlib\ntheorem e : 1 = 1", "--identity", "a@b")
    assert rc == 0
    assert load_node(croot / "nodes" / "Env_lemma.toml").author.session == "env-session"


# ---------------------------------------------------------------------------
# audit: structured, independent, substantive
# ---------------------------------------------------------------------------

def test_audit_records_structured_auditor_and_independence(tmp_path):
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    assert _audit(mroot) == 0
    node = load_node(croot / "nodes" / "New_lemma_x.toml")
    assert node.status == "open"
    rb = node.readback
    assert (rb.auditor_identity, rb.auditor_session) == (AUDITOR["identity"], AUDITOR["session"])
    assert rb.independence == "independent"
    assert rb.auditor == AUDITOR["identity"]  # label defaults to the identity


def test_audit_refuses_same_session(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    rc = _audit(mroot, session=AUTHOR["session"])
    assert rc == 1
    assert "author's session" in capsys.readouterr().out
    node = load_node(croot / "nodes" / "New_lemma_x.toml")
    assert node.readback is None, "a refused self-audit must leave no trace"
    assert node.status == "draft"


def test_audit_refuses_same_identity_even_from_another_session(tmp_path, capsys):
    """A subagent of the author runs under the author's git identity. That is the 2026-09-19
    to 09-22 pattern this rule exists for."""
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    rc = _audit(mroot, identity=AUTHOR["identity"].upper(), session="s-subagent")
    assert rc == 1
    assert "author's identity" in capsys.readouterr().out
    assert load_node(croot / "nodes" / "New_lemma_x.toml").readback is None


def test_audit_refuses_short_text(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    assert _audit(mroot, text="Lemma X says 1 = 1.") == 1
    assert "characters" in capsys.readouterr().out
    assert load_node(croot / "nodes" / "New_lemma_x.toml").readback is None


def test_audit_refuses_title_only(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    long_title = ("A statement whose title is long enough on its own to clear the length "
                  "floor, so that a lazy read-back could simply repeat it and look substantive")
    rc = _cli(mroot, "add", "demo", "Titled.lemma", "--title", long_title, "--kind", "lemma",
              "--statement", "import Mathlib\ntheorem titled : 1 = 1", "--identity", AUTHOR["identity"],
              "--session", AUTHOR["session"])
    assert rc == 0
    assert _audit(mroot, slug="Titled_lemma", text=long_title.upper() + "!") == 1
    assert "repeats the node title" in capsys.readouterr().out
    assert load_node(croot / "nodes" / "Titled_lemma.toml").readback is None


def test_audit_refuses_without_session(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    assert _add(mroot) == 0
    assert _audit(mroot, session="") == 1
    assert "session is empty" in capsys.readouterr().out


def test_audit_on_legacy_node_is_unverified_with_warning(tmp_path, capsys):
    """A node with no [author] block cannot be checked; the read-back is recorded but
    honestly labelled."""
    mroot, croot = _demo(tmp_path)
    assert _audit(mroot, slug="Demo_lemma_b") == 0   # fixture node: draft, no author
    out = capsys.readouterr().out
    assert "no [author] block" in out
    rb = load_node(croot / "nodes" / "Demo_lemma_b.toml").readback
    assert rb.independence == "unverified"
    assert rb.auditor_session == AUDITOR["session"]


# ---------------------------------------------------------------------------
# grant: the [grant] block and the self-audit refusal
# ---------------------------------------------------------------------------

def test_grant_writes_grant_block_with_digests(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem g_one : 1 = 1"
    _open_with_proof(croot, "G_one", stmt, f"{stmt} := by rfl\n")
    node = grant_status(load_campaign(croot), "G_one", **GATE)
    assert node.status == "proved"
    g = node.grant
    assert g is not None
    assert g.artifact_sha256 == prov.sha256_file(croot / "proof" / "G_one.lean")
    assert g.statement_sha256 == prov.sha256_file(croot / "lean" / "Statements" / "G_one.lean")
    assert g.gate_version == prov.GATE_VERSION
    assert (g.identity, g.session) == (GATE["identity"], GATE["session"])
    on_disk = (croot / "nodes" / "G_one.toml").read_text()
    assert "[grant]" in on_disk and g.artifact_sha256 in on_disk
    assert verify_campaign(croot).ok


def test_grant_requires_identity_and_session(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem g_two : 2 = 2"
    _open_with_proof(croot, "G_two", stmt, f"{stmt} := by rfl\n")
    with pytest.raises(GateError, match="session is empty"):
        grant_status(load_campaign(croot), "G_two", identity="x@y", session="")
    with pytest.raises(GateError, match="identity is empty"):
        grant_status(load_campaign(croot), "G_two", identity="", session="s")
    assert load_node(croot / "nodes" / "G_two.toml").status == "open"


def test_grant_refuses_hand_written_self_audit(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem g_self : 3 = 3"
    author = Author(**AUTHOR, date="2026-09-23")
    rb = Readback(text=LONG, auditor="me", date="2026-09-23",
                  auditor_identity=AUTHOR["identity"], auditor_session="s-other",
                  independence="independent")   # the label lies; the identity does not
    _open_with_proof(croot, "G_self", stmt, f"{stmt} := by rfl\n", author=author, readback=rb)
    with pytest.raises(GateError, match="self-audit"):
        grant_status(load_campaign(croot), "G_self", **GATE)
    assert load_node(croot / "nodes" / "G_self.toml").status == "open"


def test_grant_cli_records_provenance(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem g_cli : 4 = 4"
    _open_with_proof(croot, "G_cli", stmt, f"{stmt} := by rfl\n")
    rc = _cli(mroot, "grant", "G_cli", "--campaign", "demo",
              "--identity", GATE["identity"], "--session", GATE["session"])
    assert rc == 0
    assert load_node(croot / "nodes" / "G_cli.toml").grant.session == GATE["session"]
    # and without a session the CLI refuses
    _open_with_proof(croot, "G_cli2", "theorem g_cli2 : 5 = 5", "theorem g_cli2 : 5 = 5 := by rfl\n")
    assert _cli(mroot, "grant", "G_cli2", "--campaign", "demo", "--identity", "x@y") == 1
    assert load_node(croot / "nodes" / "G_cli2.toml").status == "open"


# ---------------------------------------------------------------------------
# verify: digests, self-audit, comparator staleness
# ---------------------------------------------------------------------------

def test_verify_fails_when_artifact_changes_under_grant(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem v_art : 1 = 1"
    _open_with_proof(croot, "V_art", stmt, f"{stmt} := by rfl\n")
    grant_status(load_campaign(croot), "V_art", **GATE)
    assert verify_campaign(croot).ok
    # Same statement, different proof text: containment still holds, the digest does not.
    (croot / "proof" / "V_art.lean").write_text(f"{stmt} := by decide\n")
    rep = verify_campaign(croot)
    assert not rep.ok
    assert any("has changed since the gate granted it" in e for e in rep.errors)


def test_verify_fails_when_statement_changes_under_grant(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem v_stmt : 1 = 1"
    _open_with_proof(croot, "V_stmt", stmt, f"{stmt} := by rfl\n")
    grant_status(load_campaign(croot), "V_stmt", **GATE)
    sp = croot / "lean" / "Statements" / "V_stmt.lean"
    sp.write_text(sp.read_text() + "\n-- a trailing comment\n")
    rep = verify_campaign(croot)
    assert not rep.ok
    assert any("statement file has changed since the gate granted" in e for e in rep.errors)


def test_verify_fails_proved_self_audit(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem v_self : 1 = 1"
    author = Author(**AUTHOR, date="2026-09-23")
    rb = Readback(text=LONG, auditor="me", date="2026-09-23",
                  auditor_identity="other@x", auditor_session=AUTHOR["session"])
    node = _open_with_proof(croot, "V_self", stmt, f"{stmt} := by rfl\n", author=author, readback=rb)
    # bypass the gate: hand-edit to proved, which is what a self-certifying session would do
    save_node(dataclasses.replace(node, status="proved"), croot / "nodes" / "V_self.toml")
    rep = verify_campaign(croot)
    assert any("self-audit" in e for e in rep.errors)


def test_verify_warns_when_comparator_record_is_stale(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem v_cmp : 1 = 1"
    _open_with_proof(croot, "V_cmp", stmt, f"{stmt} := by rfl\n")
    grant_status(load_campaign(croot), "V_cmp", **GATE)
    rc = _cli(mroot, "comparator-record", "V_cmp", "--campaign", "demo",
              "--run-id", "12345", "--theorem", "v_cmp")
    assert rc == 0
    node = load_node(croot / "nodes" / "V_cmp.toml")
    assert node.comparator.run_id == "12345"
    assert node.comparator.artifact_sha256 == node.grant.artifact_sha256
    assert not any("stale" in w for w in verify_campaign(croot).warnings)
    # regrant after an edit would be needed; here just rewrite the artifact and the grant digest
    (croot / "proof" / "V_cmp.lean").write_text(f"{stmt} := by decide\n")
    n2 = load_node(croot / "nodes" / "V_cmp.toml")
    save_node(dataclasses.replace(n2, grant=dataclasses.replace(
        n2.grant, artifact_sha256=prov.sha256_file(croot / "proof" / "V_cmp.lean"))),
        croot / "nodes" / "V_cmp.toml")
    rep = verify_campaign(croot)
    assert rep.ok
    assert any("stale" in w for w in rep.warnings)


def test_comparator_record_refuses_non_proved(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    rc = _cli(mroot, "comparator-record", "Demo_lemma_a", "--campaign", "demo",
              "--run-id", "1", "--theorem", "x")
    assert rc == 1
    assert "proved" in capsys.readouterr().out


# ---------------------------------------------------------------------------
# requires_ci_job / ci-record (owner ruling 2026-09-24)
# ---------------------------------------------------------------------------

def _ci_node(croot: Path, slug: str, stmt: str, requires: str = "wf.yml:kernel-ladder") -> Node:
    node = _open_with_proof(croot, slug, stmt, f"{stmt} := by rfl\n")
    node = dataclasses.replace(node, requires_ci_job=requires)
    save_node(node, croot / "nodes" / f"{slug}.toml")
    return node


def _ci_record(mroot: Path, slug: str, *, conclusion="success", job="kernel-ladder",
               workflow="wf.yml", run_id="4242") -> int:
    return _cli(mroot, "ci-record", slug, "--campaign", "demo", "--workflow", workflow,
                "--job", job, "--run-id", run_id, "--head-sha", "abc123def", "--conclusion", conclusion)


def test_requires_ci_job_blocks_grant_until_a_passing_record_on_the_current_artifact(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem ci_one : 1 = 1"
    _ci_node(croot, "CI_one", stmt)
    with pytest.raises(GateError, match="requires a recorded passing run of CI job 'wf.yml:kernel-ladder'"):
        grant_status(load_campaign(croot), "CI_one", **GATE)
    # a record of the WRONG job does not count
    assert _ci_record(mroot, "CI_one", job="other-job") == 0
    with pytest.raises(GateError, match="record is for 'wf.yml:other-job'"):
        grant_status(load_campaign(croot), "CI_one", **GATE)
    # a FAILED run of the right job does not count (and the verb exits 1 to say so)
    assert _ci_record(mroot, "CI_one", conclusion="failure") == 1
    with pytest.raises(GateError, match="concluded 'failure'"):
        grant_status(load_campaign(croot), "CI_one", **GATE)
    # a passing run on the current artifact does
    assert _ci_record(mroot, "CI_one") == 0
    node = grant_status(load_campaign(croot), "CI_one", **GATE)
    assert node.status == "proved"
    rec = node.ci_record
    assert (rec.workflow, rec.job, rec.run_id, rec.head_sha, rec.conclusion) == \
        ("wf.yml", "kernel-ladder", "4242", "abc123def", "success")
    assert rec.artifact_sha256 == node.grant.artifact_sha256
    on_disk = (croot / "nodes" / "CI_one.toml").read_text()
    assert "[ci_record]" in on_disk and 'requires_ci_job = "wf.yml:kernel-ladder"' in on_disk
    assert verify_campaign(croot).ok


def test_ci_record_on_a_stale_artifact_blocks_grant_and_fails_verify(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem ci_two : 2 = 2"
    _ci_node(croot, "CI_two", stmt)
    assert _ci_record(mroot, "CI_two") == 0
    (croot / "proof" / "CI_two.lean").write_text(f"{stmt} := by decide\n")   # artifact edited
    with pytest.raises(GateError, match="was on artifact sha256"):
        grant_status(load_campaign(croot), "CI_two", **GATE)
    assert _ci_record(mroot, "CI_two", run_id="4343") == 0                    # re-recorded
    grant_status(load_campaign(croot), "CI_two", **GATE)
    assert verify_campaign(croot).ok
    # a proved node whose artifact drifts under its ci_record is an error in the battery
    # (alongside the [grant] digest error)
    (croot / "proof" / "CI_two.lean").write_text(f"{stmt} := by simp\n")
    rep = verify_campaign(croot)
    assert any("record" in e and "kernel-ladder" in e for e in rep.errors)


def test_nodes_without_requires_ci_job_are_unaffected(tmp_path):
    mroot, croot = _demo(tmp_path)
    stmt = "theorem ci_free : 3 = 3"
    _open_with_proof(croot, "CI_free", stmt, f"{stmt} := by rfl\n")
    assert grant_status(load_campaign(croot), "CI_free", **GATE).status == "proved"
    assert prov.required_ci_problem(croot, load_node(croot / "nodes" / "CI_free.toml")) == ""


def test_ci_record_round_trips_and_refuses_empty_fields(tmp_path):
    from telperion.missions.schema import CIRecord
    rec = CIRecord("w.yml", "j", "1", "sha", "art", "success", "2026-09-24", run_url="u")
    node = Node(name="S.ci", title="t", kind="lemma", status="open", depends_on=(),
                statement_module="Statements.S_ci", requires_ci_job="w.yml:j", ci_record=rec)
    p = tmp_path / "S_ci.toml"
    save_node(node, p)
    assert load_node(p) == node
    with pytest.raises(SchemaError):
        CIRecord("w.yml", "", "1", "sha", "art", "success", "d")


# ---------------------------------------------------------------------------
# migration and report
# ---------------------------------------------------------------------------

def test_migration_marks_legacy_readbacks_unverified_and_is_idempotent(tmp_path):
    mroot, croot = _demo(tmp_path)
    before = {p.name: load_node(p) for p in (croot / "nodes").glob("*.toml")}
    changed = prov.migrate_unverified(croot)
    with_rb = sorted(n for n, node in before.items() if node.readback is not None)
    assert sorted(f"{c}.toml" for c in changed) == with_rb
    for name, old in before.items():
        new = load_node(croot / "nodes" / name)
        assert new.status == old.status
        if old.readback is None:
            assert new.readback is None
        else:
            assert new.readback.independence == "unverified"
            assert (new.readback.text, new.readback.auditor, new.readback.date) == \
                (old.readback.text, old.readback.auditor, old.readback.date)
    snapshot = {p.name: p.read_text() for p in (croot / "nodes").glob("*.toml")}
    assert prov.migrate_unverified(croot) == []
    assert {p.name: p.read_text() for p in (croot / "nodes").glob("*.toml")} == snapshot


def test_migration_cli(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    assert _cli(mroot, "provenance-migrate", "demo") == 0
    assert "read-back(s) marked" in capsys.readouterr().out


def test_provenance_report_lists_unverified_and_self_audits_only_when_proved(tmp_path, capsys):
    mroot, croot = _demo(tmp_path)
    # 1. legacy proved node (unverified after migration)
    stmt = "theorem r_legacy : 1 = 1"
    _open_with_proof(croot, "R_legacy", stmt, f"{stmt} := by rfl\n")
    grant_status(load_campaign(croot), "R_legacy", **GATE)
    # 2. independently audited proved node
    author = Author(**AUTHOR, date="2026-09-23")
    rb = Readback(text=LONG, auditor="a", date="2026-09-23",
                  auditor_identity=AUDITOR["identity"], auditor_session=AUDITOR["session"],
                  independence="independent")
    stmt2 = "theorem r_ind : 2 = 2"
    _open_with_proof(croot, "R_ind", stmt2, f"{stmt2} := by rfl\n", author=author, readback=rb)
    grant_status(load_campaign(croot), "R_ind", **GATE)
    # 3. legacy proved node covered by a passing Comparator run
    stmt3 = "theorem r_cmp : 3 = 3"
    _open_with_proof(croot, "R_cmp", stmt3, f"{stmt3} := by rfl\n")
    grant_status(load_campaign(croot), "R_cmp", **GATE)
    assert _cli(mroot, "comparator-record", "R_cmp", "--campaign", "demo",
                "--run-id", "777", "--theorem", "r_cmp") == 0
    prov.migrate_unverified(croot)
    capsys.readouterr()

    rc = _cli(mroot, "provenance-report", "demo")
    out = capsys.readouterr().out
    assert rc == 0
    assert "R_legacy" in out and "readback=unverified" in out
    assert "R_ind" not in out
    assert "R_cmp" not in out.split("covered by")[0]
    assert "1 proved node(s) covered by a passing Comparator run" in out
    # open/draft nodes are never listed, whatever their read-back says
    assert "Demo_lemma_a" not in out and "Demo_lemma_b" not in out
    assert _cli(mroot, "provenance-report", "demo", "--strict") == 1


# ---------------------------------------------------------------------------
# schema
# ---------------------------------------------------------------------------

def test_schema_round_trips_new_tables(tmp_path):
    node = Node(
        name="S.rt", title="t", kind="lemma", status="proved", depends_on=(),
        statement_module="Statements.S_rt",
        proof=Proof("a.lean", "lean_module", "direct", True),
        readback=Readback(text=LONG, auditor="lbl", date="d", auditor_identity="i",
                          auditor_session="s", independence="independent"),
        author=Author("ai", "as", "ad"),
        grant=Grant("aa", "ss", "2026-09-23.1", "gd", "gi", "gs"),
        comparator=ComparatorRecord("1", "cd", "aa", "S.rt", run_url="u"),
    )
    p = tmp_path / "S_rt.toml"
    save_node(node, p)
    back = load_node(p)
    assert back == node
    doc = loads_toml(p.read_text())
    assert set(doc) >= {"author", "grant", "comparator", "readback"}
    assert doc["readback"]["independence"] == "independent"


def test_schema_legacy_readback_round_trips_unchanged(tmp_path):
    """A file without the new keys is written back without them (until migrated)."""
    src = DEMO_FIXTURE / "nodes" / "Demo_lemma_a.toml"
    node = load_node(src)
    assert node.readback.independence == "" and node.author is None and node.grant is None
    out = tmp_path / "x.toml"
    save_node(node, out)
    assert loads_toml(out.read_text()) == loads_toml(src.read_text())


def test_schema_rejects_bad_independence_and_empty_provenance():
    with pytest.raises(SchemaError):
        Readback(text="t", auditor="a", date="d", independence="bogus")
    with pytest.raises(SchemaError):
        Author(identity="", session="s", date="d")
    with pytest.raises(SchemaError):
        Grant("a", "s", "", "d", "i", "s")


def test_readback_text_problem_rules():
    assert prov.readback_text_problem("short", "title")
    assert prov.readback_text_problem(LONG, LONG + " and more") == \
        "read-back repeats the node title; a read-back must render the FORMAL statement, not restate the title."
    assert prov.readback_text_problem(LONG, "unrelated title") == ""


def test_independence_of_rules():
    a = Author("a@x", "s1", "d")
    assert prov.independence_of(None, "b@x", "s2") == "unverified"
    assert prov.independence_of(a, "b@x", "s2") == "independent"
    with pytest.raises(prov.SelfAuditError):
        prov.independence_of(a, "b@x", "s1")
    with pytest.raises(prov.SelfAuditError):
        prov.independence_of(a, "A@X", "s2")


# ---------------------------------------------------------------------------
# the live registry
# ---------------------------------------------------------------------------

def _live_missions() -> Path | None:
    root = Path(__file__).resolve().parents[1] / "missions"
    return root if (root / "rh" / "mission.toml").exists() else None


def test_live_registry_every_readback_is_labelled_and_no_grant_digest_is_stale():
    root = _live_missions()
    if root is None:
        pytest.skip("live registry not present")
    for camp_dir in sorted(d for d in root.iterdir() if (d / "mission.toml").exists()):
        camp = load_campaign(camp_dir)
        for sl, node in camp.nodes.items():
            if node.readback is not None:
                assert node.readback.independence in ("unverified", "independent"), \
                    f"{camp_dir.name}/{sl}: read-back has no independence label (run provenance-migrate)"
            assert not prov.readback_is_self_audit(node), f"{camp_dir.name}/{sl} is a self-audit"
            assert prov.grant_digest_errors(camp_dir, node) == [], f"{camp_dir.name}/{sl}"
