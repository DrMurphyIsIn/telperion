"""The `[checks]` record, `checks_problem`, the grant gate, and `mission checks-record`.

Spec 5.2 grant rule: no node is granted unless the negation probe passes (or is
`probe-only` with a reviewer's sign-off) and the closure audit is clean; the statement
fingerprint is recorded. Only nodes created on or after the cutoff (2026-10-28) are gated,
and a node with no `created` date is gated too (Ruling 2, fail-closed). The verdicts are
read from the JSON the checks themselves print, never from flags; the probe and
fingerprint JSONs must name the same replayed olean closure (Ruling 9).
"""
from __future__ import annotations

import dataclasses
import hashlib
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.closure_audit import AuditResult, TargetInfo  # noqa: E402
from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    ChecksRecord, MissionManifest, Node, Proof, Readback, SchemaError,
    load_node, save_manifest, save_node,
)
from telperion.missions.statements import write_statement  # noqa: E402
from telperion.missions.verify import GateError, grant_status  # noqa: E402

OLEAN = "d" * 64
FPRINT = "e" * 64


def _rec(art_sha: str, *, probe: str = "WITNESSED", closure: str = "PASS",
         note: str = "") -> ChecksRecord:
    return ChecksRecord(date="2026-10-29", artifact_sha256=art_sha, olean_sha256=OLEAN,
                        probe_verdict=probe, closure_verdict=closure,
                        statement_fingerprint=FPRINT, theorem="t", note=note)


def _art_sha(root: Path, node: Node) -> str:
    return hashlib.sha256((root / node.proof.artifact).read_bytes()).hexdigest()


def test_checks_roundtrip(tmp_path):
    from telperion.missions.schema import _node_to_doc, _doc_to_node
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _rec("b" * 64, probe="PROBE_ONLY", note="signoff: reviewer bb")
    node2 = _doc_to_node(_node_to_doc(dataclasses.replace(node, checks=rec)), tmp_path / "n.toml")
    assert node2.checks == rec
    assert node2.extra is None                 # `checks` is modelled, not carried as extra
    p = tmp_path / "n.toml"
    save_node(dataclasses.replace(node, checks=rec), p)
    assert "[checks]" in p.read_text()
    assert load_node(p).checks == rec


def test_checks_roundtrip_without_optional_fields(tmp_path):
    from telperion.missions.schema import _node_to_doc, _doc_to_node
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = ChecksRecord(date="2026-10-29", artifact_sha256="b" * 64, olean_sha256=OLEAN,
                       probe_verdict="WITNESSED", closure_verdict="PASS",
                       statement_fingerprint=FPRINT)
    doc = _node_to_doc(dataclasses.replace(node, checks=rec))
    assert "note" not in doc["checks"] and "theorem" not in doc["checks"]
    assert _doc_to_node(doc, tmp_path / "n.toml").checks == rec


@pytest.mark.parametrize("bad", [
    dict(probe_verdict="PASS"),                  # not a probe verdict
    dict(closure_verdict="pass"),                # PASS/FAIL only, exact case
    dict(statement_fingerprint="e" * 63),
    dict(olean_sha256=""),                       # Ruling 9: the replayed closure is required
    dict(olean_sha256="D" * 64),                 # lowercase hex only
    dict(artifact_sha256="z" * 64),
    dict(date=" "),
])
def test_bad_checks_record_rejected(bad):
    fields = dict(date="2026-10-29", artifact_sha256="b" * 64, olean_sha256=OLEAN,
                  probe_verdict="WITNESSED", closure_verdict="PASS",
                  statement_fingerprint=FPRINT)
    fields.update(bad)
    with pytest.raises(SchemaError):
        ChecksRecord(**fields)


def test_probe_verdicts_match_negation_probe():
    from telperion.checks.negation_probe import VERDICTS
    from telperion.missions.schema import PROBE_VERDICTS
    assert set(PROBE_VERDICTS) == set(VERDICTS)


def test_checks_current_record_has_no_problem(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert checks_problem(tmp_path, dataclasses.replace(node, checks=_rec(_art_sha(tmp_path, node)))) == ""


def test_checks_missing_record_is_a_problem(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    assert "checks-record" in checks_problem(tmp_path, node)


def test_checks_stale_artifact(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    old = _art_sha(tmp_path, node)
    (tmp_path / node.proof.artifact).write_text("theorem t : True := by trivial\n")
    problem = checks_problem(tmp_path, dataclasses.replace(node, checks=_rec(old)))
    assert "artifact" in problem and old[:12] in problem


@pytest.mark.parametrize("verdict", ["VACUOUS", "REFUTED", "ERROR"])
def test_vacuous_blocks_grant(tmp_path, verdict):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _rec(_art_sha(tmp_path, node), probe=verdict, note="signoff: does not help here")
    assert verdict in checks_problem(tmp_path, dataclasses.replace(node, checks=rec))


def test_probe_only_needs_signoff(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    sha = _art_sha(tmp_path, node)
    for note in ("", "reviewed, looks fine", "signoff:", "signoff:   "):
        problem = checks_problem(tmp_path, dataclasses.replace(
            node, checks=_rec(sha, probe="PROBE_ONLY", note=note)))
        assert "PROBE_ONLY" in problem and "signoff:" in problem, note
    ok = _rec(sha, probe="PROBE_ONLY", note="probe could not run; signoff: bb 2026-10-29")
    assert checks_problem(tmp_path, dataclasses.replace(node, checks=ok)) == ""


def test_closure_fail_blocks(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _rec(_art_sha(tmp_path, node), closure="FAIL")
    assert "closure" in checks_problem(tmp_path, dataclasses.replace(node, checks=rec))


@pytest.mark.parametrize("created,required", [
    ("2026-10-01", False), ("2026-10-27", False), ("2026-10-27T23:59:00Z", False),
    ("2026-10-28", True), ("2026-10-29", True),
    ("", True),                       # Ruling 2: no date is not pre-process
    ("1999", True), ("yesterday", True), ("2026-00-00", True),   # unparseable: fail-closed
])
def test_checks_required_by_created(created, required):
    from telperion.missions.provenance import checks_required
    node = Node(name="n", title="t", kind="lemma", status="open", depends_on=(),
                statement_module="S", created=created)
    assert checks_required(node) is required


# ---------------------------------------------------------------------------
# The grant gate
# ---------------------------------------------------------------------------

def _grant_campaign(tmp_path: Path, *, created: str, campaign: str = "campaign") -> Path:
    """An `open`, non-heavy node with a statement, an independent read-back and a matching
    artifact: everything the gate needs except (possibly) a `[checks]` record."""
    root = tmp_path / campaign
    (root / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.ck", title="Demo Campaign", description="synthetic",
        goal_node="Demo_ck", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, root / "mission.toml")
    stmt = "theorem lemma_ck : 1 + 1 = 2"
    node = Node(
        name="Demo.ck", title="node awaiting grant", kind="lemma", status="open",
        depends_on=(), statement_module="Statements.Demo_ck",
        proof=Proof(artifact="proof/Demo_ck.lean", artifact_kind="lean_module",
                    via="direct", closure_clean=False),
        readback=Readback(text="read-back of Demo.ck, rendering the formal statement in "
                               "the auditor's own words at length", auditor="test-auditor",
                          date="2026-10-29"),
        created=created, updated=created,
    )
    save_node(node, root / "nodes" / "Demo_ck.toml")
    write_statement(root, node, stmt, manifest)
    art = root / "proof" / "Demo_ck.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text(f"{stmt} := by simp\n")
    return root


def _with_checks(root: Path, rec: ChecksRecord) -> None:
    p = root / "nodes" / "Demo_ck.toml"
    save_node(dataclasses.replace(load_node(p), checks=rec), p)


def _grant(root: Path) -> Node:
    return grant_status(load_campaign(root), "Demo_ck", identity="gate@test",
                        session="gate-session")


def test_pre_cutoff_node_not_required(tmp_path):
    root = _grant_campaign(tmp_path, created="2026-10-01")
    assert _grant(root).status == "proved"
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "proved"


def test_post_cutoff_node_required(tmp_path):
    root = _grant_campaign(tmp_path, created="2026-10-28")
    with pytest.raises(GateError, match=r"\[checks\]"):
        _grant(root)
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_missing_created_requires_checks(tmp_path):
    root = _grant_campaign(tmp_path, created="")
    with pytest.raises(GateError, match=r"\[checks\]"):
        _grant(root)
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_post_cutoff_node_with_passing_checks_granted(tmp_path):
    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    assert _grant(root).status == "proved"


@pytest.mark.parametrize("probe,closure,note", [
    ("VACUOUS", "PASS", ""), ("REFUTED", "PASS", ""), ("ERROR", "PASS", ""),
    ("PROBE_ONLY", "PASS", ""), ("WITNESSED", "FAIL", ""),
])
def test_post_cutoff_node_with_blocking_checks_refused(tmp_path, probe, closure, note):
    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node), probe=probe, closure=closure, note=note))
    with pytest.raises(GateError, match=r"\[checks\]"):
        _grant(root)
    assert load_node(root / "nodes" / "Demo_ck.toml").status == "open"


def test_post_cutoff_node_with_stale_checks_refused(tmp_path):
    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node)))
    art = root / node.proof.artifact
    art.write_text(art.read_text() + "-- edited after the checks ran\n")
    with pytest.raises(GateError, match="artifact"):
        _grant(root)


def test_provenance_report_shows_checks(tmp_path):
    from telperion.missions.provenance import render_provenance_report
    pre = _grant_campaign(tmp_path, created="2026-10-01", campaign="pre")
    _grant(pre)
    report = render_provenance_report(load_campaign(pre))
    assert "pre-process" in report
    post = _grant_campaign(tmp_path, created="2026-10-29", campaign="post")
    node = load_node(post / "nodes" / "Demo_ck.toml")
    _with_checks(post, _rec(_art_sha(post, node)))
    _grant(post)
    report = render_provenance_report(load_campaign(post))
    assert "probe WITNESSED, closure PASS" in report
    assert "pre-process" not in report


# ---------------------------------------------------------------------------
# CLI: `mission checks-record`
# ---------------------------------------------------------------------------

def _cli(mroot: Path, *args: str) -> int:
    return main(["mission", "--missions-root", str(mroot), *args])


def _write_jsons(tmp_path: Path, *, verdict: str = "WITNESSED", closure: str = "PASS",
                 probe_olean: str = OLEAN, fp_olean: str = OLEAN,
                 fingerprints=None, targets=("lemma_ck",), lean_exit_code=0):
    """The three JSONs in the exact shapes the checks print: `probe-negation --json`
    (ProbeResult.to_json), `fingerprint --json` (cmd_fingerprint) and `audit-closure --json`
    (AuditResult.to_json, the real serializer)."""
    closure_list = [["Demo.Proof", "olean", "f" * 64]]
    probe = {"verdict": verdict, "detail": "synthetic"}
    if probe_olean is not None:
        probe.update(olean_sha256=probe_olean, olean_closure=closure_list)
    fp = {"fingerprints": fingerprints if fingerprints is not None else {"lemma_ck": FPRINT},
          "olean_sha256": fp_olean, "olean_closure": closure_list}
    audit = AuditResult(verdict=closure, lean_exit_code=lean_exit_code,
                        targets=[TargetInfo(name=t, kind="theorem", statement="1 + 1 = 2")
                                 for t in targets])
    paths = {}
    for name, body in (("probe", json.dumps(probe)), ("fp", json.dumps(fp)),
                       ("closure", audit.to_json())):
        paths[name] = tmp_path / f"{name}.json"
        paths[name].write_text(body + "\n")
    return paths


def _record(mroot: Path, paths: dict, *extra: str) -> int:
    return _cli(mroot, "checks-record", "Demo_ck", "--campaign", "demo",
                "--probe-json", str(paths["probe"]), "--closure-json", str(paths["closure"]),
                "--fingerprint-json", str(paths["fp"]), *extra)


def _cli_campaign(tmp_path: Path, created: str = "2026-10-29") -> Path:
    mroot = tmp_path / "missions"
    _grant_campaign(mroot, created=created, campaign="demo")
    return mroot


def _node(mroot: Path) -> Node:
    return load_node(mroot / "demo" / "nodes" / "Demo_ck.toml")


def test_cli_reads_verdicts_from_json(tmp_path):
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path)
    assert _record(mroot, paths) == 0
    n = _node(mroot)
    c = n.checks
    assert c is not None
    assert (c.probe_verdict, c.closure_verdict) == ("WITNESSED", "PASS")
    assert c.statement_fingerprint == FPRINT and c.theorem == "lemma_ck"
    assert c.olean_sha256 == OLEAN
    assert c.artifact_sha256 == _art_sha(mroot / "demo", n)
    assert n.updated == c.date
    assert n.status == "open"                 # checks-record never flips status itself


@pytest.mark.parametrize("verdict", ["VACUOUS", "REFUTED", "ERROR", "PROBE_ONLY"])
def test_cli_blocking_probe_recorded_exit1(tmp_path, verdict):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, verdict=verdict)) == 1
    assert _node(mroot).checks.probe_verdict == verdict


def test_cli_probe_only_with_signoff_exit0(tmp_path):
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path, verdict="PROBE_ONLY")
    assert _record(mroot, paths, "--note", "signoff: bb reviewed the hypotheses") == 0
    assert "signoff:" in _node(mroot).checks.note


@pytest.mark.parametrize("closure,lean_rc", [("FAIL", 1), ("", None), ("PASS", 1)])
def test_cli_closure_not_ok_recorded_as_fail(tmp_path, closure, lean_rc):
    """PASS needs both the verdict line AND `ok` (a clean Lean exit): AuditResult.ok."""
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, closure=closure, lean_exit_code=lean_rc)) == 1
    assert _node(mroot).checks.closure_verdict == "FAIL"


def test_cli_olean_mismatch_refused(tmp_path, capsys):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, fp_olean="c" * 64)) == 2
    assert _node(mroot).checks is None
    assert "olean_sha256" in capsys.readouterr().err


def test_cli_probe_without_olean_refused(tmp_path):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, probe_olean=None)) == 2
    assert _node(mroot).checks is None


def test_cli_fingerprint_error_json_refused(tmp_path):
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path)
    paths["fp"].write_text(json.dumps({"error": "target not found"}))
    assert _record(mroot, paths) == 2
    assert _node(mroot).checks is None


def test_cli_unknown_probe_verdict_refused(tmp_path):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, verdict="PASS")) == 2
    assert _node(mroot).checks is None


def test_cli_several_fingerprints_need_target(tmp_path):
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path, fingerprints={"lemma_ck": FPRINT, "other": "a" * 64},
                         targets=("lemma_ck", "other"))
    assert _record(mroot, paths) == 2
    assert _node(mroot).checks is None
    assert _record(mroot, paths, "--target", "other") == 0
    assert _node(mroot).checks.statement_fingerprint == "a" * 64


def test_cli_fingerprint_target_must_be_closure_audited(tmp_path):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, targets=("something_else",))) == 2
    assert _node(mroot).checks is None


def test_cli_no_verdict_flags():
    """The verdicts come from the JSON files; there is no flag to assert one."""
    with pytest.raises(SystemExit):
        main(["mission", "checks-record", "X", "--campaign", "c", "--probe-verdict", "WITNESSED"])


def test_checks_record_then_grant_closes_the_loop(tmp_path):
    mroot = _cli_campaign(tmp_path)
    croot = mroot / "demo"
    with pytest.raises(GateError, match=r"\[checks\]"):
        _grant(croot)
    assert _record(mroot, _write_jsons(tmp_path)) == 0
    assert _grant(croot).status == "proved"
