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
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.closure_audit import AuditResult, TargetInfo  # noqa: E402
from telperion.missions.process import (  # noqa: E402
    DEVIATIONS_TEMPLATE, deviations_path, freeze, freeze_path,
)
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
         note: str = "", theorem: str = "lemma_ck", axioms=("propext",)) -> ChecksRecord:
    # final review I1/I3: the record is of the node's registered theorem (the campaign fixtures'
    # `lemma_ck`) and carries the replay's axiom list
    return ChecksRecord(date="2026-10-29", artifact_sha256=art_sha, olean_sha256=OLEAN,
                        probe_verdict=probe, closure_verdict=closure,
                        statement_fingerprint=FPRINT, theorem=theorem, note=note, axioms=axioms)


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


def _statement_for(root: Path, node: Node) -> None:
    """The node's statement file, so `checks_problem` can resolve its registered theorem (final review I1):
    `minimal_proved_node`'s artifact declares `theorem t : True`."""
    from telperion.missions.statements import statement_path
    p = statement_path(root, node)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("theorem t : True\n")


def test_checks_current_record_has_no_problem(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    _statement_for(tmp_path, node)
    assert checks_problem(tmp_path, dataclasses.replace(node, checks=_rec(_art_sha(tmp_path, node),
                                                                          theorem="t"))) == ""


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
    _statement_for(tmp_path, node)
    ok = _rec(sha, probe="PROBE_ONLY", note="probe could not run; signoff: bb 2026-10-29", theorem="t")
    assert checks_problem(tmp_path, dataclasses.replace(node, checks=ok)) == ""


def test_closure_fail_blocks(tmp_path):
    from telperion.missions.provenance import checks_problem
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    rec = _rec(_art_sha(tmp_path, node), closure="FAIL")
    assert "closure" in checks_problem(tmp_path, dataclasses.replace(node, checks=rec))


@pytest.mark.parametrize("created,required", [
    ("2026-10-01", False), ("2026-10-27", False),
    ("2026-10-27T23:59:00Z", True), ("2026-10-01junk", True),   # Ruling 12: the WHOLE string
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
    # Step 5 Task 1: a post-cutoff node is granted only once the campaign is frozen
    # (freeze_grant_problem). Fix round 2 (Controller Ruling 6): freeze_grant_problem also
    # refuses on any freeze_problems(root) problem, history included, and
    # freeze_history_problems fails closed on a post-cutoff FREEZE.toml with no git history
    # -- so a real grant now also needs the freeze committed. These fixtures predate all of
    # that, so freeze AND commit once here, same as a real session would run `mission
    # freeze` + `git commit` before `mission grant`; a campaign already frozen (e.g. a
    # re-grant in the same test) is left alone.
    if not freeze_path(root).exists():
        freeze(root, identity="gate@test", session="gate-session", date="2026-10-29")
        subprocess.run(["git", "-C", str(root), "init", "-q"],
                       check=True, capture_output=True, text=True)
        subprocess.run(["git", "-C", str(root), "add", "."],
                       check=True, capture_output=True, text=True)
        subprocess.run(
            ["git", "-C", str(root), "-c", "user.name=Test User",
             "-c", "user.email=test@example.com", "commit", "-q", "-m",
             "test fixture: initial freeze"],
            check=True, capture_output=True, text=True,
        )
    # Step 5 Task 3: a post-cutoff grant also needs a DEVIATIONS.md ledger
    # (deviations_grant_problem); write the "none" template here, same as freezing above,
    # unless a test already put one in place.
    if not deviations_path(root).exists():
        deviations_path(root).write_text(DEVIATIONS_TEMPLATE)
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


#: Stands for "the sha256 of the CLI campaign's artifact as it is on disk now".
CUR = object()
_SAME = object()


def _write_jsons(tmp_path: Path, *, verdict: str = "WITNESSED", closure: str = "PASS",
                 probe_olean: str = OLEAN, fp_olean: str = OLEAN,
                 fingerprints=None, targets=("lemma_ck",), lean_exit_code=0,
                 probe_theorem="lemma_ck", fp_theorem=_SAME, probe_src=CUR, fp_src=CUR,
                 probe_axioms=("propext",), fp_axioms=("propext",), closure_axioms=("propext",), stale=None):
    """The three JSONs in the exact shapes the checks print: `probe-negation --json`
    (ProbeResult.to_json plus module/theorem/source_sha256, cmd_probe_negation),
    `fingerprint --json` (cmd_fingerprint) and `audit-closure --json` (AuditResult.to_json,
    the real serializer). A value of None leaves the key out (an older JSON)."""
    cur = hashlib.sha256((tmp_path / "missions" / "demo" / "proof" / "Demo_ck.lean")
                         .read_bytes()).hexdigest()
    closure_list = [["Demo.Proof", "olean", "f" * 64]]
    fps = fingerprints if fingerprints is not None else {"lemma_ck": FPRINT}
    if fp_theorem is _SAME:
        fp_theorem = next(iter(fps)) if len(fps) == 1 else None
    probe = {"verdict": verdict, "detail": "synthetic"}
    if probe_olean is not None:
        probe.update(olean_sha256=probe_olean, olean_closure=closure_list)
    if probe_axioms is not None:
        probe["axioms"] = list(probe_axioms)
    if stale is not None:
        probe["stale"] = stale
    probe["module"] = "Demo.Proof"
    if probe_theorem is not None:
        probe["theorem"] = probe_theorem
    if probe_src is not None:
        probe["source_sha256"] = cur if probe_src is CUR else probe_src
    fp = {"fingerprints": fps, "olean_sha256": fp_olean, "olean_closure": closure_list,
          "module": "Demo.Proof", "theorem": fp_theorem}
    if fp_src is not None:
        fp["source_sha256"] = cur if fp_src is CUR else fp_src
    if fp_axioms is not None:
        fp["axioms"] = list(fp_axioms)
    audit = AuditResult(verdict=closure, lean_exit_code=lean_exit_code,
                        targets=[TargetInfo(name=t, kind="theorem", statement="1 + 1 = 2",
                                            axioms=list(closure_axioms)) for t in targets])
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
    # final review I1: the target is the node's registered theorem (lemma_ck), with or without
    # --target, so several fingerprints are no longer ambiguous and a helper's are refused
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path, fingerprints={"lemma_ck": FPRINT, "other": "a" * 64},
                         targets=("lemma_ck", "other"))
    assert _record(mroot, paths, "--target", "other") == 2      # not the registered theorem
    assert _node(mroot).checks is None
    paths = _write_jsons(tmp_path, fingerprints={"lemma_ck": FPRINT, "other": "a" * 64},
                         targets=("lemma_ck", "other"), probe_theorem="other")
    assert _record(mroot, paths, "--target", "other") == 2      # a helper lemma's checks
    assert _node(mroot).checks is None
    paths = _write_jsons(tmp_path, fingerprints={"lemma_ck": FPRINT, "other": "a" * 64},
                         targets=("lemma_ck", "other"))
    assert _record(mroot, paths) == 0
    assert _node(mroot).checks.statement_fingerprint == FPRINT


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


# ---------------------------------------------------------------------------
# Ruling 11: GATE_VERSION, and `mission verify` re-checks [checks] on proved nodes
# ---------------------------------------------------------------------------

def test_gate_version_bumped_for_checks(tmp_path):
    from telperion.missions import provenance as prov
    assert prov.GATE_VERSION == "2026-10-29.1"
    root = _grant_campaign(tmp_path, created="2026-10-29")
    _with_checks(root, _rec(_art_sha(root, load_node(root / "nodes" / "Demo_ck.toml"))))
    assert _grant(root).grant.gate_version == "2026-10-29.1"


def _proved(tmp_path: Path, *, created: str, checks: bool = True) -> Path:
    """A node granted `proved` through the gate (with a current [checks] record when the
    gate demands one), then optionally stripped of its record afterwards."""
    root = _grant_campaign(tmp_path, created=created)
    p = root / "nodes" / "Demo_ck.toml"
    _with_checks(root, _rec(_art_sha(root, load_node(p))))
    _grant(root)
    if not checks:
        save_node(dataclasses.replace(load_node(p), checks=None), p)
    return root


def _checks_errors(root: Path) -> list:
    from telperion.missions.verify import verify_campaign
    return [e for e in verify_campaign(root).errors if "[checks]" in e]


def test_verify_post_cutoff_proved_node_with_current_checks_passes(tmp_path):
    assert _checks_errors(_proved(tmp_path, created="2026-10-29")) == []


def test_verify_post_cutoff_proved_node_missing_checks_fails(tmp_path):
    errs = _checks_errors(_proved(tmp_path, created="2026-10-29", checks=False))
    assert len(errs) == 1 and "Demo_ck" in errs[0] and "checks-record" in errs[0], errs


def test_verify_post_cutoff_proved_node_stale_checks_fails(tmp_path):
    root = _proved(tmp_path, created="2026-10-29")
    art = root / "proof" / "Demo_ck.lean"
    art.write_text(art.read_text() + "-- edited after the grant\n")
    errs = _checks_errors(root)
    assert len(errs) == 1 and "artifact" in errs[0], errs


def test_verify_proved_node_without_created_needs_checks(tmp_path):
    root = _proved(tmp_path, created="2026-10-29", checks=False)
    p = root / "nodes" / "Demo_ck.toml"
    save_node(dataclasses.replace(load_node(p), created=""), p)
    assert len(_checks_errors(root)) == 1


def test_verify_pre_cutoff_proved_node_without_checks_passes(tmp_path):
    assert _checks_errors(_proved(tmp_path, created="2026-10-01", checks=False)) == []


def test_verify_open_post_cutoff_node_without_checks_not_an_error(tmp_path):
    """Only a PROVED status rests on the checks; an open node simply has not been granted."""
    assert _checks_errors(_grant_campaign(tmp_path, created="2026-10-29")) == []


# ---------------------------------------------------------------------------
# Ruling 12: the requirement survives a `created` edit; strict parsing; unknown keys;
# the probe and fingerprint JSONs are tied to the artifact source and to one theorem
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("flag,required", [(True, True), (False, False)])
def test_checks_required_by_grant_record(flag, required):
    from telperion.missions.provenance import checks_required
    from telperion.missions.schema import Grant
    node = Node(name="n", title="t", kind="lemma", status="open", depends_on=(),
                statement_module="S", created="2026-10-01",
                grant=Grant("a" * 64, "b" * 64, "2026-10-29.1", "2026-10-29", "gi", "gs",
                            checks_required=flag))
    assert checks_required(node) is required


@pytest.mark.parametrize("created,flag", [("2026-10-29", True), ("", True), ("2026-10-01", False)])
def test_gate_records_its_checks_decision(tmp_path, created, flag):
    """Every grant the new gate writes is 2026-10-29.1, so the decision itself is recorded: a
    pre-cutoff node granted today stays exempt (Ruling 11), a post-cutoff one keeps the rule."""
    root = _proved(tmp_path, created=created)
    p = root / "nodes" / "Demo_ck.toml"
    assert load_node(p).grant.checks_required is flag
    assert ("checks_required = true" in p.read_text()) is flag


def test_verify_created_edited_after_new_gate_grant_still_needs_checks(tmp_path):
    root = _proved(tmp_path, created="2026-10-29", checks=False)
    p = root / "nodes" / "Demo_ck.toml"
    assert load_node(p).grant.gate_version == "2026-10-29.1"
    save_node(dataclasses.replace(load_node(p), created="2026-10-01"), p)
    errs = _checks_errors(root)
    assert len(errs) == 1 and "checks-record" in errs[0], errs


def test_regrant_after_created_edit_still_needs_checks(tmp_path):
    """The re-grant path shares the predicate: a node reopened with its [grant] block kept
    cannot be granted again without [checks] by back-dating `created`."""
    root = _proved(tmp_path, created="2026-10-29", checks=False)
    p = root / "nodes" / "Demo_ck.toml"
    n = load_node(p)
    save_node(dataclasses.replace(n, status="open", created="2026-10-01"), p)
    with pytest.raises(GateError, match=r"\[checks\]"):
        _grant(root)


def test_unknown_checks_key_rejected(tmp_path):
    from telperion.missions.schema import _node_to_doc, _doc_to_node
    from missions_fixtures import minimal_proved_node
    node = minimal_proved_node(tmp_path, heavy=False)
    doc = _node_to_doc(dataclasses.replace(node, checks=_rec("b" * 64)))
    doc["checks"]["probe_override"] = "WITNESSED"
    with pytest.raises(SchemaError, match="probe_override"):
        _doc_to_node(doc, tmp_path / "n.toml")


@pytest.mark.parametrize("which", ["probe_src", "fp_src"])
def test_cli_stale_source_sha_refused(tmp_path, which, capsys):
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path, **{which: "0" * 64})
    assert _record(mroot, paths) == 2                             # a WRONG value is never allowed
    assert _node(mroot).checks is None
    assert "source_sha256" in capsys.readouterr().err


@pytest.mark.parametrize("kw", [dict(probe_src=None), dict(fp_src=None), dict(probe_theorem=None)])
def test_cli_missing_source_or_theorem_needs_flag(tmp_path, kw, capsys):
    # final review I2: --allow-missing-source is gone; an absent value is always refused
    mroot = _cli_campaign(tmp_path)
    paths = _write_jsons(tmp_path, **kw)
    assert _record(mroot, paths) == 2
    assert _node(mroot).checks is None
    assert "--file" in capsys.readouterr().err
    with pytest.raises(SystemExit):
        _record(mroot, paths, "--allow-missing-source")


@pytest.mark.parametrize("kw", [dict(probe_theorem="other"), dict(fp_theorem="other")])
def test_cli_theorem_must_agree(tmp_path, kw, capsys):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, **kw)) == 2
    assert _node(mroot).checks is None
    assert "theorem" in capsys.readouterr().err


def test_cli_probe_json_carries_module_theorem_source(tmp_path, monkeypatch, capsys):
    from telperion.checks import negation_probe as np_
    from telperion.checks.negation_probe import ProbeResult
    monkeypatch.setattr(np_, "run_probe", lambda spec, project, **kw: ProbeResult("WITNESSED", "ok"))
    assert main(["probe-negation", "--project", str(tmp_path), "--module", "T", "--theorem",
                 "Foo.bar", "--json"]) == 0
    out = json.loads(capsys.readouterr().out)
    assert (out["module"], out["theorem"], out["source_sha256"]) == ("T", "Foo.bar", None)


def test_cli_fingerprint_json_carries_module_theorem_source(tmp_path, monkeypatch, capsys):
    from telperion.checks import fingerprint as fp_
    monkeypatch.setattr(fp_, "run_fingerprint", lambda project, imports, targets, **kw:
                        fp_.Fingerprints({t: "a" * 64 for t in targets}, "b" * 64, []))
    src = tmp_path / "M.lean"
    src.write_text("theorem foo : True := trivial\n")
    assert main(["fingerprint", "--project", ".", "--import", "M", "--target", "foo",
                 "--file", str(src), "--json"]) == 0
    out = json.loads(capsys.readouterr().out)
    assert (out["module"], out["theorem"]) == ("M", "foo")
    assert out["source_sha256"] == hashlib.sha256(src.read_bytes()).hexdigest()
    assert main(["fingerprint", "--project", ".", "--import", "M", "--import", "N",
                 "--target", "foo", "--target", "bar", "--json"]) == 0
    out = json.loads(capsys.readouterr().out)
    assert (out["module"], out["theorem"], out["source_sha256"]) == (None, None, None)


# ---------------------------------------------------------------------------
# Final review: I1 (the node's own theorem), I3 (the replay's axioms), I4 (stale builds)
# ---------------------------------------------------------------------------

def test_helper_lemma_record_refused_by_the_gate(tmp_path):
    root = _grant_campaign(tmp_path, created="2026-10-29")
    art = root / "proof" / "Demo_ck.lean"
    art.write_text(art.read_text() + "theorem helper : True := trivial\n")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    _with_checks(root, _rec(_art_sha(root, node), theorem="helper"))
    with pytest.raises(GateError, match="registered theorem is 'lemma_ck'"):
        _grant(root)
    _with_checks(root, _rec(_art_sha(root, node)))
    assert _grant(root).status == "proved"


def test_helper_lemma_record_refused_by_checks_record(tmp_path, capsys):
    mroot = _cli_campaign(tmp_path)
    art = mroot / "demo" / "proof" / "Demo_ck.lean"
    art.write_text(art.read_text() + "theorem helper : True := trivial\n")
    paths = _write_jsons(tmp_path, fingerprints={"helper": FPRINT}, targets=("helper",),
                         probe_theorem="helper")
    assert _record(mroot, paths) == 2
    assert _node(mroot).checks is None
    assert "registered theorem" in capsys.readouterr().err


def test_record_of_another_theorem_than_the_comparator_record_fails(tmp_path):
    from telperion.missions.provenance import checks_problem
    from telperion.missions.schema import ComparatorRecord
    root = _grant_campaign(tmp_path, created="2026-10-29")
    p = root / "nodes" / "Demo_ck.toml"
    node = load_node(p)
    node = dataclasses.replace(node, checks=_rec(_art_sha(root, node)))
    assert checks_problem(root, node) == ""
    comp = ComparatorRecord(run_id="1", date="2026-10-29", artifact_sha256=_art_sha(root, node),
                            theorem="other_thm")
    assert "Comparator record" in checks_problem(root, dataclasses.replace(node, comparator=comp))


@pytest.mark.parametrize("axioms,why", [(None, "no replay axiom list"),
                                        (("propext", "TpBad.bad"), "non-standard axioms")])
def test_checks_problem_needs_clean_replay_axioms(tmp_path, axioms, why):
    from telperion.missions.provenance import checks_problem
    root = _grant_campaign(tmp_path, created="2026-10-29")
    node = load_node(root / "nodes" / "Demo_ck.toml")
    assert why in checks_problem(root, dataclasses.replace(node, checks=_rec(_art_sha(root, node), axioms=axioms)))


@pytest.mark.parametrize("kw,why", [
    (dict(probe_axioms=None), "axioms"),
    (dict(fp_axioms=None), "axioms"),
    (dict(fp_axioms=("propext", "Quot.sound")), "differ"),
    (dict(probe_axioms=("propext", "Lean.ofReduceBool"), fp_axioms=("propext", "Lean.ofReduceBool")),
     "non-standard"),
    (dict(closure_axioms=("propext", "Classical.choice")), "closure audit's axioms"),
])
def test_cli_replay_axioms_cross_check(tmp_path, kw, why, capsys):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, **kw)) == 2
    assert _node(mroot).checks is None
    assert why in capsys.readouterr().err


def test_cli_records_the_replay_axioms(tmp_path):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, probe_axioms=("propext", "Quot.sound"),
                                       fp_axioms=("Quot.sound", "propext"))) == 0
    assert _node(mroot).checks.axioms == ("Quot.sound", "propext")


def test_cli_stale_json_refused(tmp_path, capsys):
    mroot = _cli_campaign(tmp_path)
    assert _record(mroot, _write_jsons(tmp_path, stale=True)) == 2
    assert "stale" in capsys.readouterr().err


def _stale_project(tmp_path: Path, newer_source: bool) -> tuple[Path, Path]:
    import os
    proj = tmp_path / "proj"
    olean = proj / ".lake" / "build" / "lib" / "lean" / "M.olean"
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b"olean")
    src = proj / "M.lean"
    src.write_text("theorem foo : True := trivial\n")
    t = olean.stat().st_mtime
    os.utime(src, (t + 100, t + 100) if newer_source else (t - 100, t - 100))
    return proj, src


def test_cli_probe_refuses_a_stale_build(tmp_path, monkeypatch, capsys):
    from telperion.checks import negation_probe as np_
    from telperion.checks.negation_probe import ProbeResult
    ran = []
    monkeypatch.setattr(np_, "run_probe", lambda spec, project, **kw: ran.append(1) or ProbeResult("WITNESSED", "ok"))
    proj, src = _stale_project(tmp_path, newer_source=True)
    assert main(["probe-negation", "--project", str(proj), "--module", "M", "--theorem", "foo",
                 "--file", str(src), "--json"]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["verdict"] == "ERROR" and "stale" in out["detail"] and out["stale"] is True and not ran
    assert out["source_mtime"] > out["olean_mtime"]
    proj2, src2 = _stale_project(tmp_path / "fresh", newer_source=False)
    assert main(["probe-negation", "--project", str(proj2), "--module", "M", "--theorem", "foo",
                 "--file", str(src2), "--json"]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["stale"] is False and ran


def test_cli_fingerprint_refuses_a_stale_build(tmp_path, monkeypatch, capsys):
    from telperion.checks import fingerprint as fp_
    monkeypatch.setattr(fp_, "run_fingerprint", lambda project, imports, targets, **kw:
                        fp_.Fingerprints({t: "a" * 64 for t in targets}, "b" * 64, [], ["propext"]))
    proj, src = _stale_project(tmp_path, newer_source=True)
    assert main(["fingerprint", "--project", str(proj), "--import", "M", "--target", "foo",
                 "--file", str(src), "--json"]) == 2
    assert "stale" in json.loads(capsys.readouterr().out)["error"]
    proj2, src2 = _stale_project(tmp_path / "fresh", newer_source=False)
    assert main(["fingerprint", "--project", str(proj2), "--import", "M", "--target", "foo",
                 "--file", str(src2), "--json"]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["axioms"] == ["propext"] and out["stale"] is False
