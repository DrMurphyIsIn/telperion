"""Invariants I1-I5 each have a violating case that must refuse; dry-run e2e."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.api import HttpResponse, Prove2MeClient  # noqa: E402
from telperion.prove2me.attempt import (  # noqa: E402
    BuildFailed,
    InvariantViolation,
    check_no_self_import,
    check_no_sorry,
    check_solution_theorem,
    lake_build,
    render_solution,
    run_attempt,
)
from telperion.prove2me.ledger import AttemptLedger  # noqa: E402
from telperion.prove2me.triage import QueueItem  # noqa: E402
from telperion.prove2me.workspace import Workspace  # noqa: E402

STMT = "theorem solution : (1 : ℚ) + 1 = 2"
GOOD = "import Mathlib\n\ntheorem solution : (1 : ℚ) + 1 = 2 := by norm_num\n"


def test_render_solution_contains_statement_and_imports():
    src = render_solution(STMT, "by norm_num")
    assert "import Mathlib" in src and "theorem solution" in src


def test_i3_no_sorry_refuses():
    with pytest.raises(InvariantViolation, match="sorry"):
        check_no_sorry(GOOD.replace("by norm_num", "by sorry"))
    check_no_sorry(GOOD)   # clean source passes


def test_i3_solution_name_and_statement_must_match():
    with pytest.raises(InvariantViolation):
        check_solution_theorem(GOOD.replace("solution", "myThm"), STMT)
    with pytest.raises(InvariantViolation):
        check_solution_theorem(GOOD, "theorem solution : (2 : ℚ) = 2")
    check_solution_theorem(GOOD, STMT)


def test_i2_no_self_import_refuses():
    src = "import Theorems.M42\n" + GOOD
    with pytest.raises(InvariantViolation, match="own target"):
        check_no_self_import(src, "Theorems.M42")
    check_no_self_import(GOOD, "Theorems.M42")


def test_i1_lake_build_gate(tmp_path):
    calls = {}

    def fake_run(cmd, **kw):
        calls["cmd"] = cmd
        class R: returncode, stdout, stderr = 1, b"", b"error: unsolved goals"
        return R()

    with pytest.raises(BuildFailed, match="unsolved goals"):
        lake_build(tmp_path, runner=fake_run)
    assert calls["cmd"][:2] == ["lake", "build"]


def _scripted_client(tmp_path, responses):
    def transport(method, url, headers, body):
        r = responses.pop(0)
        return r if isinstance(r, HttpResponse) else HttpResponse(*r)
    c = Prove2MeClient(workspace=tmp_path, transport=transport,
                       _sleep=lambda s: None, _now=lambda: 0.0)
    c.access_token = "t"
    return c


def test_run_attempt_dry_run_never_touches_network(tmp_path, monkeypatch):
    c = _scripted_client(tmp_path, [])          # any request would IndexError
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash",
                      led, no_submit=True, _sleep=lambda s: None)
    assert rec.verdict == "DryRun" and led.records()[0].verdict == "DryRun"


def test_run_attempt_submits_polls_annotates_and_ledgers(tmp_path, monkeypatch):
    responses = [
        HttpResponse(200, json.dumps({"submission_id": "s7"})),      # POST /verify (multipart, explanation inline: I4)
        HttpResponse(200, json.dumps({"status": "PENDING"})),
        HttpResponse(200, json.dumps({"status": "Proved"})),
    ]
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)   # I1 assumed green here
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                      explanation="norm_num identity; source: arithmetic",
                      _sleep=lambda s: None)
    assert rec.verdict == "Proved" and rec.submission_id == "s7"
    assert not responses        # all three calls consumed (I4 rides on verify)


def test_run_attempt_certify_refused_ledgered(tmp_path, monkeypatch):
    """InvariantViolation (sorry) in run_attempt returns CertifyRefused, no network."""
    c = _scripted_client(tmp_path, [])          # any request would IndexError
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    sorry_source = GOOD.replace("by norm_num", "by sorry")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    rec = run_attempt(c, ws, item, sorry_source, ("IdentityEmitter",), "hash",
                      led, _sleep=lambda s: None)
    assert rec.verdict == "CertifyRefused"
    assert led.records()[0].verdict == "CertifyRefused"


def test_run_attempt_build_failed_ledgered_no_network(tmp_path, monkeypatch):
    """BuildFailed from lake_build is ledgered; no network call is made."""
    c = _scripted_client(tmp_path, [])          # any request would IndexError
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    def _failing_build(project_dir, runner=None):
        raise BuildFailed("I1: lake build failed in /tmp:\nunsolved goals")
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build", _failing_build)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash",
                      led, _sleep=lambda s: None)
    assert rec.verdict == "BuildFailed"
    assert "unsolved goals" in rec.server_output
    assert led.records()[0].verdict == "BuildFailed"


def test_run_attempt_rejection_is_ledgered_not_retried(tmp_path, monkeypatch):
    responses = [
        HttpResponse(200, json.dumps({"submission_id": "s8"})),
        HttpResponse(200, json.dumps({"status": "Rejected",
                                      "output": "type mismatch"})),
    ]
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                      _sleep=lambda s: None)
    assert rec.verdict == "Rejected" and "type mismatch" in rec.server_output
    assert led.rejected("m1")           # I5: recorded; caller re-triages, never blind-resubmits


# --- F3: PollTimeout verdict ---

def test_run_attempt_poll_timeout_verdict(tmp_path, monkeypatch):
    """After max_polls PENDING responses, verdict is PollTimeout (not Rejected)."""
    from telperion.prove2me.api import PlatformDown
    responses = [
        HttpResponse(200, json.dumps({"submission_id": "s_pt"})),
        HttpResponse(200, json.dumps({"status": "PENDING"})),
        HttpResponse(200, json.dumps({"status": "PENDING"})),
    ]
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                      _sleep=lambda s: None, max_polls=2)
    assert rec.verdict == "PollTimeout"
    assert "2 polls" in rec.server_output
    assert rec.submission_id == "s_pt"
    assert led.records()[0].verdict == "PollTimeout"
    # PollTimeout counts as attempted (no-repeat rule)
    assert led.attempted("m1")


# --- F1: SubmittedUnknown on 5xx burst after verify ---

def test_run_attempt_submitted_unknown_on_5xx_after_verify(tmp_path, monkeypatch):
    """If verify() succeeds but verdict poll raises PlatformDown, ledger
    SubmittedUnknown with the submission_id, then re-raise PlatformDown."""
    from telperion.prove2me.api import PlatformDown

    # verify returns OK; 4 × 500 responses exhaust backoff -> PlatformDown
    five_xx = [HttpResponse(500, "err")] * 4
    responses = [HttpResponse(200, json.dumps({"submission_id": "s_unk"}))] + five_xx
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)

    with pytest.raises(PlatformDown):
        run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                    _sleep=lambda s: None)

    # Ledger must contain SubmittedUnknown with the submission_id
    records = led.records()
    assert records, "ledger must not be empty after SubmittedUnknown"
    assert records[-1].verdict == "SubmittedUnknown"
    assert records[-1].submission_id == "s_unk"
    # No-repeat rule must fire
    assert led.attempted("m1")


# --- F9: render_solution and check_solution_theorem strip := sorry variants ---

def test_render_solution_strips_bare_sorry():
    stmt = "theorem solution : (1 : ℚ) + 1 = 2 := sorry"
    src = render_solution(stmt, "by norm_num")
    assert ":= sorry" not in src
    assert "by norm_num" in src


def test_check_solution_theorem_allows_statement_with_bare_sorry_suffix():
    """Formal statement ending in `:= sorry` (captain placeholder) must be
    accepted after normalization — the sorry suffix is stripped before the
    verbatim check so CertifyRefused is not incorrectly triggered."""
    stmt_with_sorry = STMT + " := sorry"
    # check_solution_theorem should pass: sorry stripped from want, GOOD contains stmt
    check_solution_theorem(GOOD, stmt_with_sorry)


# --- F4: target_module I2 wired ---

def test_run_attempt_i2_target_module_wired(tmp_path, monkeypatch):
    """run_attempt with target_module matching an import in lean_source triggers
    CertifyRefused and ledgers it — no network call."""
    src_with_self_import = "import Theorems.Thm_m1\n" + GOOD
    c = _scripted_client(tmp_path, [])    # any request would IndexError
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)
    rec = run_attempt(c, ws, item, src_with_self_import, ("IdentityEmitter",), "hash",
                      led, no_submit=True, target_module="Theorems.Thm_m1",
                      _sleep=lambda s: None)
    assert rec.verdict == "CertifyRefused"
    assert "I2" in rec.server_output
    assert led.records()[0].verdict == "CertifyRefused"


def test_compose_submission_merges_imports_first():
    from telperion.prove2me.attempt import compose_submission
    preamble = "import Mathlib.Data.Real.Basic\nopen Real\n"
    emitted = "import Mathlib\n\ntheorem helper : (0:\u211d) \u2264 1 := by norm_num\n"
    stmt = "theorem solution : (0:\u211d) \u2264 1 := by sorry"
    out = compose_submission(preamble, emitted, stmt, "by exact helper")
    lines = out.splitlines()
    first_nonimport = next(i for i, ln in enumerate(lines)
                           if ln.strip() and not ln.startswith("import"))
    assert all(not ln.startswith("import") for ln in lines[first_nonimport:]), \
        "all imports must precede everything else"
    assert lines[0] == "import Mathlib.Data.Real.Basic"   # preamble imports first
    assert "import Mathlib" in out and out.count("import Mathlib\n") == 1
    assert "open Real" in out
    assert "theorem helper" in out
    assert "theorem solution : (0:\u211d) \u2264 1 := by exact helper" in out
    assert "sorry" not in out
