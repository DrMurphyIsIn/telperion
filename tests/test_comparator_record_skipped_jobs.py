"""comparator-record must ignore SKIPPED jobs (they never ran, GitHub keeps no log) but still refuse
when a job that DID run has an unreadable log.  Regression for the heavy targets mode (#716), whose
ladder-only `heavy-seg` and `verdict` jobs are skipped.  conjecture1_proved = False."""
import json
import subprocess

from telperion import cli

PASS = ("2026-10-13T14:39:55Z COMPARATOR PASS island=rvm_bridge node=MM_x theorem=thm_x "
        "run=111 kernel=lean-kernel-only\n")


def _fake_run_ok(jobs, logs):
    def run_ok(cmd, **kw):
        path = cmd[2]
        if path.endswith("/jobs?per_page=100"):
            return subprocess.CompletedProcess(cmd, 0, json.dumps({"jobs": jobs}), "")
        jid = path.split("/jobs/")[1].split("/")[0]
        if logs.get(jid) is None:
            return None                      # gh failed: no log available
        return subprocess.CompletedProcess(cmd, 0, logs[jid], "")
    return run_ok


def test_skipped_jobs_are_ignored(monkeypatch):
    jobs = [{"id": 1, "conclusion": "success", "head_sha": "abc"},
            {"id": 2, "conclusion": "skipped", "head_sha": "abc"},
            {"id": 3, "conclusion": "skipped", "head_sha": "abc"}]
    monkeypatch.setattr(cli, "_run_ok", _fake_run_ok(jobs, {"1": PASS}))
    monkeypatch.setattr(cli, "_gh_repo", lambda: "o/r")
    chosen, errs = cli._fetch_judge_job("111", "MM_x")
    assert errs == []
    assert chosen.job_id == "1" and chosen.verdict.theorem == "thm_x"


def test_unreadable_job_that_ran_still_blocks(monkeypatch):
    jobs = [{"id": 1, "conclusion": "success", "head_sha": "abc"},
            {"id": 2, "conclusion": "failure", "head_sha": "abc"}]
    monkeypatch.setattr(cli, "_run_ok", _fake_run_ok(jobs, {"1": PASS}))
    monkeypatch.setattr(cli, "_gh_repo", lambda: "o/r")
    chosen, errs = cli._fetch_judge_job("111", "MM_x")
    assert chosen is None and any("could not read the log" in e for e in errs)
