"""Attempt pipeline (spec section 4): invariants I1-I5 as named, tested checks.

    probe -> certify -> emit   (existing Telperion pipeline, done by caller)
    -> I2/I3 source checks -> I1 local lake build -> POST /verify
    -> poll -> I4 annotate -> ledger (I5)

Every check raises rather than warns: an autonomous agent must refuse, not
proceed with a caveat.
"""
from __future__ import annotations

import datetime
import re
import subprocess
import time
from pathlib import Path

from .api import Prove2MeClient, Prove2MeError
from .ledger import AttemptLedger, AttemptRecord
from .triage import QueueItem
from .workspace import Workspace


class InvariantViolation(Prove2MeError):
    """A hard submission invariant (I1-I5) would be violated; refused."""


class BuildFailed(Prove2MeError):
    """I1: local lake build failed; nothing was submitted."""


def render_solution(formal_statement: str, proof_body: str,
                    imports: tuple[str, ...] = ("Mathlib",)) -> str:
    stmt = formal_statement.strip()
    stmt = re.sub(r":=\s*by\s+sorry\s*$", "", stmt).rstrip()
    lines = [f"import {i}" for i in imports]
    lines += ["", f"{stmt} := {proof_body}", ""]
    return "\n".join(lines)


def check_no_sorry(src: str) -> None:
    if re.search(r"\bsorry\b", src):
        raise InvariantViolation("I3: submission contains `sorry`")


def check_solution_theorem(src: str, formal_statement: str) -> None:
    if not re.search(r"\btheorem solution\b", src):
        raise InvariantViolation("I3: submitted theorem must be named `solution`")
    want = " ".join(
        re.sub(r":=\s*by\s+sorry\s*$", "", formal_statement.strip()).split()
    )
    have = " ".join(src.split())
    if want not in have:
        raise InvariantViolation(
            "I3: submission does not contain the formal_statement verbatim "
            "(binders/conclusion must match the captain's statement exactly)"
        )


def check_no_self_import(src: str, target_module: str) -> None:
    if target_module and re.search(
            rf"^import\s+{re.escape(target_module)}\s*$", src, re.M):
        raise InvariantViolation(
            f"I2: submission imports its own target ({target_module})")


def lake_build(project_dir: Path, runner=subprocess.run) -> None:
    r = runner(["lake", "build"], cwd=str(project_dir),
               capture_output=True, timeout=3600)
    if r.returncode != 0:
        tail = (r.stdout + r.stderr).decode(errors="replace")[-2000:]
        raise BuildFailed(f"I1: lake build failed in {project_dir}:\n{tail}")


def run_attempt(
    client: Prove2MeClient,
    workspace: Workspace,
    item: QueueItem,
    lean_source: str,
    emitters: tuple[str, ...],
    lift_hash: str,
    ledger: AttemptLedger,
    no_submit: bool = False,
    explanation: str = "",
    poll_interval_s: float = 10.0,
    max_polls: int = 90,
    _sleep=time.sleep,
    target_module: str = "",
) -> AttemptRecord:
    t0 = time.monotonic()
    today = datetime.date.today().isoformat()

    def record(verdict: str, server_output: str = "", submission_id: str = "") -> AttemptRecord:
        rec = AttemptRecord(item.milestone_id, item.mission_id, tuple(emitters),
                            lift_hash, verdict, server_output,
                            round(time.monotonic() - t0, 2), submission_id, today)
        ledger.append(rec)
        return rec

    # I2 + I3: source checks before anything expensive
    check_no_sorry(lean_source)
    check_solution_theorem(lean_source, item.statement)
    check_no_self_import(lean_source, target_module)

    # I1: green local build against the platform pin
    name = f"M{re.sub(r'[^A-Za-z0-9]', '', item.milestone_id)}"
    proj = workspace.scratch_project(name)
    (proj / name / f"{name}.lean").write_text(lean_source)
    lake_build(proj)

    if no_submit:
        return record("DryRun")

    submission_id = client.verify(lean_source, target_id=item.milestone_id)
    for _ in range(max_polls):
        v = client.verdict(submission_id)
        status = v.get("status", "PENDING")
        if status != "PENDING":
            break
        _sleep(poll_interval_s)
    else:
        return record("Rejected", "poll timeout", submission_id)

    output = v.get("output", "")
    if status in ("Proved", "Disproved"):
        if explanation:
            client.annotate(submission_id, explanation)      # I4
        return record(status, output, submission_id)
    # I5: ledger the rejection; the CALLER re-triages -- never resubmit here.
    return record("Rejected", output, submission_id)
