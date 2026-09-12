"""Attempt pipeline (spec section 4): invariants I1-I5 as named, tested checks.

    probe -> certify -> emit   (existing Telperion pipeline, done by caller)
    -> I2/I3 source checks -> I1 local lake build -> POST /verify
    -> poll -> I4 annotate -> ledger (I5)

Every check raises rather than warns: an autonomous agent must refuse, not
proceed with a caveat.
"""
from __future__ import annotations

import datetime
import hashlib
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
    # Strip both `:= by sorry` and `:= sorry` so the caller's proof_body replaces it.
    stmt = re.sub(r":=\s*(by\s+)?sorry\s*$", "", stmt).rstrip()
    lines = [f"import {i}" for i in imports]
    lines += ["", f"{stmt} := {proof_body}", ""]
    return "\n".join(lines)


def compose_submission(preamble: str, emitted: str, formal_statement: str,
                       proof_body: str) -> str:
    """Compose solution.lean: merged imports FIRST (Lean requirement), then
    the theorem's preamble opens/defs, then the emitted supporting theorems
    (their import lines hoisted), then `theorem solution : <verbatim> := body`.

    The platform's preamble carries whatever the formal_statement needs to
    parse (targeted imports, `open` lines); the emitted file typically starts
    with `import Mathlib`. Duplicates are dropped, order preserved
    (preamble imports before emitted imports).
    """
    def split_imports(text: str) -> tuple[list[str], list[str]]:
        imports, rest = [], []
        for line in text.splitlines():
            (imports if re.match(r"\s*import\s+\S", line) else rest).append(line)
        return imports, rest

    pre_imports, pre_rest = split_imports(preamble or "")
    emit_imports, emit_rest = split_imports(emitted or "")
    seen: set[str] = set()
    merged_imports = []
    for line in pre_imports + emit_imports:
        key = " ".join(line.split())
        if key not in seen:
            seen.add(key)
            merged_imports.append(line.strip())
    solution = render_solution(formal_statement, proof_body, imports=())
    blocks = [
        "\n".join(merged_imports),
        "\n".join(pre_rest).strip(),
        "\n".join(emit_rest).strip(),
        solution.strip(),
    ]
    return "\n\n".join(b for b in blocks if b) + "\n"


def check_no_sorry(src: str) -> None:
    if re.search(r"\bsorry\b", src):
        raise InvariantViolation("I3: submission contains `sorry`")


def check_solution_theorem(src: str, formal_statement: str) -> None:
    if not re.search(r"\btheorem solution\b", src):
        raise InvariantViolation("I3: submitted theorem must be named `solution`")
    # Strip both `:= by sorry` and `:= sorry` from the want normalization so
    # the captain's placeholder proof body never blocks the verbatim check.
    want = " ".join(
        re.sub(r":=\s*(by\s+)?sorry\s*$", "", formal_statement.strip()).split()
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
    try:
        # Pre-warm the Mathlib binary cache; non-fatal if unavailable (cache miss
        # is not an error; first build simply compiles from source).
        runner(["lake", "exe", "cache", "get"], cwd=str(project_dir),
               capture_output=True, timeout=3600)
        r = runner(["lake", "build"], cwd=str(project_dir),
                   capture_output=True, timeout=3600)
    except subprocess.TimeoutExpired as exc:
        raise BuildFailed(f"I1: lake timed out in {project_dir}") from exc
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
    try:
        check_no_sorry(lean_source)
        check_solution_theorem(lean_source, item.statement)
        check_no_self_import(lean_source, target_module)
    except InvariantViolation as e:
        return record("CertifyRefused", str(e))

    # I1: green local build against the platform pin
    # Stable suffix prevents milestone_ids differing only in punctuation from colliding.
    suffix = hashlib.sha256(item.milestone_id.encode()).hexdigest()[:6]
    name = f"M{re.sub(r'[^A-Za-z0-9]', '', item.milestone_id)}_{suffix}"
    proj = workspace.scratch_project(name)
    (proj / name / f"{name}.lean").write_text(lean_source, encoding="utf-8")
    try:
        lake_build(proj)
    except BuildFailed as e:
        return record("BuildFailed", str(e))

    if no_submit:
        return record("DryRun")

    # I4: the explanation rides along with the submission itself (live
    # contract: `-F explanation=` on /verify; PATCH annotate remains for
    # later edits).
    submission_id = client.verify(lean_source, target_id=item.milestone_id,
                                  explanation=explanation)
    # F1: wrap the poll so a 5xx burst after verify() still ledgers the
    # fact that a submission was sent (SubmittedUnknown).
    try:
        for _ in range(max_polls):
            v = client.verdict(submission_id)
            status = v.get("status", "PENDING")
            if status != "PENDING":
                break
            _sleep(poll_interval_s)
        else:
            return record("PollTimeout",
                          f"poll timeout after {max_polls} polls",
                          submission_id)

        output = v.get("output", "")
        if status in ("Proved", "Disproved"):
            return record(status, output, submission_id)
        # I5: ledger the rejection; the CALLER re-triages -- never resubmit here.
        return record("Rejected", output, submission_id)
    except Prove2MeError as exc:
        # Submission was sent but verdict is unknown (e.g. 5xx burst on poll).
        # Ledger SubmittedUnknown so the no-repeat rule fires; re-raise so the
        # caller can surface the error rather than silently swallowing it.
        record("SubmittedUnknown", str(exc), submission_id)
        raise
