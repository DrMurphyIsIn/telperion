"""Read the independent judge's verdict out of a CI job log.

`mission comparator-record` used to take the run id, the theorem name and the kernel mode
on trust: it wrote whatever string it was handed, and nothing checked that the cited run
had actually passed on that node, let alone with that theorem.  The convention ("the island
theorem's fully-qualified name, exactly as the PASS line prints it") lived only in reviewers'
heads.  These functions turn it into a check.

The judge prints one line per node:

    COMPARATOR PASS island=rvm_bridge node=<slug> theorem=<thm> run=<id> kernel=<mode>

with `kernel` either `nanoda` (both kernels replayed the export) or `lean-kernel-only` (the
node declares `heavy_certificates = true`, so only the Lean kernel and the axiom whitelist
ran).  A failure prints `::error::COMPARATOR FAIL island=... node=... theorem=...`.

Two details matter when reading a log:

* The job log also contains the workflow's own `echo` of those templates, with the shell
  variables unexpanded (`node=$slug`).  Those are not verdicts and are skipped.
* Verdicts must be read from the JOB, never from the run's conclusion.  Pushing the record
  commit to the same pull request supersedes the run that validated the artifact, so the
  run's overall conclusion can be `cancelled` while the shard that judged this node passed
  (seen 2026-09-25 on cl/kwin: run 36169770951 cancelled, job 108204239961 successful).
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional

#: `kernel=` values the judge is allowed to print, mapped to the second kernel that ran.
KERNEL_MODES = {
    "nanoda": "nanoda",
    "lean-kernel-only": "none: heavy_certificates",
}

_PASS = re.compile(
    r"COMPARATOR PASS\s+island=(?P<island>\S+)\s+node=(?P<node>\S+)\s+"
    r"theorem=(?P<theorem>\S+)\s+run=(?P<run>\S+)\s+kernel=(?P<kernel>\S+)")
_FAIL = re.compile(r"COMPARATOR FAIL\s+island=(?P<island>\S+)\s+node=(?P<node>\S+)")
_UNEXPANDED = re.compile(r"\$\{?[A-Za-z_]")


@dataclass(frozen=True)
class Verdict:
    """One judged node, as the log states it."""
    island: str
    node: str
    theorem: str
    run: str
    kernel: str

    @property
    def second_kernel(self) -> str:
        """The `second_kernel` string this verdict implies, or "" for an unknown mode."""
        return KERNEL_MODES.get(self.kernel, "")


def parse_verdicts(text: str) -> Dict[str, Verdict]:
    """Every PASS verdict in a job log, by node slug.  Unexpanded templates are skipped."""
    out: Dict[str, Verdict] = {}
    for line in text.splitlines():
        if _UNEXPANDED.search(line):
            continue  # the workflow echoing its own `echo "COMPARATOR PASS ... node=$slug ..."`
        m = _PASS.search(line)
        if m:
            out[m.group("node")] = Verdict(m.group("island"), m.group("node"),
                                           m.group("theorem"), m.group("run"), m.group("kernel"))
    return out


def failed_nodes(text: str) -> List[str]:
    """Nodes the log reports as FAIL (templates skipped)."""
    return [m.group("node") for line in text.splitlines()
            if not _UNEXPANDED.search(line) for m in [_FAIL.search(line)] if m]


def check(text: str, *, node: str, theorem: str, run_id: str = "",
          expect_lean_kernel_only: Optional[bool] = None) -> List[str]:
    """Problems with recording `node`/`theorem` against this log.  Empty list means OK.

    `expect_lean_kernel_only` is what the caller believes (from the node's
    `heavy_certificates` flag and the `--lean-kernel-only` switch); when given, the log must
    agree, so a record can neither claim both kernels ran when only Lean did, nor the reverse.
    """
    errs: List[str] = []
    if node in failed_nodes(text):
        errs.append(f"the log reports COMPARATOR FAIL for {node}: a failing run must never be recorded")
    verdicts = parse_verdicts(text)
    v = verdicts.get(node)
    if v is None:
        others = ", ".join(sorted(verdicts)[:4]) or "none"
        errs.append(f"no COMPARATOR PASS line for {node} in this log "
                    f"(nodes judged here: {others}) -- wrong run, wrong shard, or it never passed")
        return errs
    if v.theorem != theorem:
        errs.append(f"the log says the judge asserted {v.theorem!r} for {node}, "
                    f"not {theorem!r}; record the theorem exactly as the PASS line prints it")
    if run_id and v.run != str(run_id):
        errs.append(f"the PASS line for {node} cites run {v.run}, not {run_id}")
    if v.kernel not in KERNEL_MODES:
        errs.append(f"unknown kernel mode {v.kernel!r} for {node}; expected one of "
                    f"{sorted(KERNEL_MODES)}")
    elif expect_lean_kernel_only is not None:
        lean_only = (v.kernel == "lean-kernel-only")
        if lean_only and not expect_lean_kernel_only:
            errs.append(f"the log says {node} was judged with kernel={v.kernel} (nanoda did NOT "
                        f"run), so the record must say so: pass --lean-kernel-only")
        if expect_lean_kernel_only and not lean_only:
            errs.append(f"--lean-kernel-only was given but the log says {node} was judged with "
                        f"kernel={v.kernel}, i.e. the second kernel DID run; drop the switch")
    return errs


@dataclass(frozen=True)
class JobVerdict:
    """What one shard job of a run says about a node."""
    job_id: str
    job_url: str = ""
    head_sha: str = ""
    verdict: Optional[Verdict] = None
    failed: bool = False
    #: False when the job's log could not be downloaded.  A job we could not read is not a
    #: job that said nothing: it may be the one holding the FAIL.
    readable: bool = True
    #: The log itself, so the caller can re-check the chosen job without downloading it twice.
    log: str = ""


def choose(jobs: List[JobVerdict], node: str):
    """(the job to cite, errors).  Scans EVERY job: silence from one is not consent.

    Refuses when any job reports the node as failed, when no job passed it, when two jobs
    disagree about the theorem or the kernel mode (a shard-split change or a matrix bug could
    judge one node twice), or when any job's log was unreadable -- that job could be the one
    with the FAIL.
    """
    errs: List[str] = []
    unreadable = [j.job_id for j in jobs if not j.readable]
    if unreadable:
        errs.append(f"could not read the log of job(s) {', '.join(unreadable)} in this run; one of "
                    "them may hold a FAIL for this node, so the run cannot be certified from here")
    failed = [j.job_id for j in jobs if j.failed]
    if failed:
        errs.append(f"job(s) {', '.join(failed)} report COMPARATOR FAIL for {node}: "
                    "a failing run must never be recorded")
    hits = [j for j in jobs if j.verdict is not None]
    if not hits:
        errs.append(f"no job in this run printed a COMPARATOR PASS for {node}")
        return None, errs
    shapes = {(j.verdict.theorem, j.verdict.kernel) for j in hits}
    if len(shapes) > 1:
        errs.append(f"{node} was judged by {len(hits)} jobs with disagreeing verdicts "
                    f"({sorted(shapes)}); refusing to pick one")
    return (None if errs else hits[0]), errs
