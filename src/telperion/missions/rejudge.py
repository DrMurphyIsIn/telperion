"""Verdict of a local Comparator re-judge, read from its log (never from a flag).

A `heavy_certificates` node's certificates exhaust a 16 GB CI runner under nanoda, so
hosted CI judges it Lean-kernel-only. The owner's rule: such a node stays proved only with
a passing local re-judge -- Comparator run with nanoda ON, on a large machine -- against its
CURRENT artifact. The verdict must come from what Comparator actually printed, not from an
operator-supplied flag, so this module reads the raw log text and nothing else.

Exact wording confirmed against a real `missions-comparator.yml` CI run (2026-10-27, run
39583777537, job "judge li_positivity 0/2"): a passing Comparator shard prints, in order,
"Nanoda kernel accepts the solution", "Lean default kernel accepts the solution", and
"Your solution is okay!" -- matching the strings below verbatim.
"""
from __future__ import annotations

import re
from typing import Optional, Tuple

REQUIRED = ("Lean default kernel accepts the solution",
            "Nanoda kernel accepts the solution",
            "Your solution is okay!")

#: Owner ruling (fix round 1, 2026-10-27): a re-judge log must bind itself to ONE node and
#: ONE artifact digest, or a passing log from a different node (or an older artifact) could
#: be recorded against the wrong `[rejudge]`. The re-judge runner writes this line itself,
#: before Comparator starts; `mission rejudge-record` refuses a log without it.
_REJUDGE_HEADER_RE = re.compile(
    r"^REJUDGE-HEADER\s+node=(?P<node>\S+)\s+artifact_sha256=(?P<sha>[0-9a-fA-F]{64})\s*$")


def parse_comparator_log(text: str) -> str:
    """"pass" iff every REQUIRED string appears as a line and no line signals an error.

    The error check looks only at lines that, once leading whitespace is stripped, START
    with "error" or "uncaught exception" (case-insensitive) -- never merely a line that
    CONTAINS the word "error" somewhere, which would misfire on a theorem name, a Lean
    info/warning line, or (as seen in the real CI log) a GitHub Actions `::error::...`
    annotation -- that starts with "::", not "error", so it is correctly left alone.
    """
    lines = text.splitlines()
    if any(l.lstrip().lower().startswith(("error", "uncaught exception")) for l in lines):
        return "fail"
    return "pass" if all(any(req in l for l in lines) for req in REQUIRED) else "fail"


def parse_rejudge_header(text: str) -> Optional[Tuple[str, str]]:
    """Find the `REJUDGE-HEADER node=<slug> artifact_sha256=<64-hex>` line.

    The re-judge runner writes this line before invoking Comparator, binding the log that
    follows to exactly one node and one artifact digest. Returns `(node, sha256)` -- `sha256`
    lower-cased -- from the first matching line, or `None` if no line matches.
    """
    for line in text.splitlines():
        m = _REJUDGE_HEADER_RE.match(line.strip())
        if m:
            return m.group("node"), m.group("sha").lower()
    return None
