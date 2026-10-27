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
REQUIRED = ("Lean default kernel accepts the solution",
            "Nanoda kernel accepts the solution",
            "Your solution is okay!")


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
