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
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

REQUIRED = ("Lean default kernel accepts the solution",
            "Nanoda kernel accepts the solution",
            "Your solution is okay!")

#: Owner ruling (fix round 1, 2026-10-27): a re-judge log must bind itself to ONE node and
#: ONE artifact digest, or a passing log from a different node (or an older artifact) could
#: be recorded against the wrong `[rejudge]`. The re-judge runner writes this line itself,
#: before Comparator starts; `mission rejudge-record` refuses a log without it.
#:
#: Step 0b Task 1 (2026-10-28): the header may ALSO carry `closure_sha256=<64-hex>`, written
#: by `rejudge_queue.sh` with the same function `mission rejudge-record` uses
#: (`provenance.closure_digest`). It is optional here so a pre-Task-1 header still matches;
#: `parse_rejudge_header` ignores it (unchanged 2-tuple), and `parse_rejudge_header_closure`
#: reads it separately.
_REJUDGE_HEADER_RE = re.compile(
    r"^REJUDGE-HEADER\s+node=(?P<node>\S+)\s+artifact_sha256=(?P<sha>[0-9a-fA-F]{64})"
    r"(?:\s+closure_sha256=(?P<csha>[0-9a-fA-F]{64}))?\s*$")

#: Step 0b Task 3 (2026-10-28): a log may carry `REJUDGE-ROUTE <token>` (written by
#: `nanoda_direct.run_direct` as `REJUDGE-ROUTE nanoda-direct`), naming how the log was
#: produced. Its ABSENCE means "comparator" -- every log `rejudge_queue.sh` wrote before this
#: line existed, and every log it writes now (it never writes this line itself).
_REJUDGE_ROUTE_RE = re.compile(r"^REJUDGE-ROUTE\s+(?P<route>\S+)\s*$")


def parse_rejudge_route(text: str) -> str:
    """The log's `REJUDGE-ROUTE <token>` line, or "comparator" when none matches."""
    for line in text.splitlines():
        m = _REJUDGE_ROUTE_RE.match(line.strip())
        if m:
            return m.group("route")
    return "comparator"


def _is_error_line(line: str) -> bool:
    return line.lstrip().lower().startswith(("error", "uncaught exception"))


def _accepts(lines: Sequence[str]) -> bool:
    """Every REQUIRED string is, after stripping, a WHOLE line of *lines* (not a substring:
    a single line holding all three must not pass)."""
    stripped = {l.strip() for l in lines}
    return all(req in stripped for req in REQUIRED)


def parse_comparator_log(text: str) -> str:
    """ONE Comparator part's log: "pass" iff every REQUIRED string is a whole line (after
    stripping) and no line signals an error.

    This is the per-part rule. `rejudge_queue.sh`'s `part_passed` applies it to each part's
    own log; `rejudge_log_verdict` applies it to each part block of a node log. Never use it
    on a whole multi-part node log: a log whose part 1 passed and part 2 was killed still
    holds every accept line once.

    The error check looks only at lines that, once leading whitespace is stripped, START
    with "error" or "uncaught exception" (case-insensitive) -- never merely a line that
    CONTAINS the word "error" somewhere, which would misfire on a theorem name, a Lean
    info/warning line, or (as seen in the real CI log) a GitHub Actions `::error::...`
    annotation -- that starts with "::", not "error", so it is correctly left alone.
    """
    lines = text.splitlines()
    if any(_is_error_line(l) for l in lines):
        return "fail"
    return "pass" if _accepts(lines) else "fail"


#: The per-part delimiter `rejudge_queue.sh` writes into a node's rejudge.log before each
#: part's own Comparator output (keep the two in step):
#:   ==================== REJUDGE-PART 3/9 <part-slug> (comparator exit 0, peak 6810160 kB) ====================
_PART_RE = re.compile(
    r"^=+ REJUDGE-PART (?P<i>\d+)/(?P<n>\d+) (?P<slug>\S+) "
    r"\(comparator exit (?P<rc>-?\d+)(?:,[^)]*)?\) =+$")


def rejudge_log_verdict(text: str, part_slugs: Sequence[str]) -> str:
    """A whole NODE log, as `rejudge_queue.sh` writes it: "pass" iff it holds exactly one
    REJUDGE-PART block per expected part, in order, and every block passes.

    *part_slugs* are the challenge slugs the node's bundle renders (nanoda forced on), in
    render order -- 1 for an ordinary node, 9 for the h8000 compositional ladder. Block k must
    be headed `REJUDGE-PART k/N <part_slugs[k-1]> (comparator exit 0, ...)` with N =
    len(part_slugs), and must contain all three accept lines as whole lines. No line anywhere
    in the log (header, any block, or the compositional-glue output after the last part) may
    be an error line. Any line naming REJUDGE-PART that is not a well-formed delimiter fails
    the log. Zero expected parts fails: there is nothing a pass could be about.

    Step 0b Task 3 (2026-10-28): branches on `parse_rejudge_route`. A nanoda-direct log (the
    seven nodes no Comparator bundle can consume) carries no REJUDGE-PART block at all --
    `part_slugs` is ignored, and the verdict comes from `nanoda_direct.verdict_of_log` instead,
    over the log's own `REJUDGE-EXPORT`/`REJUDGE-NANODA` sections.
    """
    if parse_rejudge_route(text) == "nanoda-direct":
        from . import nanoda_direct
        return nanoda_direct.verdict_of_log(text)
    want = list(part_slugs)
    lines = text.splitlines()
    if not want or any(_is_error_line(l) for l in lines):
        return "fail"
    blocks: List[Tuple[re.Match, List[str]]] = []
    for line in lines:
        if "REJUDGE-PART" in line:
            m = _PART_RE.match(line.strip())
            if m is None:
                return "fail"
            blocks.append((m, []))
        elif blocks:
            blocks[-1][1].append(line)
    if len(blocks) != len(want):
        return "fail"
    n = str(len(want))
    for k, ((m, body), slug) in enumerate(zip(blocks, want), 1):
        if (m.group("i") != str(k) or m.group("n") != n or m.group("slug") != slug
                or m.group("rc") != "0" or not _accepts(body)):
            return "fail"
    return "pass"


class RejudgeSetupError(Exception):
    """The node's expected re-judge parts cannot be determined (no island, render failed)."""


def island_of_artifact(telperion_root: Path, artifact: Path) -> str:
    """The judge island an artifact lives on: `examples/<island>/...` under *telperion_root*
    (in-tree and materialized islands), else an OUT_OF_TREE_ISLANDS island whose lean dir
    contains it. Raises RejudgeSetupError when it is on none."""
    from . import judge
    art = Path(artifact).resolve()
    try:
        rel = art.relative_to((Path(telperion_root) / "examples").resolve())
    except ValueError:
        rel = None
    if rel is not None and len(rel.parts) >= 2:
        return rel.parts[0]
    for name in judge.OUT_OF_TREE_ISLANDS:
        try:
            d = judge.island_dir(Path(telperion_root), name).resolve()
        except judge.JudgeError:
            continue
        if art.is_relative_to(d):
            return name
    raise RejudgeSetupError(f"artifact {art} is on no judge island under {telperion_root}")


def expected_part_slugs(campaign_root: Path, node, slug: str) -> List[str]:
    """The Comparator parts a nanoda-ON re-judge of *node* must run, in the queue's order.

    Rendered exactly as `rejudge_queue.sh` renders them: `build_bundle(<telperion root>,
    <island>, only=[slug], heavy=(judge_via == "heavy"), force_nanoda=True)` -- a per-PR node
    takes heavy=False plus force_nanoda. The telperion root is the campaign's grandparent
    (`<root>/missions/<campaign>`), the island the one the node's artifact lives on. Raises
    RejudgeSetupError when the bundle cannot be rendered, or renders a part with nanoda off.
    """
    from . import judge
    camp = Path(campaign_root).resolve()
    troot = camp.parent.parent
    if node.proof is None:
        raise RejudgeSetupError(f"{slug}: no artifact linked")
    island = island_of_artifact(troot, camp / node.proof.artifact)
    heavy = (getattr(node, "judge_via", "") or "").strip() == "heavy"
    try:
        b = judge.build_bundle(troot, island, only=[slug], heavy=heavy, force_nanoda=True)
    except Exception as exc:      # JudgeError, a registry error, a missing file ...
        raise RejudgeSetupError(f"{slug}: cannot render its bundle on island {island!r}: "
                                f"{type(exc).__name__}: {exc}") from exc
    if not b.challenges:
        raise RejudgeSetupError(f"{slug}: its bundle on island {island!r} renders no part")
    off = [c.slug for c in b.challenges if not c.nanoda]
    if off:
        raise RejudgeSetupError(f"{slug}: part(s) {off} render with nanoda off")
    # The queue's part order: `judge --configs` prints `shard(challenges, None)`, i.e. sorted
    # by slug (h8000: __compose, then __seg_h1000 .. __seg_h8000).
    return [c.slug for c in judge.shard(b.challenges, None)]


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


def parse_rejudge_header_closure(text: str) -> Optional[str]:
    """The `REJUDGE-HEADER` line's `closure_sha256=<64-hex>` field, lower-cased, or None
    when the (matching) header line carries no such field -- a log written before step 0b
    Task 1 bound the header to a closure digest."""
    for line in text.splitlines():
        m = _REJUDGE_HEADER_RE.match(line.strip())
        if m and m.group("csha"):
            return m.group("csha").lower()
    return None
