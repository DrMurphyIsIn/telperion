"""Provenance: who wrote a statement, who read it back, and what the gate actually saw.

WHY (governance 2026-09-23, docs/AUDIT_INDEPENDENCE_2026-09-23.md). The read-back is the
one link in the proof chain no machine checks: it is the testimony that the formal statement
says what its title claims. `MISSIONS_DESIGN_2026-09-11.md` section 8 required the renderer
to be independent of the author, but nothing recorded who the author was, `--auditor` was
free text, and every testimony written 2026-09-19..22 came from a subagent of the authoring
session under the same git identity. The proofs themselves are fine; the point of this
module is to make self-certification VISIBLE and refuse it where it can be recognised.

Three records, all small and all in the node file:

  [author]     identity + session + date, written by `mission add`;
  [readback]   gains auditor_identity / auditor_session / independence, written by
               `mission audit`, which REFUSES an auditor matching the author;
  [grant]      artifact + statement digests, gate version, identity, session, date --
               written by the gate only; `mission verify` recomputes the digests.

Plus a `[comparator]` sidecar recording a passing independent-judge run (deliverable 2).

None of this is unforgeable. A session can supply any identity string for itself or for a
subagent. What it buys is a record the next reader can check against git and against the
attempts ledger, and a CLI that will not write a self-audit without being lied to.
"""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import List, Optional

from .schema import Author, ComparatorRecord, Grant, Node, Readback, SchemaError, load_node, save_node
from .statements import statement_path

#: Bumped whenever the gate's rule set changes in a way that makes an older grant weaker
#: than a fresh one. History:
#:   2026-09-23.1  first version that writes a [grant] block (digests + provenance) and
#:                 refuses a read-back whose auditor matches the author.
GATE_VERSION = "2026-09-23.1"

#: A read-back shorter than this is not a rendering of a formal statement; it is a label.
#: The shortest genuine read-back in the live registry on 2026-09-23 was 262 characters.
MIN_READBACK_CHARS = 120

#: Environment variable a session's id is taken from when `--session` is not given.
SESSION_ENV = "CLAUDE_SESSION_ID"


class SelfAuditError(SchemaError):
    """The auditor is the author (same session or same identity)."""


class ProvenanceError(SchemaError):
    """Missing or malformed provenance input (empty identity/session, unreadable file)."""


# ---------------------------------------------------------------------------
# Identity inputs
# ---------------------------------------------------------------------------

def git_identity(cwd: Optional[Path] = None) -> str:
    """`git config user.email` for *cwd*, or "" when git or the setting is absent."""
    try:
        out = subprocess.run(
            ["git", "config", "user.email"], cwd=str(cwd) if cwd else None,
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return out.stdout.strip() if out.returncode == 0 else ""


def session_id(explicit: Optional[str] = None) -> str:
    """The session id: `explicit` when given, else `$CLAUDE_SESSION_ID`, else ""."""
    if explicit and explicit.strip():
        return explicit.strip()
    return os.environ.get(SESSION_ENV, "").strip()


def require_identity(identity: str, session: str, what: str) -> None:
    """Raise ProvenanceError unless both strings are non-empty."""
    if not (identity or "").strip():
        raise ProvenanceError(
            f"{what}: identity is empty. It is taken from `git config user.email`; set it or "
            "pass --identity.")
    if not (session or "").strip():
        raise ProvenanceError(
            f"{what}: session is empty. Pass --session or set ${SESSION_ENV}.")


# ---------------------------------------------------------------------------
# Read-back content and independence
# ---------------------------------------------------------------------------

def _words(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


def readback_text_problem(text: str, title: str) -> str:
    """"" if *text* is a plausible read-back of a node titled *title*; else why not.

    Two shapes are refused: a text under MIN_READBACK_CHARS, and a text that merely repeats
    the title (equal to it, or contained in it, after case/punctuation folding). Neither is a
    rendering of the formal statement, which is the only thing the read-back exists to be.
    """
    t = (text or "").strip()
    if len(t) < MIN_READBACK_CHARS:
        return (f"read-back is {len(t)} characters; a rendering of a formal statement is at "
                f"least {MIN_READBACK_CHARS}. Say what the statement quantifies over and what "
                "it concludes, in your own words.")
    tw, titlew = _words(t), _words(title or "")
    if titlew and (tw == titlew or tw in titlew):
        return "read-back repeats the node title; a read-back must render the FORMAL statement, not restate the title."
    return ""


def independence_of(author: Optional[Author], identity: str, session: str) -> str:
    """Classify an auditor {identity, session} against the node's author.

    Returns "independent" when the node has an author and both fields differ, or
    "unverified" when the node has no [author] block (it predates the field, so nothing can
    be compared). Raises SelfAuditError when either field matches the author's.
    """
    if author is None:
        return "unverified"
    if session.strip() == author.session.strip():
        raise SelfAuditError(
            f"auditor session {session!r} is the author's session; a read-back must come from "
            "a different session (MISSIONS_DESIGN_2026-09-11.md section 8).")
    if identity.strip().lower() == author.identity.strip().lower():
        raise SelfAuditError(
            f"auditor identity {identity!r} is the author's identity; a read-back must come "
            "from a different principal, not a subagent of the author under the same account.")
    return "independent"


def readback_is_self_audit(node: Node) -> bool:
    """True iff the stored read-back names the author's session or identity.

    Only decidable when both the [author] block and the structured auditor fields exist;
    legacy read-backs (no structured fields) return False here and are reported as
    `unverified` instead.
    """
    rb, au = node.readback, node.author
    if rb is None or au is None:
        return False
    if rb.independence == "self":
        return True
    if rb.auditor_session and rb.auditor_session.strip() == au.session.strip():
        return True
    if rb.auditor_identity and rb.auditor_identity.strip().lower() == au.identity.strip().lower():
        return True
    return False


# ---------------------------------------------------------------------------
# Digests and the grant block
# ---------------------------------------------------------------------------

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Closure digest (step 0b Task 1, 2026-10-28)
#
# WHY. Before this, a [rejudge] record bound itself to the sha256 of the top-level
# artifact FILE alone (RejudgeRecord.artifact_sha256). For the ladders the certificates
# live in IMPORTED modules (Arb4_h8000 imports every segment's edge certificates; the
# Hodge1 capstones import a chain of LDL^T blocks), so a re-judge that is current on the
# artifact file can still be stale on what the artifact actually proves. The owner's fix:
# bind the record to a digest over the artifact's WHOLE import closure instead.
# ---------------------------------------------------------------------------

_REQUIRE_HEADER = "[[require]]"


def _require_paths_of(lakefile: Path) -> List[Path]:
    """`path = "..."` targets of every `[[require]]` block in *lakefile*, resolved
    relative to its directory (the same `path`-required siblings `judge.py` builds a
    workspace from -- e.g. zeta_reflection's `zzl_core`). A `[[require]]` block with a
    `git = "..."` dependency and no `path` (rvm_bridge's `Zeta23`) is skipped: it is
    fetched by `lake` from outside this repo, so this repo's git history has nothing to
    say about it, and the closure-digest back-fill rule (Task 2) could never ask."""
    lines = Path(lakefile).read_text().splitlines()
    out: List[Path] = []
    i = 0
    while i < len(lines):
        if lines[i].strip() == _REQUIRE_HEADER:
            j = i + 1
            path_val: Optional[str] = None
            while j < len(lines) and not lines[j].strip().startswith("["):
                m = re.match(r'^path\s*=\s*"([^"]*)"', lines[j].strip())
                if m:
                    path_val = m.group(1)
                j += 1
            if path_val:
                out.append((Path(lakefile).parent / path_val).resolve())
            i = j
        else:
            i += 1
    return out


def _require_path_dirs(lean_dir: Path) -> List[Path]:
    """Every package directory reachable from *lean_dir* through `path`-required
    siblings, transitively (zeta_reflection -> zzl_core -> zero_free_bridge is two
    hops). Does not include *lean_dir* itself."""
    seen = {Path(lean_dir).resolve()}
    out: List[Path] = []
    stack = [Path(lean_dir)]
    while stack:
        d = stack.pop()
        toml = d / "lakefile.toml"
        if not toml.is_file():
            continue
        for req in _require_paths_of(toml):
            rd = req.resolve()
            if rd not in seen:
                seen.add(rd)
                out.append(req)
                stack.append(req)
    return out


def closure_files(campaign_root: Path, node: Node) -> List[Path]:
    """Every local Lean source file *node*'s artifact imports, directly or
    transitively, plus the artifact itself -- the import closure a [rejudge] record is
    now bound to (Task 1).

    Resolved through the same machinery the judge uses: `judge.island_dir` for the
    artifact's island, `judge.module_name_of` for its module name, and
    `judge.import_closure` for the island-local closure. A module `import_closure`
    cannot resolve inside the island (not a local file there) is retried in every
    `path`-required sibling package, to a fixed point -- that is how zeta_reflection
    reaches `zzl_core`, and `zzl_core` in turn reaches `zero_free_bridge`.

    When the artifact is on no judge island at all (a unit-test fixture with no Lean
    project under it), the closure degrades to the artifact file alone: there is no
    island machinery to resolve its imports against, and no sibling package to look in.
    """
    if node.proof is None:
        raise ProvenanceError("closure_files: node has no proof link")
    campaign_root = Path(campaign_root).resolve()
    artifact = (Path(campaign_root) / node.proof.artifact).resolve()
    from . import judge
    from . import rejudge as _rejudge

    try:
        troot = campaign_root.parent.parent
        island = _rejudge.island_of_artifact(troot, artifact)
        lean_dir = judge.island_dir(troot, island)
        module = judge.module_name_of(lean_dir, artifact)
    except (_rejudge.RejudgeSetupError, judge.JudgeError):
        return [artifact] if artifact.is_file() else []

    dirs = [lean_dir] + _require_path_dirs(lean_dir)
    resolved_files: set = set()
    resolved_mods: set = set()
    frontier = {module}
    while frontier:
        new_frontier: set = set()
        for m in frontier:
            if m in resolved_mods:
                continue
            found_dir = None
            for d in dirs:
                if (d / (m.replace(".", "/") + ".lean")).is_file():
                    found_dir = d
                    break
            if found_dir is None:
                resolved_mods.add(m)          # external (e.g. Mathlib); nothing to open
                continue
            for sm in judge.import_closure(found_dir, m):
                if sm in resolved_mods:
                    continue
                f = found_dir / (sm.replace(".", "/") + ".lean")
                if f.is_file():
                    resolved_files.add(f.resolve())
                    resolved_mods.add(sm)
                else:
                    new_frontier.add(sm)       # not local to found_dir; try another dir
        frontier = new_frontier
    return sorted(resolved_files)


def closure_digest(campaign_root: Path, node: Node) -> str:
    """sha256 binding a [rejudge] record to *node*'s WHOLE import closure (Task 1):
    the concatenation of every closure file's path (relative to the telperion root, so
    the digest is the same wherever the repo is checked out) and its own sha256, in
    sorted path order. Changes if any closure file's CONTENT changes, or if the SET of
    closure files changes (an import added or removed)."""
    campaign_root = Path(campaign_root).resolve()
    troot = campaign_root.parent.parent
    files = closure_files(campaign_root, node)
    h = hashlib.sha256()
    for f in files:
        try:
            rel = f.relative_to(troot)
        except ValueError:
            rel = f
        h.update(str(rel).encode("utf-8"))
        h.update(b"\0")
        h.update(sha256_file(f).encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def build_grant(campaign_root: Path, node: Node, *, identity: str, session: str,
                today: Optional[str] = None) -> Grant:
    """The [grant] block for *node*: digests of the artifact and statement files as they are
    on disk RIGHT NOW, which is what the gate has just checked."""
    require_identity(identity, session, "grant")
    if node.proof is None:
        raise ProvenanceError("build_grant: node has no proof link")
    art = Path(campaign_root) / node.proof.artifact
    stmt = statement_path(campaign_root, node)
    return Grant(
        artifact_sha256=sha256_file(art),
        statement_sha256=sha256_file(stmt),
        gate_version=GATE_VERSION,
        date=today or date.today().isoformat(),
        identity=identity.strip(),
        session=session.strip(),
    )


def grant_digest_errors(campaign_root: Path, node: Node) -> List[str]:
    """Errors when a node's [grant] digests no longer match the files on disk. Empty when the
    node has no grant block (every node granted before 2026-09-23)."""
    g = node.grant
    if g is None:
        return []
    errs: List[str] = []
    if node.proof is None:
        return [f"has a [grant] block but no proof link"]
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        errs.append(f"[grant] names artifact {node.proof.artifact!r}, which does not exist")
    elif sha256_file(art) != g.artifact_sha256:
        errs.append(
            f"artifact {node.proof.artifact!r} has changed since the gate granted it "
            f"(grant sha256 {g.artifact_sha256[:12]}..., on disk {sha256_file(art)[:12]}...); "
            "the status rests on evidence nobody re-checked. Re-run `mission grant` after "
            "reopening, or restore the artifact.")
    stmt = statement_path(campaign_root, node)
    if not stmt.exists():
        errs.append("[grant] recorded a statement digest but the statement file is missing")
    elif sha256_file(stmt) != g.statement_sha256:
        errs.append(
            "statement file has changed since the gate granted this node "
            f"(grant sha256 {g.statement_sha256[:12]}..., on disk {sha256_file(stmt)[:12]}...)")
    return errs


def comparator_staleness(campaign_root: Path, node: Node) -> str:
    """A warning when the recorded Comparator verdict no longer describes the artifact on
    disk; "" otherwise (including when there is no record)."""
    c = node.comparator
    if c is None or node.proof is None:
        return ""
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return ""
    if sha256_file(art) != c.artifact_sha256:
        return (f"[comparator] run {c.run_id} judged a different artifact "
                f"(sha256 {c.artifact_sha256[:12]}..., on disk {sha256_file(art)[:12]}...); "
                "the independent verdict is stale until the job passes again")
    # A compositional verdict judged the PART modules (the implication and each segment), not
    # the artifact file: each one must still be the file the judge saw.
    for part in c.parts:
        f = parse_part_entry(part)
        mod, want = f.get("module", ""), f.get("sha256", "")
        if not mod or not want:
            return f"[comparator] compositional part entry without module/sha256: {part!r}"
        src = art.parent / (mod.replace(".", "/") + ".lean")
        if not src.exists():
            return f"[comparator] compositional part module {mod} no longer exists ({src.name})"
        if sha256_file(src) != want:
            return (f"[comparator] run {c.run_id} judged part {f.get('part')} with {mod} at "
                    f"sha256 {want[:12]}..., on disk {sha256_file(src)[:12]}...; the "
                    "compositional verdict is stale until the heavy judge passes again")
    return ""


def parse_part_entry(entry: str) -> dict:
    """`part=seg:h1000 slug=... theorem=... module=... sha256=... job=...` -> dict."""
    return dict(kv.split("=", 1) for kv in entry.split() if "=" in kv)


def required_ci_problem(campaign_root: Path, node: Node) -> str:
    """"" when the node declares no `requires_ci_job`, or its `[ci_record]` is a passing run
    of exactly that job on the artifact digest currently on disk; else why not."""
    req = (node.requires_ci_job or "").strip()
    if not req:
        return ""
    rec = node.ci_record
    if rec is None:
        return (f"requires a recorded passing run of CI job {req!r} (`mission ci-record`), "
                "and none is recorded")
    if rec.key != req:
        return f"requires CI job {req!r} but the record is for {rec.key!r}"
    if rec.conclusion != "success":
        return f"the recorded run {rec.run_id} of {req!r} concluded {rec.conclusion!r}, not success"
    if node.proof is None:
        return f"requires CI job {req!r} but the node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"requires CI job {req!r} but artifact {node.proof.artifact!r} does not exist"
    cur = sha256_file(art)
    if cur != rec.artifact_sha256:
        return (f"the recorded run {rec.run_id} of {req!r} was on artifact sha256 "
                f"{rec.artifact_sha256[:12]}..., but the artifact on disk is {cur[:12]}...; "
                "record a passing run on the current artifact")
    return ""


def judged_lean_kernel_only(node: Node) -> bool:
    """True when the node's `[comparator]` record says the judge ran with nanoda OFF.

    `second_kernel` starting with "none" (e.g. "none: heavy_certificates") is the record's
    reading; `kernel_mode = "lean-kernel-only"` is the literal token the PASS line printed.
    Either one means only the Lean kernel replayed the export.
    """
    c = node.comparator
    if c is None:
        return False
    return (c.second_kernel.strip().lower().startswith("none")
            or c.kernel_mode.strip() == "lean-kernel-only")


def needs_rejudge(node: Node) -> bool:
    """A node whose proved status needs a passing local nanoda re-judge.

    Final-fix 1 (whole-branch review, 2026-10-28): driven by the flag OR by the judge record.
    Before, deleting `heavy_certificates = true` from a node toml made `rejudge_problem`
    return "" -- a node judged Lean-kernel-only in CI then stayed proved with no nanoda run at
    all. A `[comparator]` record that says nanoda was off now makes the node heavy too.
    """
    return bool(node.heavy_certificates) or judged_lean_kernel_only(node)


def rejudge_problem(campaign_root: Path, node: Node) -> str:
    """"" unless a node judged without nanoda lacks a passing nanoda re-judge on its current
    artifact. "Judged without nanoda" = `heavy_certificates = true`, OR a `[comparator]`
    record whose second kernel was off (see `needs_rejudge`)."""
    if not needs_rejudge(node):
        return ""
    why = ("heavy_certificates" if node.heavy_certificates else
           f"judged Lean-kernel-only (second_kernel = {node.comparator.second_kernel!r}, "
           "heavy_certificates absent)")
    r = node.rejudge
    if r is None:
        return f"{why}: no local nanoda re-judge recorded (`mission rejudge-record`)"
    if r.verdict != "pass":
        return f"local nanoda re-judge on {r.date} FAILED (nanoda {r.nanoda_rev[:8]})"
    if node.proof is None:
        return "heavy node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"artifact {node.proof.artifact!r} does not exist"
    if sha256_file(art) != r.artifact_sha256:
        return (f"re-judge of {r.date} was on artifact sha256 {r.artifact_sha256[:12]}, "
                "which is no longer the artifact")
    # Task 1 (2026-10-28): a record must also be bound to the artifact's WHOLE import
    # closure, not only the top-level file -- a ladder capstone's certificates live in
    # imported modules. A record written before this field existed is not WRONG, just
    # unproven against the closure; back-fill (Task 2, git-verified unchanged) or re-judge.
    if not r.closure_sha256:
        return "re-judge predates closure binding; back-fill or re-judge"
    cur_closure = closure_digest(campaign_root, node)
    if cur_closure != r.closure_sha256:
        return (f"re-judge closure digest {r.closure_sha256[:12]}... no longer matches the "
                f"current import closure (now {cur_closure[:12]}...); back-fill or re-judge")
    return ""


# ---------------------------------------------------------------------------
# Migration and report
# ---------------------------------------------------------------------------

def migrate_unverified(campaign_root: Path) -> List[str]:
    """Set `independence = "unverified"` on every read-back that has no value. Idempotent.

    Returns the slugs changed. Does not touch status, text, auditor or date, and does not
    add the field to nodes without a read-back.
    """
    changed: List[str] = []
    nodes_dir = Path(campaign_root) / "nodes"
    for p in sorted(nodes_dir.glob("*.toml")):
        node = load_node(p)
        if node.readback is None or node.readback.independence:
            continue
        rb = Readback(
            text=node.readback.text, auditor=node.readback.auditor, date=node.readback.date,
            auditor_identity=node.readback.auditor_identity,
            auditor_session=node.readback.auditor_session,
            independence="unverified",
        )
        import dataclasses
        save_node(dataclasses.replace(node, readback=rb), p)
        changed.append(p.stem)
    return changed


@dataclass(frozen=True)
class ProvenanceRow:
    campaign: str
    slug: str
    status: str
    independence: str      # "independent" | "unverified" | "self" | "none" (no read-back)
    self_audit: bool
    comparator_run: str    # "" when no passing run is recorded
    comparator_stale: bool
    lean_kernel_only: bool
    #: How the record was checked when written ("" for records predating the checks).
    log_check: str
    head_check: str
    has_grant: bool
    #: The literal `kernel=` token the log printed, or "unstated" for a pre-#632 log.
    kernel_mode: str = ""
    #: "" = judged by the per-PR bundle; "heavy" = excluded from it by rule and judged by the
    #: dispatch-only heavy workflow (see judge.HEAVY_WORKFLOW).
    judge_via: str = ""
    #: "compositional" when the recorded verdict glued separately judged parts (compose.py).
    judge_mode: str = ""
    parts: int = 0

    @property
    def flagged(self) -> bool:
        """A proved node whose read-back is not known-independent and that no passing
        Comparator run vouches for."""
        if self.status != "proved":
            return False
        if self.comparator_run and not self.comparator_stale:
            return False
        return self.independence != "independent" or self.self_audit


def provenance_rows(campaign) -> List[ProvenanceRow]:
    rows: List[ProvenanceRow] = []
    for sl in sorted(campaign.nodes):
        n = campaign.nodes[sl]
        rb = n.readback
        if rb is None:
            ind = "none"
        elif readback_is_self_audit(n):
            ind = "self"
        else:
            ind = rb.independence or "unverified"
        rows.append(ProvenanceRow(
            campaign=campaign.cname, slug=sl, status=n.status, independence=ind,
            self_audit=readback_is_self_audit(n),
            comparator_run=n.comparator.run_id if n.comparator else "",
            comparator_stale=bool(comparator_staleness(campaign.root, n)),
            # Only the heavy marker means "nanoda did not run".  Testing != "nanoda" would
            # read ANY other value -- e.g. a legacy record's "unstated" -- as the stronger
            # claim that the second kernel was skipped.
            lean_kernel_only=bool(n.comparator
                                  and n.comparator.second_kernel.startswith("none")),
            has_grant=n.grant is not None,
            log_check=(n.comparator.log_check if n.comparator else ""),
            head_check=(n.comparator.head_check if n.comparator else ""),
            kernel_mode=(n.comparator.kernel_mode if n.comparator else ""),
            judge_via=getattr(n, "judge_via", "") or "",
            judge_mode=(n.comparator.judge_mode if n.comparator else ""),
            parts=(len(n.comparator.parts) if n.comparator else 0),
        ))
    return rows


def render_provenance_report(campaign) -> str:
    """Per campaign: every PROVED node whose read-back is unverified or self-audited and
    that no passing Comparator run covers, then a one-line count."""
    rows = provenance_rows(campaign)
    proved = [r for r in rows if r.status == "proved"]
    flagged = [r for r in proved if r.flagged]
    lines = [f"{campaign.cname}: {len(proved)} proved, {len(flagged)} without an independent "
             "read-back or a passing Comparator run"]
    for r in flagged:
        comp = f"comparator={r.comparator_run}{' (stale)' if r.comparator_stale else ''}" \
            if r.comparator_run else "comparator=-"
        lines.append(f"  {r.slug:<48} readback={r.independence:<11} {comp}"
                     f"{'' if r.has_grant else '  grant=legacy'}")
        if r.judge_via == "heavy":
            # A known state, not an oversight: the per-PR bundle excludes this node BY RULE.
            lines.append(f"  {'':<48} per-PR Comparator: not run by rule (judge_via = heavy); "
                         "judged by missions-comparator-heavy.yml"
                         f"{'' if r.comparator_run else ' -- no heavy-judge run recorded yet'}")
    covered = [r for r in proved if r.comparator_run and not r.comparator_stale]
    if covered:
        lines.append(f"  ({len(covered)} proved node(s) covered by a passing Comparator run)")
    # Driven from `heavy_certificates` (not from having a `[comparator]` block at all: a
    # heavy node can be proved with NO comparator record yet, e.g. AND_ladder_h11000_kernel
    # on the real registry, and must still be reported on). `lean_kernel_only` is kept as an
    # OR so a legacy record that marks itself Lean-kernel-only without the flag still shows.
    heavy_rows = [r for r in proved
                 if r.lean_kernel_only or needs_rejudge(campaign.nodes[r.slug])]
    for r in heavy_rows:
        node = campaign.nodes[r.slug]
        problem = rejudge_problem(campaign.root, node)
        comp = f"comparator={r.comparator_run}" if r.comparator_run else "comparator=-"
        if not problem and node.rejudge is not None:
            rj = node.rejudge
            lines.append(f"  {r.slug:<48} {comp} Lean kernel + nanoda "
                         f"(local re-judge {rj.date}, nanoda {rj.nanoda_rev[:8]})")
        else:
            suffix = f" -- {problem}" if problem else ""
            lines.append(f"  {r.slug:<48} {comp} Lean kernel only "
                         f"(heavy_certificates: nanoda not run){suffix}")
    for r in covered:
        weak = weak_record_reasons(r)
        if weak:
            lines.append(f"  {r.slug:<48} comparator={r.comparator_run} "
                         f"WEAKLY CHECKED: {'; '.join(weak)}")
    return "\n".join(lines) + "\n"


#: A Comparator record whose own checks were skipped or could not complete.  Not an error --
#: the record may be perfectly true -- but it must never read like a fully checked one.
def weak_record_reasons(row) -> List[str]:
    out = []
    if row.log_check == "skipped":
        out.append("written with --no-verify, so no judge log confirmed the theorem or kernel")
    elif row.log_check == "verified-offline":
        out.append("verified against a supplied log file; the job id is the recorder's word")
    if row.head_check == "unresolved":
        out.append("the artifact could not be hashed at the judged commit, so only the grant "
                   "pins the artifact")
    elif row.head_check == "skipped":
        out.append("the artifact was not checked at the judged commit")
    if row.kernel_mode == "unstated":
        out.append("the judge log predates the kernel field (#632), so it does not state "
                   "which second kernel ran")
    if row.comparator_run and not row.log_check and not row.head_check:
        out.append("predates the record checks (no log_check/head_check)")
    if getattr(row, "judge_mode", "") == "compositional":
        out.append(f"COMPOSITIONAL: the capstone's own proof was not replayed; its statement "
                   f"follows by a Comparator-checked implication from {max(row.parts - 1, 0)} "
                   "Comparator-checked segment statements, glued in telperion.missions.compose "
                   "(statement identity "
                   "by lean4export bytes, no certificate module in the implication's closure, "
                   "axioms per part)")
    return out
