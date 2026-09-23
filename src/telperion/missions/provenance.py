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
    has_grant: bool

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
            has_grant=n.grant is not None,
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
    covered = [r for r in proved if r.comparator_run and not r.comparator_stale]
    if covered:
        lines.append(f"  ({len(covered)} proved node(s) covered by a passing Comparator run)")
    return "\n".join(lines) + "\n"
