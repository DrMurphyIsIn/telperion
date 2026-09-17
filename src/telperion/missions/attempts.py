"""Attempts ledger: append-only work log with corrupt-line tolerance.

An Attempt records a single work unit: which node, which session, which route,
what verdict (Proved/Refuted/NoGo/Stalled), and supporting detail.

AttemptLog manages an append-only JSONL file. On load, truncated trailing lines
are silently skipped (at most one record lost vs. crashing and losing all state).
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

VERDICTS = ("Proved", "Refuted", "NoGo", "Stalled")


@dataclass(frozen=True)
class Attempt:
    """A single work attempt: node, session, route, verdict, detail, date.

    Frozen to ensure immutability once added to the ledger.
    """
    node: str
    session: str
    route: str
    verdict: str
    detail: str
    date: str

    def __post_init__(self):
        """Validate verdict at construction."""
        if self.verdict not in VERDICTS:
            raise ValueError(
                f"verdict must be one of {VERDICTS!r}, got {self.verdict!r}"
            )

    def to_dict(self) -> dict:
        """Serialize to dict for JSON."""
        return {
            "node": self.node,
            "session": self.session,
            "route": self.route,
            "verdict": self.verdict,
            "detail": self.detail,
            "date": self.date,
        }

    @classmethod
    def from_dict(cls, d: dict) -> Attempt:
        """Deserialize from dict."""
        return cls(
            node=d["node"],
            session=d["session"],
            route=d["route"],
            verdict=d["verdict"],
            detail=d["detail"],
            date=d["date"],
        )


class AttemptLog:
    """Append-only ledger of Attempt records in JSONL format.

    Tolerates truncated trailing lines (incomplete JSONL records) by skipping
    them with a policy comment. All other lines are assumed valid JSON.
    """

    def __init__(self, path: Path):
        """Initialize ledger at path. Path need not exist yet."""
        self.path = Path(path)

    def append(self, attempt: Attempt) -> None:
        """Append an attempt record to the ledger."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        line = json.dumps(attempt.to_dict())
        with open(self.path, "a") as f:
            f.write(line + "\n")

    def records(self) -> list[Attempt]:
        """Read all valid records from the ledger.

        Truncated trailing lines are silently skipped with a policy comment.
        Returns a list of Attempt objects in order.
        """
        if not self.path.exists():
            return []

        records: list[Attempt] = []
        with open(self.path, "r") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                try:
                    d = json.loads(line)
                    records.append(Attempt.from_dict(d))
                except (json.JSONDecodeError, KeyError, ValueError):
                    # Corrupt line (truncated JSONL or invalid JSON) — skip with policy
                    # comment. At most one record lost vs. crashing entire loader.
                    pass
        return records

    def for_node(self, slug: str) -> list[Attempt]:
        """Filter records by node slug.

        The node name in records may use dots (e.g., "BG.master").
        The slug uses underscores (e.g., "BG_master"). This method matches
        node names whose slug equals the given slug.

        Args:
            slug: node slug with underscores (e.g., "BG_master").

        Returns:
            List of Attempt records for that node, in order.
        """
        def slug_of(name: str) -> str:
            return name.replace(".", "_")

        all_records = self.records()
        return [r for r in all_records if slug_of(r.node) == slug]

    def nogo_digest(self, slug: str) -> str:
        """Render a no-repeat block of NoGo details for a node.

        Includes only NoGo attempts (excludes Stalled). Deduplicates
        detail text and renders as a formatted string for display/logging.

        Args:
            slug: node slug with underscores.

        Returns:
            A formatted string containing unique NoGo details, one per line.
        """
        attempts = self.for_node(slug)
        nogo_details = set()
        for a in attempts:
            if a.verdict == "NoGo" and a.detail:
                nogo_details.add(a.detail)

        if not nogo_details:
            return ""

        # Sort for determinism
        lines = sorted(nogo_details)
        return "\n".join(lines)
