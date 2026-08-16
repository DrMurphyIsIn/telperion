"""The route ledger: dead ends as durable, shareable data.

The origin campaign's `*_nogo*.py` modules — every failed proof route
preserved with its refutation — repeatedly saved parallel sessions from
re-attempting Bethe-local bounds, degree-6 barriers, spectral truncation.
This module is that convention as infrastructure: an append-only, deduplicated
record of every refused approach (lift non-convergence with the tie that
blocks it, SOS refusals, exact counterexamples, relaxation verdicts), keyed by
a fingerprint of the target so entries survive renames and sessions.

A returning researcher (or agent) reads ROUTES.md and sees "lifting tried to
N=8: non-convergent, tie at u=1; SOS: outside the v1 class" instead of
spending an afternoon rediscovering it.  Writes are explicit (--ledger on the
CLI; record() in the API) — the tool never appends to files behind your back.
"""
from __future__ import annotations

import datetime
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class RouteEntry:
    target: str          # family name or expression text
    fingerprint: str     # stable hash of the target's content
    route: str           # e.g. polya_lift | sos | counterexample | relax | subdivide
    verdict: str         # e.g. NON_CONVERGENT | REFUSED | DISPROOF | ARITHMETIC
    detail: str
    date: str = ""


def fingerprint_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:16]


class RouteLedger:
    def __init__(self, path: Path | str):
        self.path = Path(path)
        self.entries: list[RouteEntry] = []
        if self.path.exists():
            doc = json.loads(self.path.read_text())
            self.entries = [RouteEntry(**e) for e in doc.get("entries", [])]

    def _key(self, e: RouteEntry) -> tuple:
        return (e.fingerprint, e.route, e.verdict, e.detail)

    def record(
        self, target: str, fingerprint: str, route: str, verdict: str, detail: str
    ) -> bool:
        """Append if new; returns True when a new entry was recorded."""
        entry = RouteEntry(
            target=target,
            fingerprint=fingerprint,
            route=route,
            verdict=verdict,
            detail=detail,
            date=datetime.date.today().isoformat(),
        )
        if any(self._key(e) == self._key(entry) for e in self.entries):
            return False
        self.entries.append(entry)
        return True

    def save(self) -> None:
        self.path.write_text(
            json.dumps(
                {"format": "telperion-routes-v1",
                 "entries": [asdict(e) for e in self.entries]},
                indent=1,
            )
            + "\n"
        )

    def render_md(self) -> str:
        out = [
            "# Route ledger",
            "",
            "Refused approaches, recorded so nobody re-attempts them blind.",
            "Entries are appended by `--ledger` runs of diagnose/relax/hunt;",
            "an entry is evidence about THAT fingerprint — re-derive after the",
            "target changes.",
            "",
        ]
        by_target: dict[str, list[RouteEntry]] = {}
        for e in self.entries:
            by_target.setdefault(f"{e.target} `[{e.fingerprint}]`", []).append(e)
        for target, entries in sorted(by_target.items()):
            out.append(f"## {target}")
            out.append("")
            for e in sorted(entries, key=lambda x: (x.route, x.date)):
                out.append(f"- **{e.route} → {e.verdict}** ({e.date}): {e.detail}")
            out.append("")
        if not self.entries:
            out.append("(no routes recorded yet)")
        return "\n".join(out)
