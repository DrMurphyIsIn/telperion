"""Append-only jsonl record of every prove2.me attempt (spec section 5).

Same convention as telperion.ledger.RouteLedger (dead ends as durable data),
but jsonl and keyed for the bridge's three consumers: triage ranking
(win_rate), the no-repeat rule (attempted/rejected), and `p2m status`.
This record shape deliberately seeds sub-project A's mission registry.
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path

_WINS = ("Proved", "Disproved")
_LOSSES = ("Rejected", "BuildFailed", "CertifyRefused")


@dataclass(frozen=True)
class AttemptRecord:
    milestone_id: str
    mission_id: str
    emitters: tuple[str, ...]
    lift_hash: str
    verdict: str          # Proved | Disproved | Rejected | BuildFailed | CertifyRefused | DryRun
    server_output: str
    wall_s: float
    submission_id: str
    date: str


class AttemptLedger:
    def __init__(self, path: Path):
        self.path = Path(path)
        self._records: list[AttemptRecord] = []
        if self.path.exists():
            for line in self.path.read_text().splitlines():
                if line.strip():
                    d = json.loads(line)
                    d["emitters"] = tuple(d["emitters"])
                    self._records.append(AttemptRecord(**d))

    def append(self, rec: AttemptRecord) -> None:
        self._records.append(rec)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("a") as f:
            f.write(json.dumps(asdict(rec)) + "\n")

    def records(self) -> list[AttemptRecord]:
        return list(self._records)

    def attempted(self, milestone_id: str) -> bool:
        return any(r.milestone_id == milestone_id and r.verdict != "DryRun"
                   for r in self._records)

    def rejected(self, milestone_id: str) -> list[AttemptRecord]:
        return [r for r in self._records
                if r.milestone_id == milestone_id and r.verdict in _LOSSES]

    def win_rate(self, emitter: str) -> float | None:
        outcomes = [r.verdict in _WINS for r in self._records
                    if emitter in r.emitters and r.verdict != "DryRun"]
        if not outcomes:
            return None
        return sum(outcomes) / len(outcomes)

    def render_status(self) -> str:
        wins = [r for r in self._records if r.verdict in _WINS]
        lines = [f"attempts: {len(self._records)}  proved: {len(wins)}"]
        for r in self._records[-10:]:
            lines.append(f"  {r.date}  {r.milestone_id:<16} {r.verdict:<14} "
                         f"{','.join(r.emitters)}")
        return "\n".join(lines)
