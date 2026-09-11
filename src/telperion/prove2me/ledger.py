"""Append-only jsonl record of every prove2.me attempt (spec section 5).

Same convention as telperion.ledger.RouteLedger (dead ends as durable data),
but jsonl and keyed for the bridge's three consumers: triage ranking
(win_rate), the no-repeat rule (attempted/rejected), and `p2m status`.
This record shape deliberately seeds sub-project A's mission registry.

Verdict taxonomy
----------------
Wins (scored + count as attempted):
  Proved         — server accepted; kernel verified
  Disproved      — negation certificate accepted

Losses (scored + count as attempted):
  Rejected       — server rejected; re-triage
  BuildFailed    — local lake build failed; never submitted
  CertifyRefused — I2/I3 invariant blocked; never submitted

Unscored (count as attempted for no-repeat; EXCLUDED from win_rate):
  SubmittedUnknown — verify() succeeded but verdict poll raised before resolving
  PollTimeout      — poll budget exhausted; submission may still be processing

Not attempted (never counts as attempted or in win_rate):
  DryRun           — --no-submit; nothing sent to the platform
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path

_WINS = ("Proved", "Disproved")
_LOSSES = ("Rejected", "BuildFailed", "CertifyRefused")
# Unscored: count as attempted (no-repeat) but excluded from win_rate denominators.
# DryRun is excluded from both attempted() and win_rate.
_UNSCORED = ("DryRun", "SubmittedUnknown", "PollTimeout")


@dataclass(frozen=True)
class AttemptRecord:
    milestone_id: str
    mission_id: str
    emitters: tuple[str, ...]
    lift_hash: str
    verdict: str  # Proved | Disproved | Rejected | BuildFailed | CertifyRefused | DryRun | SubmittedUnknown | PollTimeout
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
                    try:
                        d = json.loads(line)
                        d["emitters"] = tuple(d["emitters"])
                        self._records.append(AttemptRecord(**d))
                    except json.JSONDecodeError:
                        # Interrupted append loses at most one truncated record.
                        # Deterministic recovery: skip corrupt line. Crashing on
                        # boot is worse than dropping a truncated record (advisory
                        # data; impact is deferred triage only).
                        continue

    def append(self, rec: AttemptRecord) -> None:
        self._records.append(rec)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("a") as f:
            f.write(json.dumps(asdict(rec)) + "\n")

    def records(self) -> list[AttemptRecord]:
        return list(self._records)

    def attempted(self, milestone_id: str) -> bool:
        """True if any non-DryRun record exists for this milestone.

        SubmittedUnknown and PollTimeout count as attempted (no-repeat rule):
        the platform may have received the submission; don't re-send blindly.
        """
        return any(r.milestone_id == milestone_id and r.verdict != "DryRun"
                   for r in self._records)

    def rejected(self, milestone_id: str) -> list[AttemptRecord]:
        return [r for r in self._records
                if r.milestone_id == milestone_id and r.verdict in _LOSSES]

    def win_rate(self, emitter: str) -> float | None:
        """Win rate for an emitter; excludes all _UNSCORED verdicts (DryRun,
        SubmittedUnknown, PollTimeout) from the denominator so ambiguous
        outcomes don't dilute the signal.
        """
        outcomes = [r.verdict in _WINS for r in self._records
                    if emitter in r.emitters and r.verdict not in _UNSCORED]
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
