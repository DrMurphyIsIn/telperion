"""Self-profiling coverage report — Telperion measuring its own incompleteness.

Vector 3 (forward) of the self-application program.  Run the deterministic
backend over a corpus; for every refusal, take the `diagnose` remedy hints the
tool already produces and cluster them into NAMED gaps.  The largest gap is the
tool pointing at where its next emitter should grow — self-directed capability
growth, fully deterministic, no LLM.

The clustering is a small normal-form over the free-text hints so that, e.g., two
different interior-tie polynomials both land in a single "SOS" gap rather than
two singletons.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Sequence

from .benchmark import BenchmarkEntry, _lean_name
from .prove import prove_goal

# Ordered remedy rules: (canonical tag, keyword predicates).  First match wins,
# so put the most actionable / specific remedies first.
_REMEDY_RULES: list[tuple[str, tuple[str, ...]]] = [
    ("SOS / interior-tie (squares)", ("sos", "squares", "squared spelling", "even power")),
    ("box subdivision / tie isolation", ("subdivide", "bisect", "half-box", "corner")),
    ("FALSE — disprovable", ("counterexample", "is false", "disproof")),
]

_UNCATEGORIZED = "uncategorized — candidate for a new emitter shape"


def classify_remedy(hints: Sequence[str]) -> str:
    """Map a refusal's remedy hints to a single canonical gap tag."""
    text = " ".join(hints).lower()
    for tag, keys in _REMEDY_RULES:
        if any(k in text for k in keys):
            return tag
    return _UNCATEGORIZED


@dataclass(frozen=True)
class CoverageGap:
    """A named coverage hole: a remedy cluster, its size, and example targets."""

    remedy: str
    count: int
    examples: tuple[str, ...]


@dataclass(frozen=True)
class CoverageReport:
    total: int
    solved: int
    triage_counts: dict[str, int]
    gaps: list[CoverageGap]

    def render(self) -> str:
        head = (
            f"coverage: {self.solved}/{self.total} solved; "
            f"{self.total - self.solved} out-of-shape"
        )
        triage = "  triage: " + ", ".join(
            f"{k}={v}" for k, v in sorted(self.triage_counts.items())
        )
        if not self.gaps:
            return "\n".join([head, triage, "  no gaps — full coverage on this corpus"])
        rows = ["  gaps (largest first — grow these emitters):"]
        for g in self.gaps:
            rows.append(f"    {g.remedy} ({g.count}): {', '.join(g.examples)}")
        return "\n".join([head, triage, *rows])


def profile_coverage(entries: Sequence[BenchmarkEntry]) -> CoverageReport:
    """Profile the backend's coverage over `entries`, clustering refusals by
    remedy into named gaps sorted largest-first."""
    solved = 0
    verdicts: Counter[str] = Counter()
    clusters: dict[str, list[str]] = defaultdict(list)

    for e in entries:
        res = prove_goal(e.target, e.symbols, name=_lean_name(e.name))
        verdicts[res.verdict] += 1
        if res.proved:
            solved += 1
        else:
            clusters[classify_remedy(res.hints)].append(e.name)

    gaps = [
        CoverageGap(remedy=tag, count=len(names), examples=tuple(names))
        for tag, names in clusters.items()
    ]
    # deterministic order: largest first, then tag name
    gaps.sort(key=lambda g: (-g.count, g.remedy))

    return CoverageReport(
        total=len(entries),
        solved=solved,
        triage_counts=dict(verdicts),
        gaps=gaps,
    )
