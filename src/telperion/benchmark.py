"""Certifiable-fragment benchmark (Phase 2): Telperion's deterministic solve
rate, wall-clock, and honest coverage over a curated corpus of
certificate-shaped inequalities.

The bet-#2 artifact: a table of *what the deterministic backend clears with zero
sampling, in CPU-seconds* — set beside a stochastic prover's pass@N numbers on
the same items.  Honesty rules baked in:

* Every entry is source-tagged.  The seed corpus is hand-authored,
  certificate-shaped inequalities (source ``seed:*``) — it is NOT PutnamBench.
  Real benchmark items plug in behind the same ``BenchmarkEntry`` once their
  formal statements are ingested (a data step, ideally networked/cloud).
* The report keeps the full triage distribution, so un-solved entries are
  visible as NOT_POLYA / FALSE / CERTIFIABLE rather than hidden — coverage is
  reported, never rounded away.
"""
from __future__ import annotations

import time
from collections import Counter
from dataclasses import dataclass
from typing import Sequence

import sympy as sp

from .prove import prove_goal


@dataclass(frozen=True)
class BenchmarkEntry:
    """One goal ``0 <= target`` over nonnegative ``symbols`` with provenance."""

    name: str
    target: sp.Expr
    symbols: tuple[sp.Symbol, ...]
    source: str


@dataclass(frozen=True)
class EntryResult:
    name: str
    source: str
    proved: bool
    verdict: str
    wall_s: float
    emitter: str | None


@dataclass(frozen=True)
class BenchmarkReport:
    total: int
    solved: int
    solve_rate: sp.Rational
    total_wall_s: float
    triage_counts: dict[str, int]
    results: list[EntryResult]

    def render(self) -> str:
        head = (
            f"certifiable-fragment benchmark: {self.solved}/{self.total} solved "
            f"deterministically ({float(self.solve_rate):.1%}) "
            f"in {self.total_wall_s:.3f}s total"
        )
        triage = "  triage: " + ", ".join(
            f"{k}={v}" for k, v in sorted(self.triage_counts.items())
        )
        rows = [
            f"  [{'OK ' if r.proved else '   '}] {r.name:20s} {r.verdict:24s} "
            f"{r.wall_s*1000:7.1f}ms  {r.source}"
            for r in self.results
        ]
        return "\n".join([head, triage, *rows])


def run_benchmark(entries: Sequence[BenchmarkEntry]) -> BenchmarkReport:
    """Run the deterministic backend over the corpus, timing each entry."""
    results: list[EntryResult] = []
    for e in entries:
        t0 = time.perf_counter()
        res = prove_goal(e.target, e.symbols, name=_lean_name(e.name))
        wall = time.perf_counter() - t0
        results.append(
            EntryResult(
                name=e.name,
                source=e.source,
                proved=res.proved,
                verdict=res.verdict,
                wall_s=wall,
                emitter=res.emitter,
            )
        )

    solved = sum(1 for r in results if r.proved)
    total = len(results)
    triage = dict(Counter(r.verdict for r in results))
    return BenchmarkReport(
        total=total,
        solved=solved,
        solve_rate=sp.Rational(solved, total) if total else sp.Rational(0),
        total_wall_s=sum(r.wall_s for r in results),
        triage_counts=triage,
        results=results,
    )


def certifiable_seed_corpus() -> list[BenchmarkEntry]:
    """Hand-authored, certificate-shaped inequalities (verified in-shape).

    Eight reduce to Pólya certificates; two are polynomial interior ties the SOS
    rung clears (the kind-router falls through to it); one is a rational interior
    tie kept in on purpose as an honest coverage boundary (NOT_POLYA — outside
    both the Pólya and polynomial-only SOS rungs), so the corpus reports what it
    cannot do, not just what it can.
    """
    u = sp.Symbol("u", nonnegative=True)
    v = sp.Symbol("v", nonnegative=True)
    R = sp.Rational
    return [
        BenchmarkEntry("ratio_a1", (1 + u) / (u + 1) - R(1) / (u + 2), (u,), "seed:rational-monotone"),
        BenchmarkEntry("ratio_a2", (2 + u) / (u + 1) - R(2) / (u + 2), (u,), "seed:rational-monotone"),
        BenchmarkEntry("ratio_a3", (3 + u) / (u + 1) - R(3) / (u + 2), (u,), "seed:rational-monotone"),
        BenchmarkEntry("diff_recip", R(1) / (1 + u) - R(1) / (2 + u), (u,), "seed:reciprocal-gap"),
        BenchmarkEntry("u_over_1pu", u / (1 + u), (u,), "seed:elementary"),
        BenchmarkEntry("u2_over_1pu", u**2 / (1 + u), (u,), "seed:elementary"),
        BenchmarkEntry("twovar_mono", R(1) / (2 + u) - R(1) / (2 + u + v), (u, v), "seed:twovar-monotone"),
        BenchmarkEntry("twovar_prod", (u * v) / ((1 + u) * (1 + v)), (u, v), "seed:twovar-product"),
        # polynomial interior ties: no Pólya cert, but perfect squares the SOS
        # rung clears (the kind-router falls through to it)
        BenchmarkEntry("tie_sq1", (u - 1) ** 2, (u,), "seed:interior-tie-sos"),
        BenchmarkEntry("tie_sq2", (2 * u - 1) ** 2, (u,), "seed:interior-tie-sos"),
        # honest coverage boundary: a RATIONAL interior tie — outside both the
        # Pólya and (polynomial-only) SOS rungs, so it triages NOT_POLYA
        BenchmarkEntry("rational_tie", (u - 1) ** 2 / (u + 1), (u,), "seed:coverage-boundary"),
    ]


def _lean_name(name: str) -> str:
    cleaned = "".join(c if c.isalnum() else "_" for c in name)
    return cleaned[:1].upper() + cleaned[1:] if cleaned else "Goal"
