"""Phase 2 certifiable-fragment benchmark: measure Telperion's deterministic
solve rate, wall-clock, and honest coverage (triage distribution) over a curated
corpus of certificate-shaped inequalities.

The corpus is source-tagged; the seed entries are hand-authored certificate-shaped
inequalities (NOT claimed to be PutnamBench — real benchmark items plug in behind
the same `BenchmarkEntry` shape once their formal statements are ingested).
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.benchmark import (  # noqa: E402
    BenchmarkEntry,
    certifiable_seed_corpus,
    run_benchmark,
)

u = sp.Symbol("u", nonnegative=True)


def test_run_benchmark_reports_solve_rate_timing_and_triage_distribution():
    entries = [
        BenchmarkEntry("provable", (1 + u) / (u + 1) - sp.Rational(1) / (u + 2), (u,), "seed:test"),
        BenchmarkEntry("false_goal", u - 1, (u,), "seed:test"),
        BenchmarkEntry("rational_tie", (u - 1) ** 2 / (u + 1), (u,), "seed:test"),
    ]

    report = run_benchmark(entries)

    assert report.total == 3
    assert report.solved == 1                       # only the certifiable one
    assert report.solve_rate == sp.Rational(1, 3)
    # triage distribution accounts for every entry
    assert sum(report.triage_counts.values()) == 3
    assert report.triage_counts["PROVED"] == 1
    assert report.triage_counts["FALSE"] == 1
    # timing is recorded and non-negative, and totals consistently
    assert all(r.wall_s >= 0 for r in report.results)
    assert report.total_wall_s >= 0


def test_seed_corpus_is_nonempty_and_source_tagged():
    corpus = certifiable_seed_corpus()

    assert len(corpus) >= 5
    assert all(isinstance(e, BenchmarkEntry) for e in corpus)
    assert all(e.source.startswith("seed:") for e in corpus)


def test_backend_solves_a_majority_of_the_seed_corpus():
    # the seed corpus is deliberately certificate-shaped: the deterministic
    # backend should clear most of it with zero sampling.
    report = run_benchmark(certifiable_seed_corpus())

    assert report.solved >= 1
    assert report.solve_rate > sp.Rational(1, 2)
