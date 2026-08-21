"""B2-coverage — self-profiling: Telperion measuring its OWN coverage holes.

Run the deterministic backend over a corpus, then `diagnose` every refusal and
cluster the NOT_POLYA remedies into named gaps.  The output tells the tool where
to grow the next emitter — self-directed capability growth, deterministic.

Note: whether the seed corpus's interior-tie entries are *solved* depends on
which optional backends are present (cvxpy/SDP for the SOS route) and the sympy
version, so the gap-surfacing tests use a CONTROLLED corpus with a guaranteed
refusal — a FALSE target no emitter can (or should) prove — making them robust to
the backend. The SOS-remedy classification is tested directly on `classify_remedy`.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.benchmark import BenchmarkEntry, certifiable_seed_corpus, run_benchmark  # noqa: E402
from telperion.coverage import (  # noqa: E402
    profile_coverage,
    classify_remedy,
    CoverageReport,
    CoverageGap,
)

_u = sp.Symbol("u", nonnegative=True)
# 0 <= u - 1 is FALSE (negative at u=0): a guaranteed refusal, independent of any
# optional SOS/SDP backend — the SOS route cannot and must not "prove" it.
_FALSE_CORPUS = [BenchmarkEntry("false_one", _u - 1, (_u,), "test:false")]


def test_controlled_refusal_surfaces_a_gap():
    report = profile_coverage(_FALSE_CORPUS)
    assert report.solved == 0
    assert sum(g.count for g in report.gaps) == 1
    assert "false_one" in report.gaps[0].examples


def test_gaps_account_for_exactly_the_unsolved_entries():
    entries = certifiable_seed_corpus()
    report = profile_coverage(entries)
    bench = run_benchmark(entries)
    unsolved = bench.total - bench.solved
    assert sum(g.count for g in report.gaps) == unsolved


def test_solved_count_matches_the_benchmark():
    entries = certifiable_seed_corpus()
    report = profile_coverage(entries)
    assert report.solved == run_benchmark(entries).solved


def test_gaps_are_sorted_by_count_descending():
    report = profile_coverage(certifiable_seed_corpus())
    counts = [g.count for g in report.gaps]
    assert counts == sorted(counts, reverse=True)


def test_classify_remedy_maps_sos_hint_to_an_sos_tag():
    hint = ("exact SOS certificate exists: numerator = 1*(u - 1)^2 — interior-tie",)
    assert "SOS" in classify_remedy(hint).upper()


def test_report_render_is_a_string_naming_the_top_gap():
    report = profile_coverage(_FALSE_CORPUS)  # guaranteed to have a gap
    text = report.render()
    assert isinstance(text, str)
    assert report.gaps[0].remedy in text
