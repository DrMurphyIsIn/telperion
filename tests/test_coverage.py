"""B2-coverage — self-profiling: Telperion measuring its OWN coverage holes.

Run the deterministic backend over a corpus, then `diagnose` every refusal and
cluster the NOT_POLYA remedies into named gaps.  The output tells the tool where
to grow the next emitter — self-directed capability growth, deterministic.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.benchmark import certifiable_seed_corpus, run_benchmark  # noqa: E402
from telperion.coverage import (  # noqa: E402
    profile_coverage,
    classify_remedy,
    CoverageReport,
    CoverageGap,
)


def test_seed_corpus_surfaces_the_sos_interior_tie_gap():
    report = profile_coverage(certifiable_seed_corpus())
    sos_gaps = [g for g in report.gaps if "SOS" in g.remedy.upper()]
    assert sos_gaps, report.render()
    # the two interior-tie entries cluster into one gap
    assert sos_gaps[0].count == 2


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
    report = profile_coverage(certifiable_seed_corpus())
    text = report.render()
    assert isinstance(text, str)
    assert report.gaps[0].remedy in text
