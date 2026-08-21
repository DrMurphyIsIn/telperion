"""B2-evolve — the missing EVOLVE_RESULTS milestone, as a regression test.

`docs/EVOLVE_RESULTS_2026-08-18.md` recorded a one-off manual run showing the
structured (LLM-free) evolve loop reliably climbs to a certifying champion, but
nothing was frozen and it was never a test.  This locks it: the seeded loop
DETERMINISTICALLY discovers a certifying near-star champion, and that champion
EMITS lint-clean Lean (the reusable ratio certificate) ready for the cloud kernel
gate.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.evolve.freeze import (  # noqa: E402
    discover_nearstar_champion,
    emit_champion_certificate,
    build_frozen_lean,
)
from telperion.evolve.genome import to_certificate  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


@pytest.fixture(scope="module")
def champion():
    # one shared seeded run reused across tests (the loop is the slow part)
    return discover_nearstar_champion(seed=0)


def test_seeded_evolve_is_reproducible(champion):
    again = discover_nearstar_champion(seed=0)
    assert (champion.champion.ratio_src, champion.champion.s0, champion.champion.lift_max) == \
           (again.champion.ratio_src, again.champion.s0, again.champion.lift_max)


def test_seeded_evolve_finds_a_certifying_champion(champion):
    assert champion.champion_score >= 990
    cert, _ = to_certificate(champion.champion)
    assert cert is not None


def test_champion_emits_lint_clean_certificate(champion):
    body, n, cert = emit_champion_certificate(champion.champion)
    assert n >= 2  # _dec + at least one crossing fact
    errors = [i for i in lint_lean_text(body) if i.severity == "error"]
    assert errors == [], errors


def test_frozen_lean_bundles_the_prelude_and_the_certificate(champion):
    text = build_frozen_lean(champion.champion)
    assert "unimodal_peak" in text          # the reusable prelude lemma
    assert "evolve_nearstar_dec" in text     # the emitted Pólya step
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
