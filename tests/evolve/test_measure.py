from __future__ import annotations

from telperion.evolve.config import EvolveConfig
from telperion.evolve.measure import compare


def test_compare_returns_metrics_no_llm():
    cfg = EvolveConfig.default().__class__(islands=2, gens=6, use_llm=False)
    m = compare(cfg, trials=2, seed=0)
    assert 0.0 <= m["kernel_green_rate"] <= 1.0
    assert m["median_evals"] > 0
    assert "found_novel_ratio" in m


def test_compare_green_rate_with_good_pool():
    # Pool contains the known-good oracle ratio; champion should certify every trial.
    from telperion.evolve.genome import NEAR_STAR_Q
    cfg = EvolveConfig.default().__class__(islands=2, gens=8, use_llm=False)
    m = compare(cfg, trials=3, seed=7, ratio_pool=[NEAR_STAR_Q, "(2*s+1)/(2*s+3)"])
    assert m["kernel_green_rate"] == 1.0


def test_compare_wall_time_is_positive():
    cfg = EvolveConfig.default().__class__(islands=2, gens=4, use_llm=False)
    m = compare(cfg, trials=1, seed=99)
    assert m["median_wall_s"] > 0.0


def test_compare_found_novel_false_single_pool_entry():
    # When the pool has only a single ratio and seed genome uses it, found_novel stays False.
    from telperion.evolve.genome import NEAR_STAR_Q
    cfg = EvolveConfig.default().__class__(islands=2, gens=6, use_llm=False)
    m = compare(cfg, trials=2, seed=0, ratio_pool=[NEAR_STAR_Q])
    # champion must be in the pool, so novel = False
    assert m["found_novel_ratio"] is False
