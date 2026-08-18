"""Measurement harness: compare() runs evolve() trials times and returns aggregate metrics.

Metrics returned:
    kernel_green_rate  -- fraction of trials where champion scored >= 990 (certifying).
    median_evals       -- median evaluation count across trials (int).
    median_wall_s      -- median wall-clock seconds per trial (float, rounded to 3dp).
    found_novel_ratio  -- True if any champion's ratio_src is not in the ratio_pool.
                          Only possible when the LLM mutator invents a new ratio; always
                          False in the no-LLM (structured-only) arm.
"""
from __future__ import annotations

import statistics
import time

from .genome import NEAR_STAR_Q, UnimodalGenome
from .loop import evolve
from .mutate import StructuredMutator

# Default candidate pool for the no-LLM arm.
_DEFAULT_POOL = [NEAR_STAR_Q, "(2*s+1)/(2*s+3)", "(s+2)/(s+1)"]

# Seed genome used when a trial starts: deliberately non-certifying so the loop
# must climb from below.
_FAILING_SEED = UnimodalGenome("(2*s+1)/(2*s+3)", s0=3, lift_max=4)


def compare(
    cfg,
    *,
    trials: int,
    seed: int,
    ratio_pool=None,
) -> dict:
    """Run evolve() `trials` times and return aggregate performance metrics.

    Each trial starts from a FAILING seed genome so the loop must discover a
    certifying champion on its own.  The master RNG seed is offset per trial
    (seed+0, seed+1, ...) to keep trials independent while remaining fully
    reproducible.

    Args:
        cfg: EvolveConfig controlling islands, gens, use_llm.
        trials: Number of independent runs.
        seed: Base RNG seed; trial t uses seed+t.
        ratio_pool: List of ratio_src strings to draw from.  Defaults to
            _DEFAULT_POOL.  Pass a custom pool to the single-ratio novelty test.

    Returns:
        dict with:
            kernel_green_rate (float 0..1),
            median_evals (int),
            median_wall_s (float),
            found_novel_ratio (bool).
    """
    pool = ratio_pool if ratio_pool is not None else _DEFAULT_POOL
    mutator = StructuredMutator()

    evals_list: list = []
    walls_list: list = []
    greens = 0
    found_novel = False

    for t in range(trials):
        t0 = time.perf_counter()
        rep = evolve(
            _FAILING_SEED,
            mutator,
            cfg,
            seed=seed + t,
            ratio_pool=pool,
        )
        elapsed = time.perf_counter() - t0

        evals_list.append(rep.evaluations)
        walls_list.append(elapsed)

        if rep.champion_score >= 990:
            greens += 1

        champ_ratio = getattr(rep.champion, "ratio_src", None)
        if champ_ratio is not None and champ_ratio not in pool:
            found_novel = True

    return {
        "kernel_green_rate": greens / max(1, trials),
        "median_evals": int(statistics.median(evals_list)),
        "median_wall_s": round(statistics.median(walls_list), 3),
        "found_novel_ratio": found_novel,
    }
