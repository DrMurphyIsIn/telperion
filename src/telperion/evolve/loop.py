"""Island MAP-Elites evolutionary loop (no LLM).

Each individual in a population is stored as a triple (score, genome, art)
so parent artifacts are always available without re-evaluating the genome.
evaluate_genome is called exactly once per genome per evaluation event.
"""
from __future__ import annotations

import random
from dataclasses import dataclass

from .archive import Cell, MapElites
from .genome import UnimodalGenome, complexity, to_certificate


@dataclass
class RunReport:
    champion: object
    champion_score: float
    archive: MapElites
    evaluations: int
    kernel_green: object = None  # bool | None


def evaluate_genome(g: UnimodalGenome, seed: int = 1) -> tuple:
    """Tier 0-2 evaluation for a unimodal genome.

    Returns:
        (score, tag, artifacts, cell)
        score >= 990 on certifying success (1000 - complexity).
        score < 0 on failure.
        cell.certifies mirrors success/failure.
    """
    cert, art = to_certificate(g)
    comp = complexity(g)
    cell = Cell(cert is not None, min(comp, 12))
    if cert is None:
        return -100.0, f"build failed: {art.get('error', '')[:60]}", art, cell
    return 1000.0 - comp, f"CERTIFIES (complexity={comp})", {}, cell


def evolve(
    seed_genome: UnimodalGenome,
    mutator,
    cfg,
    *,
    seed: int = 0,
    ratio_pool=None,
    kernel_gate=None,
) -> RunReport:
    """Island MAP-Elites loop over UnimodalGenomes.

    Each island maintains a population of (score, genome, art) triples.
    Elite migration moves the global best into each island each generation.
    ratio_pool allows the loop to swap ratio_src (structured mutator cannot
    invent new ratios on its own).

    Args:
        seed_genome: starting genome (may be non-certifying).
        mutator: object with .mutate(genome, artifacts, rng) -> genome.
        cfg: EvolveConfig.
        seed: master RNG seed; two calls with same seed give identical results.
        ratio_pool: list of ratio_src strings to sample from; defaults to
            [seed_genome.ratio_src].
        kernel_gate: optional callable champion -> (bool, dict); run on final
            champion if score >= 990 (Tier 3).

    Returns:
        RunReport with champion, champion_score, archive, evaluations,
        kernel_green.
    """
    rng = random.Random(seed)
    pool = ratio_pool if ratio_pool else [seed_genome.ratio_src]
    archive = MapElites()
    evals = 0

    def _eval_and_record(g: UnimodalGenome):
        """Evaluate g, insert into archive, increment evals counter."""
        nonlocal evals
        evals += 1
        score, tag, art, cell = evaluate_genome(g)
        archive.insert(cell, score, g)
        return score, art

    # -- Initialise islands ---------------------------------------------------
    # Each island: list of (score, genome, art).
    # Seeded deterministically per island from master seed so the order of
    # island init does not affect other islands' rng streams.
    islands = []
    island_count = max(1, cfg.islands)
    pop_size = 6  # small to keep tests fast

    for i in range(island_count):
        irng = random.Random(seed * 1000 + i)
        # Always include the seed genome in island 0 so a good seed propagates.
        init_genomes = [seed_genome] if i == 0 else []
        while len(init_genomes) < pop_size:
            init_genomes.append(
                UnimodalGenome(
                    irng.choice(pool),
                    irng.randint(0, 8),
                    irng.randint(0, 6),
                )
            )
        pop = []
        for g in init_genomes:
            sc, art = _eval_and_record(g)
            pop.append((sc, g, art))
        islands.append((irng, pop))

    # -- Generational loop ----------------------------------------------------
    for _gen in range(max(1, cfg.gens)):
        for idx, (irng, pop) in enumerate(islands):
            pop.sort(key=lambda t: t[0], reverse=True)
            nxt = list(pop[:2])  # elitism: keep top-2 unchanged

            while len(nxt) < len(pop):
                # Tournament selection: pick 3 candidates, take the best.
                candidates = irng.sample(pop, min(3, len(pop)))
                _, parent, parent_art = max(candidates, key=lambda t: t[0])
                child = mutator.mutate(parent, parent_art, irng)
                # Loop-level ratio exploration: structured mutator cannot
                # invent new ratio_src strings, so we swap with some probability.
                if irng.random() < 0.3:
                    child = UnimodalGenome(
                        irng.choice(pool), child.s0, child.lift_max, child.search_hi
                    )
                sc, art = _eval_and_record(child)
                nxt.append((sc, child, art))

            islands[idx] = (irng, nxt)

        # -- Elite migration: inject global best into each island's last slot --
        gb = archive.best()
        if gb is not None:
            gb_score, gb_genome = gb
            # Fetch artifacts for the global best genome (already evaluated;
            # we need the art for the injected individual). Re-evaluate only if
            # the genome isn't already represented in the current island pop
            # (checking by identity is O(1) for frozen dataclasses).
            for irng, pop in islands:
                already = any(ind[1] == gb_genome for ind in pop)
                if not already:
                    # Use empty artifacts for the migrant; mutator will adapt
                    # from it on the next generation.
                    pop[-1] = (gb_score, gb_genome, {})

    # -- Pick champion --------------------------------------------------------
    best = archive.best()
    champion, champ_score = (best[1], best[0]) if best else (seed_genome, float("-inf"))

    kernel_green = None
    if kernel_gate is not None and champ_score >= 990:
        kernel_green = kernel_gate(champion)[0]

    return RunReport(champion, champ_score, archive, evals, kernel_green)
