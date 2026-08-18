from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import StructuredMutator
from telperion.evolve.config import EvolveConfig
from telperion.evolve.loop import evolve, evaluate_genome


def test_evaluate_greenoracle_scores_high():
    score, tag, art, cell = evaluate_genome(UnimodalGenome(NEAR_STAR_Q, 5, 4))
    assert cell.certifies is True and score >= 990


def test_evaluate_badratio_scores_negative_with_artifact():
    score, tag, art, cell = evaluate_genome(UnimodalGenome("(2*s+1)/(2*s+3)", 3, 4))
    assert cell.certifies is False and score < 0 and "error" in art


def test_evolve_finds_certifying_champion_no_llm():
    # Seed at a FAILING genome; the loop must climb to a certifying one.
    cfg = EvolveConfig.default().__class__(islands=2, gens=8, use_llm=False)
    seed = UnimodalGenome("(2*s+1)/(2*s+3)", 3, 4)  # non-decreasing -> fails
    # Provide the green ratio in the pool via a mutator that can swap ratio_src:
    report = evolve(seed, StructuredMutator(), cfg, seed=0,
                    ratio_pool=[NEAR_STAR_Q, "(2*s+1)/(2*s+3)"])
    assert report.champion_score >= 990
    cert_cell = report.archive.best()
    assert cert_cell is not None


def test_evolve_is_deterministic_under_seed():
    cfg = EvolveConfig.default().__class__(islands=2, gens=5, use_llm=False)
    seed = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    r1 = evolve(seed, StructuredMutator(), cfg, seed=42)
    r2 = evolve(seed, StructuredMutator(), cfg, seed=42)
    assert r1.champion == r2.champion and r1.champion_score == r2.champion_score
