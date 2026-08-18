import random
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import StructuredMutator


def test_mutation_stays_in_bounds_and_changes_something():
    m = StructuredMutator()
    g = UnimodalGenome(NEAR_STAR_Q, s0=5, lift_max=2)
    seen = {(''.join(str(m.mutate(g, {}, random.Random(i)).__dict__.values()))) for i in range(20)}
    assert len(seen) > 1  # explores
    for i in range(50):
        child = m.mutate(g, {}, random.Random(i))
        assert child.s0 >= 0 and 0 <= child.lift_max <= 6


def test_remedy_hint_biases_s0_up():
    m = StructuredMutator()
    g = UnimodalGenome(NEAR_STAR_Q, s0=3, lift_max=2)
    ups = sum(
        m.mutate(g, {"error": "ratio not certifiably decreasing (try a larger s0)"}, random.Random(i)).s0 > 3
        for i in range(40)
    )
    assert ups > 25  # strong upward bias when the certificate asks for it
