import random
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import HybridMutator, StructuredMutator, LLMMutator


class _StubClient:
    def __init__(self, reply):
        self.reply = reply

    def chat(self, *a, **k):
        return self.reply


def test_hybrid_falls_back_to_structured_when_no_llm():
    m = HybridMutator(llm=None, structured=StructuredMutator())
    g = UnimodalGenome(NEAR_STAR_Q, 5, 2)
    out = m.mutate(g, {}, random.Random(3))
    assert isinstance(out, UnimodalGenome)  # produced a child, did not raise


def test_hybrid_refines_llm_proposal_through_structured():
    reply = '{"ratio_src": "' + NEAR_STAR_Q + '", "s0": 6, "lift_max": 3}'
    m = HybridMutator(
        llm=LLMMutator(_StubClient(reply)), structured=StructuredMutator(), llm_prob=1.0
    )
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    out = m.mutate(g, {}, random.Random(0))
    # structured refinement perturbs the LLM's s0=6 by at most 2
    assert abs(out.s0 - 6) <= 2 and 0 <= out.lift_max <= 6
