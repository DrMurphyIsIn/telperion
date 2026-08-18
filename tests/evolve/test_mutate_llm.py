"""Tests for LLMMutator."""
import random

from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import LLMMutator


class _StubClient:
    def __init__(self, reply):
        self.reply = reply

    def chat(self, system, user, temperature, seed, timeout=60.0):
        return self.reply


def test_llm_mutator_parses_valid_reply():
    reply = '{"ratio_src": "' + NEAR_STAR_Q.replace('"', '') + '", "s0": 6, "lift_max": 3}'
    m = LLMMutator(_StubClient(reply))
    out = m.mutate(UnimodalGenome(NEAR_STAR_Q, 5, 4), {"error": "try a larger s0"}, random.Random(0))
    assert out.s0 == 6 and out.lift_max == 3


def test_llm_mutator_returns_input_on_garbage():
    m = LLMMutator(_StubClient("the model rambled with no json"))
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    assert m.mutate(g, {}, random.Random(0)) == g


def test_llm_mutator_returns_input_on_none():
    m = LLMMutator(_StubClient(None))
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    assert m.mutate(g, {}, random.Random(0)) == g
