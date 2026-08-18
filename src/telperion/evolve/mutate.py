"""StructuredMutator: deterministic programmatic mutation operators."""
from __future__ import annotations

import random

from .genome import UnimodalGenome, from_llm_text, to_prompt_repr


class StructuredMutator:
    """Deterministic programmatic operators. Always available, no dependencies."""

    def mutate(self, g: UnimodalGenome, artifacts: dict, rng: random.Random) -> UnimodalGenome:
        """Perturb s0 and lift_max, with upward bias on s0 if certificate hints at it.

        Args:
            g: UnimodalGenome to mutate.
            artifacts: dict that may carry "error" key with certificate feedback.
            rng: random.Random for deterministic control.

        Returns:
            Mutated UnimodalGenome with s0 >= 0 and 0 <= lift_max <= 6.
        """
        hint_up = "larger s0" in str(artifacts.get("error", ""))
        ds0 = rng.choice((1, 1, 2)) if hint_up else rng.choice((-1, 0, 1))
        s0 = max(0, g.s0 + ds0)
        lift_max = min(6, max(0, g.lift_max + rng.choice((-1, 0, 1))))
        return UnimodalGenome(g.ratio_src, s0, lift_max, g.search_hi)


_SYSTEM = (
    "You mutate a mathematical certificate for a UNIMODAL integer maximum. "
    "The genome is JSON: ratio_src (a rational function in the single variable s), "
    "s0 (integer threshold), lift_max (integer 0..6). The ratio must be DECREASING "
    "in s for s >= s0 with an all-nonnegative-integer numerator after clearing "
    "denominators. Propose ONE improved genome. Output ONLY the JSON object, no prose."
)


class LLMMutator:
    """LLM-driven mutation via artifact-fed prompts."""

    def __init__(self, client, temperature: float = 1.0):
        """Initialize with a client (duck-typed with .chat method).

        Args:
            client: Object with .chat(system, user, temperature, seed, timeout) method.
            temperature: LLM temperature (default 1.0).
        """
        self.client = client
        self.temperature = temperature

    def mutate(self, g: UnimodalGenome, artifacts: dict, rng: random.Random) -> UnimodalGenome:
        """Mutate via LLM; return input on client error or unparseable reply.

        Args:
            g: UnimodalGenome to mutate.
            artifacts: dict carrying fitness feedback (e.g., "error": "...", "remedy": "...").
            rng: random.Random for deterministic seed generation.

        Returns:
            Mutated UnimodalGenome on success, input g on error/garbage.
        """
        user = (
            "Current genome:\n" + to_prompt_repr(g) + "\n\n"
            "Last evaluation feedback:\n" + str(artifacts or {"note": "no feedback"}) + "\n\n"
            "Return an improved genome as JSON only."
        )
        reply = self.client.chat(
            _SYSTEM, user, temperature=self.temperature, seed=rng.randint(0, 2 ** 31 - 1)
        )
        if reply is None:
            return g
        cand = from_llm_text(reply)
        return cand if cand is not None else g
