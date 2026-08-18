"""StructuredMutator: deterministic programmatic mutation operators."""
from __future__ import annotations

import random

from .genome import UnimodalGenome


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
