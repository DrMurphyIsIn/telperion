"""Evolutionary certificate search over Telperion families.

Proposes certificate programs; the untrusted-by-design generator's output still
passes the identical certify/emit/lake-build gate. Nothing here is auto-frozen.
"""
from .config import EvolveConfig
from .genome import (
    NEAR_STAR_Q,
    SYMBOL,
    UnimodalGenome,
    complexity,
    from_llm_text,
    to_certificate,
    to_prompt_repr,
)

__all__ = [
    "EvolveConfig",
    "NEAR_STAR_Q",
    "SYMBOL",
    "UnimodalGenome",
    "complexity",
    "from_llm_text",
    "to_certificate",
    "to_prompt_repr",
]
