"""UnimodalGenome: frozen certificate candidate with sympy ratio source."""
from __future__ import annotations

import json
from dataclasses import dataclass

import sympy as sp

from .. import unimodal_certificate, UnimodalityCertificate

SYMBOL = sp.Symbol("s", nonnegative=True)

# Verified green oracle: near-star tail consecutive ratio, decreasing for s>=5.
NEAR_STAR_Q = "486/529 * (1 + 1/(4*s**2 + 11*s + 6))**11"


@dataclass(frozen=True)
class UnimodalGenome:
    ratio_src: str
    s0: int
    lift_max: int
    search_hi: int = 50


def _parse_ratio(src: str):
    """Restricted parse: only the symbol s is in scope, no builtins."""
    return sp.sympify(src, locals={"s": SYMBOL}, evaluate=True)


def to_certificate(g: UnimodalGenome) -> tuple[UnimodalityCertificate | None, dict]:
    """Call unimodal_certificate; return (cert, artifacts).

    artifacts carries 'error' (the ValueError text) on failure.
    Total — never raises.
    """
    try:
        ratio = _parse_ratio(g.ratio_src)
    except Exception as e:  # noqa: BLE001
        return None, {"error": f"parse: {type(e).__name__}: {str(e)[:200]}"}
    try:
        cert = unimodal_certificate(
            ratio,
            s0=int(g.s0),
            s_symbol=SYMBOL,
            search_hi=int(g.search_hi),
            lift_max=int(g.lift_max),
        )
        return cert, {}
    except Exception as e:  # noqa: BLE001
        return None, {"error": f"{type(e).__name__}: {str(e)[:300]}"}


def complexity(g: UnimodalGenome) -> int:
    """Parsimony proxy: smaller crossover + fewer lifts = simpler Lean."""
    return int(g.s0) + int(g.lift_max)


def to_prompt_repr(g: UnimodalGenome) -> str:
    """Serialize to JSON for LLM consumption."""
    return json.dumps(
        {"ratio_src": g.ratio_src, "s0": g.s0, "lift_max": g.lift_max, "search_hi": g.search_hi},
        sort_keys=True,
    )


def from_llm_text(text: str) -> UnimodalGenome | None:
    """Deserialize from LLM text; total — None on unparseable.

    Tolerates a fenced code block or surrounding prose: grabs the first {...}.
    Rejects unparseable ratios early so a bad mutation is a miss, not a loop crash.
    """
    start, end = text.find("{"), text.rfind("}")
    if start < 0 or end <= start:
        return None
    try:
        d = json.loads(text[start : end + 1])
        g = UnimodalGenome(
            ratio_src=str(d["ratio_src"]),
            s0=int(d["s0"]),
            lift_max=int(d["lift_max"]),
            search_hi=int(d.get("search_hi", 50)),
        )
    except Exception:  # noqa: BLE001
        return None
    # Reject unparseable ratios early so a bad mutation is a miss, not a loop crash.
    try:
        _parse_ratio(g.ratio_src)
    except Exception:  # noqa: BLE001
        return None
    return g
