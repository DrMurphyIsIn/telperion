"""Freeze an evolve-discovered champion into emittable Lean — the milestone the
`EVOLVE_RESULTS` write-up left open (search worked end-to-end, but nothing was
ever emitted/frozen).

`discover_nearstar_champion` runs the structured (LLM-free) island loop on the
near-star payload; it is deterministic in the seed.  `emit_champion_certificate`
renders the champion's reusable ratio certificate (the Pólya-decreasing step plus
the crossing facts) as kernel-checkable Lean via `UnimodalMaxEmitter`.
`build_frozen_lean` bundles those with the reusable `Telperion.unimodal_peak`
prelude into a self-contained file, ready for the cloud `lake build` gate.

Trust model unchanged: the loop only PROPOSES; every emitted theorem still faces
the identical kernel gate, and nothing here is auto-frozen into CI.
"""
from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace

from ..emit_unimodal import UNIMODAL_PRELUDE, UnimodalMaxEmitter
from ..lean import LeanProfile
from .config import EvolveConfig
from .genome import NEAR_STAR_Q, UnimodalGenome, to_certificate
from .loop import evolve
from .mutate import StructuredMutator

# The near-star payload from EVOLVE_RESULTS: a failing seed genome and the ratio
# pool the structured mutator samples from (it cannot invent a ratio itself).
_SEED_GENOME = UnimodalGenome(ratio_src="(2*s+1)/(2*s+3)", s0=3, lift_max=4)
_RATIO_POOL = [NEAR_STAR_Q, "(2*s+1)/(2*s+3)", "(s+2)/(s+1)"]


def discover_nearstar_champion(*, seed: int = 0, islands: int = 4, gens: int = 20):
    """Run the structured (LLM-free) evolve loop on the near-star payload.
    Deterministic in ``seed`` — same seed, same champion."""
    cfg = replace(EvolveConfig.default(), islands=islands, gens=gens, use_llm=False)
    return evolve(_SEED_GENOME, StructuredMutator(), cfg, seed=seed, ratio_pool=_RATIO_POOL)


def emit_champion_certificate(
    champion: UnimodalGenome,
    *,
    name: str = "evolve_nearstar",
    namespace: tuple[str, ...] = ("EvolveNearStar",),
) -> tuple[str, int, object]:
    """Render the champion's reusable ratio certificate as Lean.

    Returns ``(body, n_theorems, certificate)``.  Raises ValueError if the
    champion does not certify (a caller must only freeze a certifying champion)."""
    cert, _art = to_certificate(champion)
    if cert is None:
        raise ValueError("champion does not certify — nothing to emit")
    fam = SimpleNamespace(
        instances=[SimpleNamespace(payload=(cert, cert.s_star), lean_name=name)]
    )
    body, n = UnimodalMaxEmitter().emit_body(fam, LeanProfile(namespace=namespace))
    return body, n, cert


def build_frozen_lean(
    champion: UnimodalGenome,
    *,
    name: str = "evolve_nearstar",
    namespace: tuple[str, ...] = ("EvolveNearStar",),
) -> str:
    """A self-contained Lean file: imports + the reusable `unimodal_peak` prelude
    + the evolve-discovered ratio certificate, plus a documented note on the
    caller-supplied sequence application (the near-star `f` is not a rational
    function, so its definition and the final `unimodal_peak` invocation are the
    caller's one line — by design of `UnimodalMaxEmitter`)."""
    body, n, cert = emit_champion_certificate(champion, name=name, namespace=namespace)
    ns = namespace[0]
    note = (
        f"\n-- Evolve-discovered champion (structured/LLM-free, seed=0): "
        f"ratio_src = {champion.ratio_src}, s0 = {champion.s0}, "
        f"lift_max = {champion.lift_max}.\n"
        f"-- The {n} theorems above are the reusable ratio certificate "
        f"(Pólya-decreasing step + crossing of 1 at s* = {cert.s_star}).\n"
        f"-- To conclude `f n ≤ f {cert.s_star}` for the caller's sequence f, "
        f"apply `Telperion.unimodal_peak` against f's own definition.\n"
    )
    return (
        f"import Mathlib\n\n{UNIMODAL_PRELUDE}\n\n"
        f"namespace {ns}\n\n{body}{note}\nend {ns}\n"
    )
