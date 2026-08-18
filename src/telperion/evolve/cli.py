"""CLI entry point for `telperion evolve`."""
from __future__ import annotations

import argparse
from dataclasses import replace

from .config import EvolveConfig
from .genome import NEAR_STAR_Q, UnimodalGenome
from .loop import evolve
from .mutate import HybridMutator, LLMMutator, StructuredMutator
from .ollama import OllamaClient


def run_evolve(argv) -> int:
    """Parse argv and run the MAP-Elites evolve loop.

    Returns 0 if a certifying champion is found (score >= 990), else 1.
    """
    ap = argparse.ArgumentParser(prog="telperion evolve")
    ap.add_argument("--islands", type=int, default=4)
    ap.add_argument("--gens", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--model", default="qwen2.5-coder:7b")
    ap.add_argument("--no-llm", action="store_true")
    args = ap.parse_args(argv)

    cfg = replace(EvolveConfig.default(), islands=args.islands, gens=args.gens,
                  use_llm=not args.no_llm, model_tag=args.model)

    structured = StructuredMutator()
    llm = None
    if cfg.use_llm:
        client = OllamaClient(model=args.model)
        if client.available():
            llm = LLMMutator(client)
        else:
            print("[evolve] Ollama unreachable; structured-only fallback.")
    mutator = HybridMutator(llm=llm, structured=structured)

    seed_genome = UnimodalGenome(NEAR_STAR_Q, s0=5, lift_max=4)
    ratio_pool = [NEAR_STAR_Q, "(2*s+1)/(2*s+3)", "(s+2)/(s+1)"]
    report = evolve(seed_genome, mutator, cfg, seed=args.seed, ratio_pool=ratio_pool)

    print(
        f"[evolve] champion score {report.champion_score:.0f}  "
        f"({report.evaluations} evaluations, {cfg.islands} islands)"
    )
    print(f"[evolve] champion: {report.champion}")
    for cell, (s, _payload) in sorted(
        report.archive.cells().items(), key=lambda kv: -kv[1][0]
    )[:8]:
        tag = "CERTIFIES" if cell.certifies else "fails"
        print(f"    complexity_bin {cell.complexity_bin}: {tag}  score {s:.0f}")

    return 0 if report.champion_score >= 990 else 1
