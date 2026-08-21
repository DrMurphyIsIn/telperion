"""LLM statement front-door (Phase 5): natural language -> a formal candidate
goal, then the deterministic core certifies-or-rejects it.

This closes the one capability Telperion genuinely lacks — autoformalizing a
*statement* — without weakening the trust model.  The division of labour is
strict:

* the **proposer** (an LLM, or a stub, or a lookup table) turns informal text
  into a candidate ``0 <= target`` over nonnegative symbols.  It only proposes
  the STATEMENT; it never touches the proof.
* the **deterministic core** (`prove_goal`) then certifies the candidate to a
  kernel-checkable Lean theorem, or refuses it with a FALSE (rational
  counterexample) / NOT_POLYA / CERTIFIABLE triage.

A wrong formalization therefore cannot yield a false theorem: it is either
rejected outright, or it produces a *checkable* theorem whose vacuity the
auditor (Phase 3) catches.  The default path is LLM-free — you inject a
proposer; `ollama_proposer` is an opt-in arm that reuses the evolve layer's
local Ollama client.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .prove import ProofResult, prove_goal

# A proposer maps informal text -> (target expr, symbols) for the goal 0 <= target.
Proposer = Callable[[str], "tuple[sp.Expr, Sequence[sp.Symbol]]"]


@dataclass(frozen=True)
class FormalizeResult:
    """Outcome of formalize: the committed formal statement + the proof attempt."""

    informal: str
    target: sp.Expr | None
    symbols: tuple[sp.Symbol, ...]
    proved: bool
    verdict: str
    lean: str | None = None
    emitter: str | None = None
    counterexample: dict | None = None
    hints: tuple[str, ...] = ()
    detail: str = ""

    def render(self) -> str:
        head = f'formalize {self.informal!r} -> 0 <= {self.target}'
        if self.proved:
            return f"{head}\n  PROVED via {self.emitter}"
        return f"{head}\n  {ProofResult(self.proved, self.verdict, self.lean, self.emitter, self.detail, self.counterexample, self.hints).render()}"


def formalize(
    informal: str,
    proposer: Proposer,
    *,
    name: str = "Goal",
    namespace: tuple[str, ...] | None = None,
) -> FormalizeResult:
    """Formalize an informal claim to a candidate goal, then certify-or-reject it.

    Raises whatever the proposer raises if it cannot produce a candidate (an
    honest failure — no fabricated statement).  Otherwise the deterministic core
    is the sole arbiter of whether the candidate becomes Lean.
    """
    target, symbols = proposer(informal)
    syms = tuple(symbols)
    res = prove_goal(target, syms, name=name, namespace=namespace)
    return FormalizeResult(
        informal=informal,
        target=target,
        symbols=syms,
        proved=res.proved,
        verdict=res.verdict,
        lean=res.lean,
        emitter=res.emitter,
        counterexample=res.counterexample,
        hints=res.hints,
        detail=res.detail,
    )


def ollama_proposer(
    symbols: Sequence[sp.Symbol],
    *,
    host: str = "http://localhost:11434",
    model: str = "qwen2.5-coder:7b",
    temperature: float = 0.2,
    seed: int = 0,
) -> Proposer:
    """Opt-in LLM proposer backed by the local Ollama client (evolve layer).

    Returns a proposer over the given nonnegative ``symbols``; the model is
    asked for a single sympy expression ``target`` such that ``0 <= target`` is
    the informal claim.  The output is parsed through the token whitelist
    (``safe_parse_expr``) — the model's raw text never reaches sympy's
    evaluating parser — so a malformed or unsafe proposal is rejected before it
    can reach the certifier.  This never runs unless explicitly constructed; the
    default `formalize` path is LLM-free.
    """
    from .evolve.ollama import OllamaClient
    from .parsing import safe_parse_expr

    syms = tuple(symbols)
    client = OllamaClient(host=host, model=model)
    sym_names = ", ".join(str(s) for s in syms)
    system = (
        "You formalize an informal inequality over NONNEGATIVE real variables "
        f"({sym_names}) into a single sympy expression `target` such that the "
        "claim is exactly `0 <= target`. Reply with ONLY the sympy expression, "
        "no prose, no code fences."
    )

    def _propose(informal: str) -> "tuple[sp.Expr, tuple[sp.Symbol, ...]]":
        text = client.chat(system=system, user=informal, temperature=temperature, seed=seed)
        if not text:
            raise ValueError("ollama proposer returned no candidate (is the server running?)")
        expr = safe_parse_expr(text.strip(), syms)
        return expr, syms

    return _propose
