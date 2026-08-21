"""Backend bridge (Phase 1): the request/response protocol an external prover
calls to discharge a certificate-shaped subgoal.

An LLM/RL prover (Goedel-Prover-V2, Seed-Prover, ...) runs a Lean-verifier loop.
When its search hits a goal of the shape ``0 <= <expr>`` — a polynomial or
rational inequality — it can hand that goal to Telperion instead of sampling a
tactic proof: `discharge` returns a spliceable, kernel-checkable auxiliary lemma
(sound by construction, deterministic, CPU-seconds) or an exact triage.

Contract (JSON-serializable both ways, so it crosses a process/tool boundary):

    request  = {"target": "<sympy expr>", "symbols": "u,v", "aux_name": "..."}
    response = {
        "proved": bool,
        "verdict": "PROVED" | "FALSE" | "NOT_POLYA_IN_THIS_FORM" | "CERTIFIABLE",
        "aux_lemma": "<complete Lean theorem>" | None,
        "emitter": "DirectPolyaEmitter" | "SOSEmitter" | None,
        "over_all_reals": bool,   # SOS lemma is `∀ x:ℝ,…`; Pólya carries `0≤x` binders
        "counterexample": {sym: value} | None,
        "hints": [str, ...],
        "detail": str,
    }

The Lean tactic that extracts the goal into a request and splices ``aux_lemma``
above the caller's goal (applying it with or without the nonnegativity
hypotheses per ``over_all_reals``) is the cloud-verified frontend; this module is
the tested Python seam.  No new trusted surface — `discharge` runs the same
enforced `prove_goal` pipeline; the Lean kernel remains the sole arbiter.
"""
from __future__ import annotations

import json
from typing import Sequence

import sympy as sp

from .parsing import safe_parse_expr
from .prove import prove_goal

# Emitters whose emitted theorem quantifies over ALL reals (no `0 ≤ x` binder).
_OVER_ALL_REALS_EMITTERS = {"SOSEmitter"}


def discharge(
    target: str | sp.Expr,
    symbols: str | Sequence[sp.Symbol],
    *,
    aux_name: str = "telperion_aux",
) -> dict:
    """Discharge ``0 <= target`` to a spliceable Lean lemma, or return the triage.

    ``target`` and ``symbols`` accept either the wire form (strings) or native
    sympy objects.  ``aux_name`` is the Lean name the emitted lemma carries so
    the frontend can apply it.
    """
    syms = _resolve_symbols(symbols)
    expr = safe_parse_expr(target, syms) if isinstance(target, str) else target

    res = prove_goal(expr, syms, name=aux_name, namespace=None)
    over_all_reals = res.emitter in _OVER_ALL_REALS_EMITTERS

    # counterexample values are exact sympy rationals — stringify them so the
    # whole response is JSON-serializable across a process/tool boundary.
    counterexample = (
        {k: str(v) for k, v in res.counterexample.items()}
        if res.counterexample is not None
        else None
    )

    return {
        "proved": res.proved,
        "verdict": res.verdict,
        "aux_lemma": res.lean,
        "emitter": res.emitter,
        "over_all_reals": over_all_reals,
        "counterexample": counterexample,
        "hints": list(res.hints),
        "detail": res.detail,
    }


def discharge_json(request: str) -> str:
    """Pure string->string wire wrapper over `discharge` for a process boundary."""
    req = json.loads(request)
    resp = discharge(
        req["target"],
        req.get("symbols", "u"),
        aux_name=req.get("aux_name", "telperion_aux"),
    )
    return json.dumps(resp)


def _resolve_symbols(symbols: str | Sequence[sp.Symbol]) -> tuple[sp.Symbol, ...]:
    if isinstance(symbols, str):
        return tuple(sp.Symbol(s.strip(), nonnegative=True) for s in symbols.split(","))
    return tuple(symbols)
