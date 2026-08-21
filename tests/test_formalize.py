"""Phase 5 LLM statement front-door: close the one gap Telperion genuinely lacks
(natural-language -> formal statement) WITHOUT becoming a stochastic prover.

An LLM *proposer* maps informal text to a formal candidate goal; the
deterministic core then certifies-or-rejects it.  The LLM never touches the
proof — a wrong formalization is rejected by certification (or yields a
checkable, possibly-vacuous theorem the auditor catches).  Default is LLM-free:
you inject a proposer; the Ollama arm is opt-in.  The proposer seam is exactly
the Phase-1 prover seam applied to statements, so this is testable with a stub.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.formalize import formalize  # noqa: E402

u = sp.Symbol("u", nonnegative=True)


def _stub_proposer(informal: str):
    # a deterministic stand-in for the LLM: informal text -> (target, symbols)
    if "reciprocal" in informal:
        return sp.Rational(1) / (1 + u) - sp.Rational(1) / (2 + u), (u,)
    if "false" in informal:
        return u - 1, (u,)
    raise ValueError(f"stub cannot formalize: {informal!r}")


def test_formalize_proves_a_faithful_candidate():
    res = formalize("the reciprocal gap is nonnegative", proposer=_stub_proposer)

    assert res.proved is True
    assert res.verdict == "PROVED"
    assert "theorem" in res.lean
    # the formal statement it committed to is recorded for review
    assert res.target == sp.Rational(1) / (1 + u) - sp.Rational(1) / (2 + u)


def test_formalize_rejects_a_false_candidate_without_proving_it():
    # the LLM proposes a false statement; the deterministic core must refuse,
    # returning the FALSE triage rather than emitting anything.
    res = formalize("a false claim", proposer=_stub_proposer)

    assert res.proved is False
    assert res.verdict == "FALSE"
    assert res.lean is None
    assert res.counterexample is not None
