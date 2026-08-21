"""Phase 1 backend bridge: the stable request/response protocol an external
prover (e.g. Goedel-Prover-V2) calls to discharge a certificate-shaped subgoal.

`discharge` wraps prove_goal into a JSON-serializable contract: goal in
(target string + symbol names, as a Lean frontend would extract via
metaprogramming), a spliceable auxiliary lemma out — or the FALSE / NOT_POLYA /
CERTIFIABLE triage.  The Lean tactic that extracts the goal and splices the
lemma is the cloud-verified frontend; this Python side is the tested seam.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.tactic import discharge, discharge_json  # noqa: E402


def test_discharge_returns_spliceable_aux_lemma_for_provable_goal():
    resp = discharge("(1 + u)/(u + 1) - 1/(u + 2)", "u", aux_name="telperion_aux_1")

    assert resp["proved"] is True
    assert resp["verdict"] == "PROVED"
    # the aux lemma is a complete Lean theorem carrying the requested name,
    # ready to splice above the caller's goal
    assert "theorem telperion_aux_1" in resp["aux_lemma"]
    # the frontend needs to know the binder shape to apply it
    assert resp["over_all_reals"] is False          # DirectPolya: nonneg-orthant


def test_discharge_reports_over_all_reals_for_sos_goal():
    # a polynomial interior tie routes to SOS, whose lemma is `∀ x : ℝ, ...`
    resp = discharge("(u - 1)^2", "u", aux_name="telperion_aux_2")

    assert resp["proved"] is True
    assert resp["over_all_reals"] is True


def test_discharge_returns_false_triage_with_counterexample():
    resp = discharge("u - 1", "u", aux_name="telperion_aux_3")

    assert resp["proved"] is False
    assert resp["verdict"] == "FALSE"
    assert resp["aux_lemma"] is None
    assert resp["counterexample"] is not None


def test_discharge_json_is_a_pure_string_to_string_wire_contract():
    request = json.dumps({"target": "u - 1", "symbols": "u", "aux_name": "aux"})
    response = discharge_json(request)

    # must be a JSON string round-tripping to the same dict discharge returns
    parsed = json.loads(response)
    assert parsed["proved"] is False
    assert parsed["verdict"] == "FALSE"
