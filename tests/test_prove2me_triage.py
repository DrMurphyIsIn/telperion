"""Stage-1 triage: golden-corpus precision/recall, registry coverage, ranking."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.ledger import AttemptLedger, AttemptRecord  # noqa: E402
from telperion.prove2me.triage import (  # noqa: E402
    coverage_report,
    match_statement,
    registry_class_names,
    save_queue,
    load_queue,
    triage,
)

GOLDEN = json.loads(
    (Path(__file__).parent / "fixtures" / "prove2me" / "golden_statements.json")
    .read_text()
)["statements"]


def test_golden_corpus_matches_labels():
    misses = []
    for g in GOLDEN:
        conf, classes = match_statement(g["text"])
        matched = conf > 0
        if matched != g["match"]:
            misses.append((g["id"], "matched" if matched else "missed"))
        elif g["match"] and g["expect_any"]:
            if not set(classes) & set(g["expect_any"]):
                misses.append((g["id"], f"wrong classes {classes}"))
    assert not misses, f"golden corpus failures: {misses}"


def test_every_rule_class_exists_in_registry():
    rep = coverage_report()
    assert rep["unknown_rule_classes"] == [], (
        "SHAPE_RULES references emitters not in the registry"
    )


def test_unmatched_registry_classes_is_a_named_list():
    rep = coverage_report()
    assert isinstance(rep["unmatched_registry_classes"], list)  # named gap, not hidden


def test_registry_enumeration_is_nonempty_and_large():
    names = registry_class_names()
    assert "SOSEmitter" in names and len(names) >= 100   # 133 on main


def test_registry_includes_non_emit_module_emitters():
    names = registry_class_names()
    # TailNatEmitter lives in tails.py, not an emit*-prefixed module.
    # Confirms EXTRA_EMITTER_MODULES is scanned.
    assert "TailNatEmitter" in names
    assert "DichotomyGlueEmitter" in names
    assert "VarMapAdapterEmitter" in names


def test_exact_identity_does_not_match_lean_definition_syntax():
    # ':= (expr)' is a Lean definition — the old pattern r"=\s*[-\d(]" fires
    # on the '=' in ':=' when followed by '(' (e.g. ':= (n + 1)').
    # The negative lookbehind r"(?<!:)=\s*[-\d(]" blocks this.
    conf, classes = match_statement(
        "theorem solution (n : ℕ) : result := (n + 1)"
    )
    identity_classes = {"IdentityEmitter", "ExactFactEmitter", "RationalIdentityEmitter"}
    assert not (set(classes) & identity_classes), (
        f"exact-identity falsely fired on ':=' syntax: {classes}"
    )
    # Genuine numeric equality still fires correctly.
    _, classes2 = match_statement("theorem solution : (3 : ℚ)/4 + 1/4 = 1")
    assert set(classes2) & identity_classes


def test_coverage_report_exposes_import_failures():
    rep = coverage_report()
    assert "import_failures" in rep
    assert isinstance(rep["import_failures"], list)


def test_triage_ranks_skips_attempted_and_roundtrips(tmp_path):
    milestones = [
        {"id": "m1", "mission_id": "A", "status": "open",
         "formal_statement": "theorem solution : (1 : ℚ) + 1 = 2"},
        {"id": "m2", "mission_id": "A", "status": "open",
         "formal_statement": "theorem solution (G : Type*) [Group G] : True"},
        {"id": "m3", "mission_id": "B", "status": "open",
         "formal_statement": "theorem solution : ∀ x : ℝ, 0 ≤ x^2"},
    ]
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(AttemptRecord("m3", "B", ("SOSEmitter",), "h", "Rejected",
                             "", 1.0, "s", "2026-09-11"))
    q = triage(milestones, ledger=led)
    ids = [i.milestone_id for i in q]
    assert "m1" in ids          # identity-shaped: selected
    assert "m2" not in ids      # group theory: filtered
    assert "m3" not in ids      # already attempted: no-repeat
    save_queue(q, tmp_path / "queue.json")
    assert [i.milestone_id for i in load_queue(tmp_path / "queue.json")] == ids
