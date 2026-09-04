"""Tests for the data-driven mechanical repair passes.

No Lean is invoked here - these exercise the pure-Python rename machinery:
  * the table loads from deprecations.json (and falls back to the seed);
  * the extractor parses the real Mathlib deprecated-alias shapes;
  * substitution is idempotent and word-boundary safe;
  * the div_le_iff seed rename still fires;
  * unknown-identifier failures surface as (non-applied) candidates.
"""
from __future__ import annotations

import json

import pytest

from telperion import repair
from telperion.deprecations import (
    RenameTable,
    extract_from_text,
    extract_renames,
)

DIV_LE_IFF0 = "div_le_iff" + "₀"


# ---- extractor: real Mathlib alias shapes -----------------------------------

def test_extract_inline_alias():
    src = '@[deprecated (since := "2026-05-27")] alias try_rfl := tryRfl\n'
    assert extract_from_text(src) == {"try_rfl": "tryRfl"}


def test_extract_protected_alias():
    src = '@[deprecated (since := "2026-01-06")] protected alias isAntisymm := antisymm\n'
    assert extract_from_text(src) == {"isAntisymm": "antisymm"}


def test_extract_multiline_attribute_then_alias():
    src = (
        '@[deprecated (since := "2026-02-24")]\n'
        "alias inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap\n"
    )
    assert extract_from_text(src) == {
        "inducedMap": "ConditionallyCompleteLinearOrderedField.inducedMap"
    }


def test_extract_message_and_sibling_attributes():
    src = '@[deprecated "use Foo" (since := "2026-02-21"), norm_cast] alias bar := Foo.baz\n'
    assert extract_from_text(src) == {"bar": "Foo.baz"}


def test_extract_ignores_deprecated_without_alias():
    # new-name and message forms attach to a `theorem`, not an alias -> no pair.
    src = (
        '@[deprecated toList_getElem (since := "2025-11-25")]\n'
        "theorem old_thm : True := trivial\n"
        '@[deprecated "Use simp" (since := "2025-11-22")]\n'
        "theorem other : True := trivial\n"
    )
    assert extract_from_text(src) == {}


def test_extract_renames_walks_tree(tmp_path):
    (tmp_path / "Mathlib").mkdir()
    (tmp_path / "Mathlib" / "A.lean").write_text(
        '@[deprecated (since := "2026-01-01")] alias a_old := a_new\n',
        encoding="utf-8",
    )
    (tmp_path / "Mathlib" / "B.lean").write_text(
        '@[deprecated (since := "2026-01-02")] alias b_old := b_new\n',
        encoding="utf-8",
    )
    table = extract_renames(tmp_path)
    assert isinstance(table, RenameTable)
    assert table.renames == {"a_old": "a_new", "b_old": "b_new"}
    assert table.files_scanned == 2
    assert table.alias_hits == 2


def test_extract_records_collision_last_write_wins(tmp_path):
    (tmp_path / "A.lean").write_text(
        '@[deprecated (since := "2026-01-01")] alias dup := first\n',
        encoding="utf-8",
    )
    (tmp_path / "B.lean").write_text(
        '@[deprecated (since := "2026-01-02")] alias dup := second\n',
        encoding="utf-8",
    )
    table = extract_renames(tmp_path)
    assert table.renames["dup"] == "second"
    assert "dup" in table.collisions
    assert set(table.collisions["dup"]) == {"first", "second"}


# ---- repair table loading ---------------------------------------------------

def test_table_loads_from_json(tmp_path, monkeypatch):
    fake = tmp_path / "deprecations.json"
    fake.write_text(
        json.dumps({"renames": {"old_lemma": "new_lemma"}}),
        encoding="utf-8",
    )
    monkeypatch.setattr(repair, "_DEPRECATIONS_JSON", fake)
    try:
        table = repair.reload_rename_table()
        assert table["old_lemma"] == "new_lemma"
        repaired, applied = repair.repair_lean("exact old_lemma h\n")
        assert repaired == "exact new_lemma h\n"
        assert ("old_lemma", "new_lemma", 1) in applied
    finally:
        # restore the real table for other tests / modules.
        monkeypatch.undo()
        repair.reload_rename_table()


def test_table_falls_back_to_seed_when_json_absent(tmp_path, monkeypatch):
    missing = tmp_path / "does_not_exist.json"
    monkeypatch.setattr(repair, "_DEPRECATIONS_JSON", missing)
    try:
        table = repair.reload_rename_table()
        assert table["div_le_iff"] == DIV_LE_IFF0
    finally:
        monkeypatch.undo()
        repair.reload_rename_table()


# ---- repair behaviour -------------------------------------------------------

def test_div_le_iff_rename_still_works():
    repair.reload_rename_table()
    repaired, applied = repair.repair_lean("rw [div_le_iff hb] at h\n")
    assert DIV_LE_IFF0 in repaired
    assert ("div_le_iff", DIV_LE_IFF0, 1) in applied


def test_repair_is_idempotent():
    repair.reload_rename_table()
    once, applied1 = repair.repair_lean("rw [div_le_iff hb, le_div_iff hc]\n")
    assert applied1  # something changed the first time
    twice, applied2 = repair.repair_lean(once)
    assert twice == once
    assert applied2 == []  # guard prevents any re-application


def test_repair_respects_word_boundary():
    repair.reload_rename_table()
    # `div_le_iff_of_...` is a different lemma and must NOT be touched.
    src = "exact div_le_iff_of_pos h\n"
    repaired, applied = repair.repair_lean(src)
    assert repaired == src
    assert applied == []


# ---- unknown-identifier candidate capture -----------------------------------

def test_candidate_capture_from_text():
    text = "error: R3Cert/Y.lean:10:1: unknown identifier 'dispatch_dT00'\n"
    assert repair.collect_rename_candidates(text) == ["dispatch_dT00"]


def test_candidate_capture_dedup_and_order():
    text = (
        "unknown identifier 'foo'\n"
        "unknown identifier 'bar'\n"
        "unknown identifier 'foo'\n"
    )
    assert repair.collect_rename_candidates(text) == ["foo", "bar"]


def test_candidate_capture_from_result_like_object():
    class _R:
        errors = ["R3Cert/Y.lean:10:1: unknown identifier 'ghost_lemma'"]
        raw = "...\nR3Cert/Y.lean:10:1: unknown identifier 'ghost_lemma'\n"

    assert repair.collect_rename_candidates(_R()) == ["ghost_lemma"]


def test_candidate_capture_empty_on_clean_text():
    assert repair.collect_rename_candidates("all good, no errors") == []


def test_unknown_constant_is_not_matched():
    # It is 'unknown identifier', NOT 'unknown constant'.
    assert repair.collect_rename_candidates("unknown constant 'X'") == []


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
