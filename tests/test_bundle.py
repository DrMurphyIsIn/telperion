"""Bundle assembly — parse emitted theorem blocks, merge many sources into one Lean
file, dedup shared atoms, and reject name-conflicting statements.

The AXLE ``merge`` / ``merge_duplicates`` lesson made practical for the growing BG
cell family: many cells reuse the same enclosure lemma (e.g. ``log54_sub_fstar_le``),
so per-cell emitted files must assemble into ONE file with the shared atom appearing
once.  These tests are pure text (no Lean build).  An optional guarded slow test
kernel-checks a tiny merged file against the real log_combination env.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))  # for the shared lean_env guard

from telperion.bundle import parse_theorems, merge_bundle, bundle_stats  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

# --- Small hardcoded theorem strings (BG-flavoured enclosure atoms) -----------

_SHARED = (
    "-- shared enclosure atom reused by several cells\n"
    "theorem log54_sub_fstar_le : Real.log (5/4 : ℝ) - FSTAR ≤ (1/20 : ℝ) := by\n"
    "  sorry\n"
)

_CELL_A = (
    _SHARED
    + "theorem cellA_bound : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by\n"
    + "  sorry\n"
)

_CELL_B = (
    _SHARED  # same shared atom, byte-identical
    + "theorem cellB_bound : Real.log (11/9 : ℝ) - FSTAR ≤ (-1/200 : ℝ) := by\n"
    + "  sorry\n"
)

# Same NAME as the shared atom but a DIFFERENT statement -> conflict.
_CELL_CONFLICT = (
    "theorem log54_sub_fstar_le : Real.log (5/4 : ℝ) - FSTAR ≤ (1/40 : ℝ) := by\n"
    "  sorry\n"
)


def test_parse_theorems_two_theorems():
    content = (
        "theorem foo : (1:ℝ) = 1 := by norm_num\n"
        "theorem bar : Real.log (5/4 : ℝ) - FSTAR ≤ (1/20 : ℝ) := by sorry\n"
    )
    blocks = parse_theorems(content)
    assert [b["name"] for b in blocks] == ["foo", "bar"]
    assert blocks[0]["statement"] == "(1:ℝ) = 1"
    assert "Real.log (5/4" in blocks[1]["statement"]
    # the full block text is preserved
    assert blocks[0]["block"].startswith("theorem foo")


def test_parse_preserves_leading_doc_comment():
    content = (
        "-- doc line for foo\n"
        "theorem foo : (1:ℝ) = 1 := by norm_num\n"
    )
    blocks = parse_theorems(content)
    assert len(blocks) == 1
    assert blocks[0]["block"].startswith("-- doc line for foo")
    assert "theorem foo" in blocks[0]["block"]


def test_parse_ignores_structural_lines():
    content = (
        "import Mathlib\n"
        "namespace Foo\n"
        "open Real\n"
        "theorem foo : (1:ℝ) = 1 := by norm_num\n"
        "end Foo\n"
        "#print axioms foo\n"
    )
    blocks = parse_theorems(content)
    assert [b["name"] for b in blocks] == ["foo"]
    # the `end`/`#print` do not leak into the block
    assert "end Foo" not in blocks[0]["block"]
    assert "#print" not in blocks[0]["block"]


def test_merge_dedups_shared_atom():
    merged = merge_bundle([_CELL_A, _CELL_B])
    stats = bundle_stats(merged)
    # 3 distinct theorems: shared + cellA + cellB (shared appears once)
    assert stats["n_theorems"] == 3
    assert stats["n_unique"] == 3
    assert stats["n_deduped"] == 0
    assert stats["names"] == ["log54_sub_fstar_le", "cellA_bound", "cellB_bound"]
    # exactly one copy of the shared atom survives
    assert merged.count("theorem log54_sub_fstar_le") == 1
    # both unique cell theorems are present
    assert "cellA_bound" in merged and "cellB_bound" in merged


def test_merge_without_dedup_keeps_duplicates():
    merged = merge_bundle([_CELL_A, _CELL_B], dedup=False)
    assert merged.count("theorem log54_sub_fstar_le") == 2
    stats = bundle_stats(merged)
    assert stats["n_theorems"] == 4
    assert stats["n_deduped"] == 1  # one duplicate name still present


def test_name_conflict_raises():
    import pytest
    with pytest.raises(ValueError):
        merge_bundle([_CELL_A, _CELL_CONFLICT])


def test_merge_wraps_namespace_with_imports_and_prelude():
    merged = merge_bundle(
        [_CELL_A],
        imports=("import Mathlib",),
        prelude="noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11",
        namespace="Foo",
    )
    assert merged.count("import Mathlib") == 1
    assert merged.count("noncomputable def FSTAR") == 1
    assert "namespace Foo" in merged
    assert "end Foo" in merged
    # imports come before the namespace open, which comes before the theorems
    assert merged.index("import Mathlib") < merged.index("namespace Foo")
    assert merged.index("namespace Foo") < merged.index("theorem log54_sub_fstar_le")
    assert merged.index("theorem log54_sub_fstar_le") < merged.index("end Foo")


def test_bundle_stats_shape():
    stats = bundle_stats(merge_bundle([_CELL_A]))
    assert set(stats) == {"n_theorems", "n_unique", "n_deduped", "names"}
    assert stats["names"] == ["log54_sub_fstar_le", "cellA_bound"]


def test_merged_file_verifies_optional():
    """OPTIONAL slow kernel check: merge two real emitted atoms and elaborate the
    result against the built log_combination env.  Skipped (still PASS) if the env
    or lake toolchain is unavailable — the pure-text merge above is the load-bearing
    contract; this pins that the ASSEMBLED file is a real, elaborable Lean source.
    """
    import pytest

    env_dir = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"
    if not lean_env_ready(env_dir):
        pytest.skip("log_combination Mathlib env not built "
                    "(guard must not let the test trigger a from-scratch rebuild)")

    from telperion.verify import verify_lean

    # Two trivially-true real theorems sharing an identical atom.
    src = (
        "theorem bundle_shared : (1:ℝ) = 1 := by norm_num\n"
        "theorem bundle_a : (2:ℝ) = 2 := by norm_num\n"
    )
    src2 = (
        "theorem bundle_shared : (1:ℝ) = 1 := by norm_num\n"
        "theorem bundle_b : (3:ℝ) = 3 := by norm_num\n"
    )
    merged = merge_bundle([src, src2], namespace="BundleCheck")
    assert merged.count("theorem bundle_shared") == 1

    r = verify_lean(merged, env_dir=env_dir,
                    decls=["BundleCheck.bundle_shared", "BundleCheck.bundle_a",
                           "BundleCheck.bundle_b"])
    assert r.okay, r.summary()
    assert r.axioms_clean, r.summary()
