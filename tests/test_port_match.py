"""Port-match gate -- the CROSS-TOOLCHAIN half of the trust boundary.

`statement_match` checks a declaration against its intended type by ELABORATION, so both
sides must live in one Lean environment.  When a lemma proved on a v4.32 island is needed
on a v4.33 island, they cannot: the composition is done by re-proving the lemma verbatim,
and the only checkable guarantee that the re-proof says the same thing is at the text
level.  These tests pin `port_match_check`:

  * an exact port (different proof, same statement) passes -- the PROOF is allowed to
    differ, because tactic spellings differ across Mathlib versions;
  * a weakened hypothesis / changed binder in the ported STATEMENT is caught;
  * a `def` whose BODY drifted is caught (for a definition the body is the content);
  * a declaration missing on either side is reported, not silently passed;
  * a theorem ported as a def (or vice versa) is drift, not a wrong-mode comparison;
  * comments and whitespace are not drift;
  * `port_match_pinned` checks the pin against a live source file too, so the pin
    cannot rot.

No Lean environment needed: this gate is deliberately text-level (see the module
docstring for its scope).  conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.port_match import (  # noqa: E402
    PortMatchResult, decl_kind, normalize, port_match_check, port_match_pinned,
    statement_text,
)

# --- a miniature "v4.32 island" and its verbatim port to a "v4.33 island" -------------

SOURCE = """
/- BoundaryLemmas-like source island (v4.32). -/
namespace Quasicrystal

/-- Uniform discreteness. -/
def IsUniformlyDiscrete (S : Set R) : Prop :=
  exists d : R, 0 < d /\\ forall x in S, forall y in S, x != y -> d <= |x - y|

theorem not_uniformlyDiscrete_of_gaps_to_zero {S : Set R}
    (hgap : forall d : R, 0 < d -> exists x in S, exists y in S, x != y /\\ |x - y| < d) :
    Not (IsUniformlyDiscrete S) := by
  rintro ⟨d, hd, hsep⟩
  exact absurd (hsep) (by simp)

end Quasicrystal
"""

# same statements, DIFFERENT proof and comments: a legitimate verbatim port
TARGET_OK = """
/- ported to the v4.33 island; namespace and tactics differ. -/
namespace RvMBridge

-- ===== PORT of BoundaryLemmas.lean:42-43 (verbatim) =====
def IsUniformlyDiscrete (S : Set R) : Prop :=
  exists d : R, 0 < d /\\ forall x in S, forall y in S, x != y -> d <= |x - y|

-- ===== PORT of BoundaryLemmas.lean:170-175 (verbatim) =====
theorem not_uniformlyDiscrete_of_gaps_to_zero {S : Set R}
    (hgap : forall d : R, 0 < d -> exists x in S, exists y in S, x != y /\\ |x - y| < d) :
    Not (IsUniformlyDiscrete S) := by
  intro h
  obtain ⟨d, hd, hsep⟩ := h
  simp_all

end RvMBridge
"""

DECLS = ["IsUniformlyDiscrete", "not_uniformlyDiscrete_of_gaps_to_zero"]


def test_exact_port_passes_despite_different_proof_and_comments():
    res = port_match_check(SOURCE, TARGET_OK, DECLS)
    assert res.all_match, res.failure_lines()
    assert sorted(res.matched) == sorted(DECLS)
    assert not res.drifted and not res.missing
    assert res.summary().startswith("[OK] 2/2")


def test_weakened_theorem_statement_is_caught():
    # the ported theorem asks for `0 < d` to hold for ALL d -- a different statement
    bad = TARGET_OK.replace("forall d : R, 0 < d ->", "forall d : R, 0 <= d ->")
    res = port_match_check(SOURCE, bad, DECLS)
    assert not res.all_match
    assert "not_uniformlyDiscrete_of_gaps_to_zero" in res.drifted
    assert "IsUniformlyDiscrete" in res.matched
    want, have = res.drifted["not_uniformlyDiscrete_of_gaps_to_zero"]
    assert "0 < d ->" in want and "0 <= d ->" in have
    assert any("drifted" in line for line in res.failure_lines())


def test_drifted_def_body_is_caught():
    # a definition's BODY is its content: `0 < d` weakened to `0 <= d` redefines the term
    bad = TARGET_OK.replace("exists d : R, 0 < d", "exists d : R, 0 <= d")
    res = port_match_check(SOURCE, bad, DECLS)
    assert not res.all_match
    assert "IsUniformlyDiscrete" in res.drifted


def test_proof_body_change_alone_is_not_drift():
    # only the tactic block differs -- exactly what a cross-version port must be allowed
    other = TARGET_OK.replace("  intro h\n  obtain ⟨d, hd, hsep⟩ := h\n  simp_all",
                              "  aesop")
    assert port_match_check(SOURCE, other, DECLS).all_match


def test_missing_declaration_is_reported_on_each_side():
    res = port_match_check(SOURCE, TARGET_OK, DECLS + ["never_ported"])
    assert not res.all_match
    assert res.missing["never_ported"] == "source island"

    dropped = "\n".join(l for l in TARGET_OK.splitlines()
                        if "def IsUniformlyDiscrete" not in l)
    res2 = port_match_check(SOURCE, dropped, ["IsUniformlyDiscrete"])
    assert not res2.all_match
    assert res2.missing["IsUniformlyDiscrete"] == "target island"
    assert "not found" in res2.failure_lines()[0]


def test_kind_change_is_drift_not_a_wrong_mode_comparison():
    swapped = TARGET_OK.replace("def IsUniformlyDiscrete", "theorem IsUniformlyDiscrete")
    res = port_match_check(SOURCE, swapped, ["IsUniformlyDiscrete"])
    assert not res.all_match
    want, have = res.drifted["IsUniformlyDiscrete"]
    assert want.startswith("[def]") and have.startswith("[theorem]")


def test_comments_and_whitespace_are_not_drift():
    noisy = TARGET_OK.replace("def IsUniformlyDiscrete (S : Set R) : Prop :=",
                              "def IsUniformlyDiscrete   (S : Set R)\n    : Prop := /- noise -/")
    assert port_match_check(SOURCE, noisy, ["IsUniformlyDiscrete"]).all_match


def test_several_source_files_are_searched_in_order():
    # a ported block may be split: the def lives in one module, the theorem in another
    part1 = "namespace A\ndef IsUniformlyDiscrete (S : Set R) : Prop :=\n" \
            "  exists d : R, 0 < d /\\ forall x in S, forall y in S, x != y -> d <= |x - y|\nend A\n"
    part2 = "\n".join(l for l in TARGET_OK.splitlines() if "IsUniformlyDiscrete (S" not in l)
    res = port_match_check(SOURCE, [(part1, "part1"), (part2, "part2")], DECLS)
    assert res.all_match, res.failure_lines()


def test_pinned_check_catches_a_rotten_pin():
    # the pin quotes the source; when the live source island IS in the checkout, the pin
    # itself must still match it
    pin = SOURCE
    first, second = port_match_pinned(pin, TARGET_OK, DECLS, live=SOURCE)
    assert first.all_match and second.all_match

    stale_pin = SOURCE.replace("0 < d /\\", "0 <= d /\\")
    first2, second2 = port_match_pinned(stale_pin, TARGET_OK, DECLS, live=SOURCE)
    assert not first2.all_match          # the port no longer matches the (stale) pin
    assert not second2.all_match         # and the pin no longer matches the live island
    assert "IsUniformlyDiscrete" in second2.drifted

    first3, none3 = port_match_pinned(pin, TARGET_OK, DECLS)
    assert first3.all_match and none3 is None


def test_helpers():
    assert decl_kind(SOURCE, "IsUniformlyDiscrete") == "def"
    assert decl_kind(SOURCE, "not_uniformlyDiscrete_of_gaps_to_zero") == "theorem"
    assert decl_kind(SOURCE, "absent") is None
    assert statement_text(SOURCE, "absent") is None
    # a theorem statement stops before the proof
    stmt = statement_text(SOURCE, "not_uniformlyDiscrete_of_gaps_to_zero")
    assert stmt.startswith("theorem not_uniformlyDiscrete_of_gaps_to_zero")
    assert "rintro" not in stmt and "by" not in stmt.split()
    assert normalize("/- c -/ a  b -- x\n c") == "a b c"


def test_result_dataclass_summary_shapes():
    res = PortMatchResult(all_match=False, matched=["a"], drifted={"b": ("x", "y")},
                          missing={"c": "target island"})
    s = res.summary()
    assert s.startswith("[DRIFT] 1/3") and "drifted" in s and "missing" in s
