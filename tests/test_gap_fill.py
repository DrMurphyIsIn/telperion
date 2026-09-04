"""Gap-driven emitter loop — sorry -> extract goal -> route-match -> fill.

The AXLE-inspired automation of the hand-driven BG round-trip: given a
``:= by sorry`` log-enclosure lemma, recover its ``(terms, q)`` and AUTO-SELECT
the certificate route.  These tests pin that the matcher + route-picker recover
EXACTLY the routes chosen by hand for the six real BG subaction enclosures, that
the ``+FSTAR`` (negative-coefficient) and negative-``q`` cases parse, that
``fill_gap`` emits a full theorem block, and that a non-enclosure gap is refused.
Kernel verification of the fills is offline here (needs a built Lean env); the
end-to-end fill->verify against the real ``R3Cert`` was exercised at build time.
conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.gap_fill import (  # noqa: E402
    Gap, extract_gaps, fill_gap, match_log_enclosure, pick_route,
)

# The six real BG enclosure atoms and the route each was proved with BY HAND.
_BG_CASES = {
    "log74_le_4fstar":       ("Real.log (7/4 : ℝ) ≤ 4 * FSTAR",              "monotone"),
    "log54_sub_fstar_le":    ("Real.log (5/4 : ℝ) - FSTAR ≤ 1/20",          "tangent"),
    "log54_sub_fstar_le_40": ("Real.log (5/4 : ℝ) - FSTAR ≤ 1/40",          "tangent"),
    "log74_le_4fstar_broom": ("Real.log (7/4 : ℝ) - 4 * FSTAR ≤ -1/2688",   "tangent"),
    "log119_sub_fstar":      ("Real.log (11/9 : ℝ) - FSTAR ≤ -1/200",       "tangent"),
    "log79_add_fstar":       ("Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0",      "tight"),
}


def test_route_selection_matches_hand_picks():
    for name, (stmt, want) in _BG_CASES.items():
        spec = match_log_enclosure(stmt)
        assert spec is not None, f"{name}: should match as a log-enclosure"
        got = pick_route(spec)
        assert got == want, f"{name}: route {got!r} != hand-picked {want!r}"


def test_terms_encoding():
    # `log(7/9) + FSTAR + 1/24 <= 0`  ->  +FSTAR (fneg=+1, i.e. k=-1), q = -1/24.
    spec = match_log_enclosure("Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0")
    assert spec.terms == [(1, "7/9"), (1, "621/64")]
    assert spec.q == "-1/24"
    # `log(5/4) - FSTAR <= 1/20`  ->  -FSTAR (fneg=-1), q = 1/20.
    spec2 = match_log_enclosure("Real.log (5/4 : ℝ) - FSTAR ≤ 1/20")
    assert spec2.terms == [(1, "5/4"), (-1, "621/64")]
    assert spec2.q == "1/20"


def test_extract_gaps_finds_sorry_lemmas():
    content = (
        "theorem foo : Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0 := by sorry\n"
        "theorem bar : (1:ℝ) = 1 := by norm_num\n"
        "lemma baz : Real.log (5/4 : ℝ) - FSTAR ≤ 1/20 := by sorry\n"
    )
    gaps = extract_gaps(content)
    names = {g.name for g in gaps}
    assert names == {"foo", "baz"}, names


def test_fill_emits_full_theorem_block():
    res = fill_gap(Gap("log79_add_fstar",
                       "Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0"))
    assert res.matcher == "log_enclosure" and res.route == "tight"
    assert res.verified is None  # no env_dir -> fill-only
    proof = res.proof
    assert proof.startswith("theorem log79_add_fstar")
    # a truncation bug once cut the block at the first inner `linarith`; the tight
    # route's proof has several `have`s AFTER it, so guard the tail is present.
    assert "Real.exp_bound'" in proof and proof.rstrip().endswith("linarith")
    assert "sorry" not in proof


def test_non_enclosure_gap_is_refused():
    spec = match_log_enclosure("(1:ℝ) + 1 = 2")
    assert spec is None
    try:
        fill_gap(Gap("nope", "(1:ℝ) + 1 = 2"))
        assert False, "should have refused a non-enclosure gap"
    except ValueError:
        pass


def test_repair_lean_mathlib_renames():
    from telperion.repair import repair_lean
    src = "rw [div_le_iff hx]; exact le_div_iff hy"
    fixed, applied = repair_lean(src)
    assert "div_le_iff₀" in fixed and "le_div_iff₀" in fixed
    assert len(applied) == 2
    # idempotent: an already-renamed lemma is not double-renamed.
    again, applied2 = repair_lean(fixed)
    assert again == fixed and applied2 == []


def test_registry_is_extensible():
    from telperion.gap_fill import register_matcher, _MATCHERS
    before = len(_MATCHERS)
    register_matcher("dummy", lambda s: None, lambda g, spec: ("", ""))
    assert len(_MATCHERS) == before + 1
    # a None-returning recognizer is skipped; the log_enclosure matcher still wins.
    res = fill_gap(Gap("log74_le_4fstar", "Real.log (7/4 : ℝ) ≤ 4 * FSTAR"))
    assert res.matcher == "log_enclosure"
    _MATCHERS.pop()  # cleanup
