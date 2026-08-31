"""emit_preconnected_cover: preconnectedness-by-convex-cover emitter.

The punctured half-plane `{b < Re s} \\ {(c,0)}` (b < c) is preconnected via four
convex pieces glued at shared points.  The load-bearing certificate is COVER
COMPLETENESS, re-verified by EXACT sign-cell enumeration -- the generator is
untrusted, so a cover that misses a cell or a non-interior puncture is REFUSED
(anti-phantom).  Emitted Lean mirrors the kernel-checked StripReprR3.lean.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_preconnected_cover import (  # noqa: E402
    PuncturedHalfPlaneCover, verify_cover_complete, verify_gluing_points,
    emit_preconnected_lean, _cell_target, _cell_pieces)


def test_r3_instance_cover_reverifies():
    # The CI-green instance: {0 < re} \ {1}.
    r3 = PuncturedHalfPlaneCover(sp.Integer(0), sp.Integer(1))
    assert verify_cover_complete(r3)
    assert verify_gluing_points(r3)


def test_shifted_instance_reverifies():
    # A different interior puncture stays a valid cover.
    inst = PuncturedHalfPlaneCover(sp.Rational(-1, 2), sp.Integer(3))
    assert verify_cover_complete(inst)
    assert verify_gluing_points(inst)


def test_non_interior_puncture_is_refused():
    # anti-phantom: c <= b means the "puncture" is on/left of the boundary; the
    # four-piece cover does NOT equal the target, so it must be refused.
    for b, c in [(sp.Integer(2), sp.Integer(1)), (sp.Integer(1), sp.Integer(1))]:
        bad = PuncturedHalfPlaneCover(b, c)
        assert not verify_cover_complete(bad)


def test_emission_refuses_forged_cover():
    bad = PuncturedHalfPlaneCover(sp.Integer(2), sp.Integer(1))
    try:
        emit_preconnected_lean(bad, "forged")
        raise AssertionError("emission must refuse a non-interior puncture")
    except ValueError:
        pass


def test_the_puncture_cell_is_excluded_by_both_sides():
    # The removed point (c,0) is cell (s1=+, s2=0, s3=0): NOT in target, NOT in
    # the union.  If either side kept it, the cover check would (correctly) fail.
    assert _cell_target(1, 0, 0) is False
    assert _cell_pieces(1, 0, 0) is False


def test_emitted_lean_has_the_verified_constructs():
    r3 = PuncturedHalfPlaneCover(sp.Integer(0), sp.Integer(1))
    lean = emit_preconnected_lean(r3, "isPreconnected_stripDomain")
    for needle in ("theorem isPreconnected_stripDomain : IsPreconnected stripDomain",
                   "convex_halfSpace_re_gt", "convex_halfSpace_im_lt",
                   "IsPreconnected.union", "rw [heq]; exact preABCD"):
        assert needle in lean, needle
