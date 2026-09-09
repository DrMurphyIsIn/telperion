"""Tests for the ReflectionHalving emitter (kind ``reflection_halving``).

The finite instance of the reflection/functional-equation halving bound
N ≤ 2·N_large (RvM/Halving ``N_le_two_mul_half``): a reflection involution
pairs the small (``Re<1/2``) part into the large (``Re≥1/2``) part, giving
``small ≤ large`` and hence ``total ≤ 2·large``, discharged by kernel decide.

Global dispatch is NOT wired yet, so the emitter is exercised DIRECTLY: build
instances via ``certify_reflection_halving_point`` and a ``CertifiedFamily``
via the construction guard, then call ``ReflectionHalvingEmitter().emit_body``.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import CertifiedFamily, _construction_guard  # noqa: E402
from telperion.emit_reflection_halving import (  # noqa: E402
    ReflectionHalvingCert,
    ReflectionHalvingEmitter,
    certify_reflection_halving_point,
    reflection_halving_certificate,
    reflection_halving_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _build_certified_family(items):
    """certify_*_point + guarded CertifiedFamily, bypassing global dispatch."""
    fam = reflection_halving_family(
        "RH", GridSpec([("_", [0])]), lambda pt: "reflect_half_demo",
        spec=lambda pt: items)
    pt = next(iter(fam.grid.points()))
    inst, n_checks = certify_reflection_halving_point(fam, pt, fam.lean_name(pt))
    _construction_guard.open = True
    try:
        cf = CertifiedFamily(family=fam, instances=(inst,), checks_passed=n_checks)
    finally:
        _construction_guard.open = False
    return cf, n_checks


# --------------------------------------------------------------------------- #
# builder — accepts valid data, refuses each bad case                         #
# --------------------------------------------------------------------------- #


def test_builder_accepts_valid_small_le_large():
    # small = 2 (the untagged item), large = 3 + 1 = 4; 2 ≤ 4 so total 6 ≤ 8.
    cert = reflection_halving_certificate([(3, True), (2, False), (1, True)])
    assert isinstance(cert, ReflectionHalvingCert)
    assert cert.small == 2 and cert.large == 4 and cert.total == 6
    assert cert.total <= 2 * cert.large


def test_builder_accepts_equality_case():
    # small == large is the tight involution (perfect pairing): total = 2·large.
    cert = reflection_halving_certificate([(5, True), (5, False)])
    assert cert.small == 5 and cert.large == 5
    assert cert.total == 2 * cert.large


def test_builder_refuses_empty():
    with pytest.raises(ValueError):
        reflection_halving_certificate([])


def test_builder_refuses_nonpositive_weight():
    with pytest.raises(ValueError):
        reflection_halving_certificate([(3, True), (0, False)])
    with pytest.raises(ValueError):
        reflection_halving_certificate([(-1, True), (2, False)])


def test_builder_refuses_small_exceeds_large():
    # small = 5 > large = 3 — the pairing involution witness is missing.
    with pytest.raises(ValueError):
        reflection_halving_certificate([(3, True), (5, False)])
    # all-small (large-part empty) is the extreme refusal.
    with pytest.raises(ValueError):
        reflection_halving_certificate([(1, False), (1, False)])


# --------------------------------------------------------------------------- #
# certify point — checks and payload                                          #
# --------------------------------------------------------------------------- #


def test_certify_point_returns_two_checks():
    fam = reflection_halving_family(
        "RH", GridSpec([("_", [0])]), lambda pt: "thm_rh",
        spec=lambda pt: [(4, True), (2, False)])
    pt = next(iter(fam.grid.points()))
    inst, n = certify_reflection_halving_point(fam, pt, "thm_rh")
    assert n == 2
    assert inst.lean_name == "thm_rh"
    assert isinstance(inst.payload, ReflectionHalvingCert)


# --------------------------------------------------------------------------- #
# emit — theorem text, 2*, decide tactic, lint clean, deterministic           #
# --------------------------------------------------------------------------- #


def test_emit_body_shape_and_lint_clean():
    cf, _ = _build_certified_family([(3, True), (2, False), (1, True)])
    text, n_thm = ReflectionHalvingEmitter().emit_body(cf, LeanProfile(namespace=("RH",)))
    assert n_thm == 1
    assert "theorem reflect_half_demo" in text
    assert "2 *" in text                    # the halving bound's doubled RHS
    assert "decide" in text                 # discharge tactic
    assert ": ℤ)" in text                    # integer literal sums
    # non-vacuous: the large-part sum uses the two tagged weights 3 and 1.
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic: same bytes on re-emit.
    text2, _ = ReflectionHalvingEmitter().emit_body(cf, LeanProfile(namespace=("RH",)))
    assert text2 == text


def test_emit_body_totals_match_certificate():
    cf, _ = _build_certified_family([(5, True), (5, False)])
    text, _ = ReflectionHalvingEmitter().emit_body(cf, LeanProfile(namespace=("RH",)))
    # grand total 10 ≤ 2 * (large 5) ; the RHS large sum is the single tagged 5.
    assert "grand total = 10" in text
    assert "2 * (5)" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_kind():
    assert ReflectionHalvingEmitter().kind == "reflection_halving"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
