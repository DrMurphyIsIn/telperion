"""Tests for the single_crossing_ladder emitter (single crossing of consecutive members of a
parametric log-sum family, increasing breakpoints, and the best-member ladder).

Offline: exact certificate construction and re-verification, every refusal (including a wrong
breakpoint bracket and a double crossing), an independent high-precision check of the certified
claims (mpmath: the zero of each D_j lies in its bracket, and the numerical argmax over the
window agrees with the ladder on a grid), the emitted Lean text, and the frozen dogfood.  The
kernel run is the dogfood `lake build` (CI) and the lean-gated negative controls
(`test_certificate_sensitivity` and `test_negctrl_single_crossing_ladder`).

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import mpmath as mp  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_single_crossing_ladder import (  # noqa: E402
    ARM_LADDER_SPEC,
    ARM_PAIR3_SPEC,
    ARM_PAIR3_WRONG_BRACKET_SPEC,
    DOUBLE_DIP_BOUNDED_SPEC,
    DOUBLE_DIP_UNBOUNDED_SPEC,
    SingleCrossingLadderEmitter,
    SingleCrossingRefusal,
    single_crossing_ladder_certificate,
    single_crossing_ladder_family,
    verify_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "single_crossing_ladder"
mp.mp.dps = 40


@pytest.fixture(scope="module")
def cert():
    return single_crossing_ladder_certificate(**ARM_LADDER_SPEC)


def _F(c, j, x):
    return sum(mp.mpf(k.p) / k.q * mp.log(1 + mp.mpf(b.p) / b.q * x)
               for k, b in c.member_terms[j - c.a])


def _emit_one(spec, name="inst"):
    fam = single_crossing_ladder_family(
        "SCLTest", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    rep = emit(certify(fam), LeanProfile(namespace=("SCLTest",)),
               [SingleCrossingLadderEmitter()],
               ValidationReport(checks=(("single_crossing_ladder", True),)))
    return next(iter(rep.files.values()))


# ---- the certificate -----------------------------------------------------------------------

def test_arm_ladder_modes_and_numerators(cert):
    assert [p.mode for p in cert.pairs] == ["dominated"] * 2 + ["cross"] * 4
    assert cert.checked and cert.X is None
    p3 = cert.pairs[2]
    assert p3.N == (sp.Rational(1, 840), sp.Rational(-1, 210), sp.Rational(-1, 160))
    # N_j(0) > 0 for crossings, < 0 for dominated pairs
    assert all((p.N[0] > 0) == (p.mode == "cross") for p in cert.pairs)


def test_arm_member_formula_matches_the_arm_weight(cert):
    """F_j equals [j log((2+x)/2) + log((j+1 + x j/(2+x))/(j+1))]/(2j+1) numerically."""
    for j in range(1, 8):
        for x in (mp.mpf("0.1"), mp.mpf("1.3"), mp.mpf(7)):
            want = (j * mp.log((2 + x) / 2) + mp.log((j + 1 + x * j / (2 + x)) / (j + 1))) / (2 * j + 1)
            assert abs(_F(cert, j, x) - want) < mp.mpf(10) ** -30


def test_zero_of_each_crossing_lies_in_its_bracket(cert):
    for p in cert.crossings:
        D = lambda x: _F(cert, p.j, x) - _F(cert, p.j + 1, x)  # noqa: E731
        z = mp.findroot(D, (mp.mpf(p.lo.p) / p.lo.q + mp.mpf(p.hi.p) / p.hi.q) / 2)
        assert p.lo < sp.Rational(str(mp.nstr(z, 30))) < p.hi
    known = {3: "0.430501858", 4: "0.872477878", 5: "1.192396468", 6: "1.435590013"}
    for p in cert.crossings:
        assert p.lo < sp.Rational(known[p.j]) < p.hi


def test_ladder_agrees_with_numerical_argmax(cert):
    """On a grid of lambda in (0, 4], the argmax of F_1..F_7 is the ladder's member."""
    br = {p.j: p for p in cert.crossings}
    for i in range(1, 400):
        x = mp.mpf(i) / 100
        vals = {j: _F(cert, j, x) for j in range(1, 8)}
        best = max(vals, key=vals.get)
        xr = sp.Rational(i, 100)
        if any(br[j].lo <= xr <= br[j].hi for j in br):
            continue                                      # inside a bracket: undecided
        want = 3 + sum(1 for j in br if xr > br[j].hi)
        assert best == want, (i, best, want)


def test_every_polycert_expands_back_and_is_signed(cert):
    for p in cert.pairs:
        for cell in list(p.left) + list(p.right):
            assert cell.pc.identity_holds() and cell.pc.ok()
        if p.mode == "cross":
            assert p.cross_cell[2].identity_holds() and p.cross_cell[2].ok()


def test_brackets_increase_and_dominated_come_first(cert):
    cr = cert.crossings
    assert all(a.hi < b.lo for a, b in zip(cr, cr[1:]))
    assert max(p.j for p in cert.dominated) < min(p.j for p in cr)


def test_verify_certificate_rejects_tampering(cert):
    p = cert.pairs[2]
    bad = replace(p, N=(p.N[0] + 1,) + p.N[1:])
    with pytest.raises(SingleCrossingRefusal, match="does not match"):
        verify_certificate(replace(cert, pairs=cert.pairs[:2] + (bad,) + cert.pairs[3:]))
    gap = replace(p, right=(replace(p.right[0], s=p.right[0].s + sp.Rational(1, 64)),))
    with pytest.raises(SingleCrossingRefusal):
        verify_certificate(replace(cert, pairs=cert.pairs[:2] + (gap,) + cert.pairs[3:]))


def test_bounded_domain_instance():
    c = single_crossing_ladder_certificate(**DOUBLE_DIP_BOUNDED_SPEC)
    assert c.X == 2 and len(c.crossings) == 1
    assert c.pairs[0].right[-1].t == 2


# ---- refusals ------------------------------------------------------------------------------

def test_wrong_bracket_is_refused():
    with pytest.raises(SingleCrossingRefusal, match="bracket wrong"):
        single_crossing_ladder_certificate(**ARM_PAIR3_WRONG_BRACKET_SPEC)


def test_double_crossing_is_refused():
    with pytest.raises(SingleCrossingRefusal, match="2 sign changes"):
        single_crossing_ladder_certificate(**DOUBLE_DIP_UNBOUNDED_SPEC)


@pytest.mark.parametrize("override,msg", [
    ({"a": 4, "J": 3}, "a <= J"),
    ({"brackets": {3: (0.4305, 0.43051)}}, "floats"),
    ({"brackets": {3: ("43051/100000", "43050/100000")}}, "0 < lo < hi"),
    ({"brackets": {9: ("1", "2")}}, "outside the window"),
    ({"terms": [("1/(j-3)", "1")]}, "undefined at j = 3"),
    ({"terms": [("1", "-1/2")]}, "unbounded domain"),
    ({"terms": [("1", "1/2")]}, "identical"),
    ({"terms": [("(j-1)/(2*j+1)", "1/2"), ("1/(2*j+1)", "0.5")]}, "float"),
    ({"terms": [("(j-1)/(2*j+1)", "1/2"), ("y/(2*j+1)", "1")]}, "only the symbol j"),
])
def test_refusals(override, msg):
    with pytest.raises(SingleCrossingRefusal, match=msg):
        single_crossing_ladder_certificate(**dict(ARM_PAIR3_SPEC, **override))


def test_dominated_after_crossing_refused():
    spec = dict(ARM_LADDER_SPEC, a=3, J=4, brackets={3: ARM_LADDER_SPEC["brackets"][3]})
    with pytest.raises(SingleCrossingRefusal, match="N_j\\(0\\) > 0|follows a crossing"):
        single_crossing_ladder_certificate(**spec)


def test_overlapping_brackets_refused():
    b = dict(ARM_LADDER_SPEC["brackets"])
    b[4] = ("43050/100000", "87248/100000")                  # contains lambda_4, overlaps [3]
    with pytest.raises(SingleCrossingRefusal, match="not increasing"):
        single_crossing_ladder_certificate(**dict(ARM_LADDER_SPEC, brackets=b))


def test_crossing_pair_without_bracket_refused():
    with pytest.raises(SingleCrossingRefusal, match="give a bracket"):
        single_crossing_ladder_certificate(**dict(ARM_PAIR3_SPEC, brackets={}))


def test_bracket_on_dominated_pair_refused():
    spec = dict(ARM_LADDER_SPEC, a=1, J=1, brackets={1: ("1/10", "2/10")})
    with pytest.raises(SingleCrossingRefusal, match="dominated, not crossing"):
        single_crossing_ladder_certificate(**spec)


def test_bounded_domain_beta_check():
    spec = dict(DOUBLE_DIP_BOUNDED_SPEC, terms=[("j", "-1")], X="2")
    with pytest.raises(SingleCrossingRefusal, match="<= 0"):
        single_crossing_ladder_certificate(**spec)


def test_forged_certificates_are_unchecked():
    c = single_crossing_ladder_certificate(**ARM_PAIR3_WRONG_BRACKET_SPEC, check=False)
    assert not c.checked and c.pairs[0].lo == sp.Rational(43052, 100000)
    d = single_crossing_ladder_certificate(**DOUBLE_DIP_UNBOUNDED_SPEC, check=False)
    tail = d.pairs[0].right[-1].pc
    assert tail.t is None and not tail.ok()               # the false tail cell


# ---- emission ------------------------------------------------------------------------------

def test_emitted_text_shape():
    text = _emit_one(ARM_PAIR3_SPEC, "pair3")
    for s in ("theorem single_crossing_core", "theorem ladder_core", "theorem pair3 :",
              "theorem pair3_p3_cross", "theorem pair3_p3_vlo", "theorem pair3_p3_vhi",
              "theorem pair3_p3_fac", "theorem pair3_p3_sign", "theorem pair3_best_3",
              "theorem pair3_best_4", "noncomputable def pair3_F"):
        assert s in text, s
    assert "sorry" not in text and "axiom " not in text and "native_decide" not in text


def test_generic_section_emitted_once_for_several_instances():
    fam = single_crossing_ladder_family(
        "SCLTwo", GridSpec([("case", [0, 1])]),
        lambda pt: ["one", "two"][pt["case"]],
        spec=lambda pt: [ARM_PAIR3_SPEC, DOUBLE_DIP_BOUNDED_SPEC][pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("SCLTwo",)),
               [SingleCrossingLadderEmitter()],
               ValidationReport(checks=(("single_crossing_ladder", True),)))
    text = next(iter(rep.files.values()))
    assert text.count("theorem ladder_core") == 1
    assert "theorem one :" in text and "theorem two :" in text


def test_emitter_for_kind():
    assert type(emitter_for("single_crossing_ladder")).__name__ == "SingleCrossingLadderEmitter"


def test_dogfood_is_frozen():
    import subprocess
    r = subprocess.run([sys.executable, str(_EX / "generate.py"), "--check"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
