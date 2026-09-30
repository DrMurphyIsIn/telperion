"""Tests for the concave_pooled_induction emitter (tree-recursion bounds by a concave witness
checked at the pooled mean).

Offline: exact certificate construction and re-verification, every refusal, an independent
brute-force check of the certified claim on random trees (exact rationals, including nodes far
beyond the explicit child counts, so the tail is exercised), the emitted Lean text, and the
frozen dogfood.  The kernel run is the dogfood `lake build` (CI) and the lean-gated negative
control in `test_certificate_sensitivity`.

Method credit: concave-witness induction, from a draft communicated by Professor John L.
Goldwasser (author: his London colleague; name to be added).  conjecture1_proved = False.
"""
import random
import sys
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_concave_pooled_induction import (  # noqa: E402
    MATCHING_DENSITY_SPEC,
    PATH_DENSITY_SPEC,
    ConcavePooledInductionEmitter,
    concave_pooled_certificate,
    concave_pooled_induction_family,
    verify_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "concave_pooled_induction"


@pytest.fixture(scope="module")
def cert():
    return concave_pooled_certificate(**MATCHING_DENSITY_SPEC)


def _emit_one(spec, name="inst"):
    fam = concave_pooled_induction_family(
        "CPITest", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    rep = emit(certify(fam), LeanProfile(namespace=("CPITest",)),
               [ConcavePooledInductionEmitter()],
               ValidationReport(checks=(("concave_pooled_induction", True),)))
    return next(iter(rep.files.values()))


# ---- the certificate -----------------------------------------------------------------------

def test_dogfood_certifies_with_pieces_and_tail(cert):
    assert cert.a == (sp.Rational(-1, 4), sp.Rational(-7, 20))
    assert cert.b == (0, sp.Rational(1, 20))
    assert cert.tail and cert.M == 2 and cert.checked
    ms = {c.m for c in cert.cells}
    assert ms == {1, 2, None}
    tail = [c for c in cert.cells if c.m is None]
    assert tail[-1].t is None                     # the unbounded cell
    assert all(cert.b[c.j] <= 0 for c in tail)    # tail uses only b_j <= 0 pieces


def test_every_polycert_expands_back_and_is_nonnegative(cert):
    n = 0
    for c in cert.cells:
        for pc in list(c.dens) + ([c.dtot] if c.dtot else []) + [o.num for o in c.obligations]:
            assert pc.identity_holds() and pc.ok()
            n += 1
        # every piece of U(h) is targeted, plus the two closure sides
        assert sorted(o.k for o in c.obligations if o.side == "piece") == list(range(cert.K))
        assert {o.side for o in c.obligations} == {"piece", "lo", "hi"}
    assert n > 30


def test_cells_cover_each_domain_exactly(cert):
    for m in (1, 2):
        cs = [c for c in cert.cells if c.m == m]
        assert cs[0].s == m * cert.lo and cs[-1].t == m * cert.hi
        assert all(x.t == y.s for x, y in zip(cs, cs[1:]))
    cs = [c for c in cert.cells if c.m is None]
    assert cs[0].s == 3 * cert.lo and all(x.t == y.s for x, y in zip(cs, cs[1:]))


def test_verify_certificate_rejects_tampering(cert):
    verify_certificate(cert)  # honest: passes
    # a gap in the m = 1 cover
    cells = [c for c in cert.cells if not (c.m == 1 and c.s == 0)]
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(replace(cert, cells=tuple(cells)))
    # a cell whose stored obligation no longer matches its exact recomputation
    c0 = cert.cells[0]
    ob = c0.obligations[0]
    bad = replace(ob, num=replace(ob.num, coeffs=tuple(x + 1 for x in ob.num.coeffs)))
    c0b = replace(c0, obligations=(bad,) + c0.obligations[1:])
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(replace(cert, cells=(c0b,) + cert.cells[1:]))
    # a larger deficit than the cells were computed for
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(replace(cert, alpha=sp.Rational(31, 50)))


def test_bounded_degree_mode(cert):
    p = concave_pooled_certificate(**PATH_DENSITY_SPEC)
    assert not p.tail and {c.m for c in p.cells} == {1}


# ---- refusals ------------------------------------------------------------------------------

@pytest.mark.parametrize("override, msg", [
    (dict(alpha=sp.Rational(13, 20)), "obligation FALSE"),
    (dict(nodes=[(0, 0), (sp.Rational(1, 2), sp.Rational(-1, 8)), (1, sp.Rational(-1, 8))]),
     "not concave"),                                   # slopes -1/4 then 0: convex kink
    (dict(nodes=[(0, 0), (sp.Rational(1, 2), sp.Rational(-1, 8)), (1, sp.Rational(-1, 4))]),
     "not concave"),                                   # equal slopes: redundant node
    (dict(nodes=[(0, 0), (1, 0.5)]), "float"),
    (dict(alpha=0.6), "float"),
    (dict(y_leaf=2), "outside"),
    (dict(l_leaf=0), "base fails"),
    (dict(M=0), "M = 0"),
    (dict(h="m/(m+R)"), "independent of m"),
])
def test_refusals(override, msg):
    with pytest.raises(ValueError, match="REFUSED") as ei:
        concave_pooled_certificate(**dict(MATCHING_DENSITY_SPEC, **override))
    assert msg in str(ei.value)


def test_single_node_refused():
    with pytest.raises(ValueError, match="at least two nodes"):
        concave_pooled_certificate(**dict(MATCHING_DENSITY_SPEC, nodes=[(0, 0)]))


def test_tail_needs_a_piece_with_nonpositive_intercept():
    # one piece with intercept b = 1/10 > 0: the tail bound m b <= (M+1) b fails
    spec = dict(MATCHING_DENSITY_SPEC, nodes=[(0, sp.Rational(1, 10)), (1, sp.Rational(-3, 10))])
    with pytest.raises(ValueError, match="no piece has intercept"):
        concave_pooled_certificate(**spec)


def test_tail_needs_nonnegative_interval():
    spec = dict(MATCHING_DENSITY_SPEC,
                nodes=[(-1, 0), (sp.Rational(1, 2), sp.Rational(-1, 8)), (1, sp.Rational(-3, 10))],
                y_leaf=1)
    with pytest.raises(ValueError, match="lo >= 0"):
        concave_pooled_certificate(**spec)


def test_foreign_symbol_refused():
    with pytest.raises(ValueError, match="other than m, R"):
        concave_pooled_certificate(**dict(MATCHING_DENSITY_SPEC, g="-1/(1+R+x)"))


# ---- the claim, checked independently on random trees --------------------------------------

def _tree(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return []
    k = rng.choice([1, 1, 1, 2, 2, 3, 5, 9]) if depth > 1 else rng.randint(1, 12)
    return [_tree(rng, depth - 1) for _ in range(k)]


def _eval(t, h, g, y0, l0):
    """(msg, ell, size) of a children-list tree, exact."""
    if not t:
        return y0, l0, 1
    ys, ls, ss = zip(*(_eval(c, h, g, y0, l0) for c in t))
    R, m = sum(ys), len(t)
    return h(m, R), sum(ls) + g(m, R), sum(ss) + 1


def _U(c, x):
    return min(Fraction(int(a.p), int(a.q)) * x + Fraction(int(b.p), int(b.q))
               for a, b in zip(c.a, c.b))


def test_claim_holds_on_random_trees(cert):
    rng = random.Random(20260929)
    h = lambda m, R: 1 / (1 + R)                       # noqa: E731
    g = lambda m, R: -1 / (1 + R)                      # noqa: E731
    alpha = Fraction(3, 5)
    big = 0
    for _ in range(300):
        t = _tree(rng, 6)
        y, ell, n = _eval(t, h, g, Fraction(1), Fraction(-1))
        assert 0 <= y <= 1
        assert ell + alpha * n <= _U(cert, y) <= 0          # i.e. sum_u y_u >= (3/5) n
        big += len(t) > 2                                   # root in the tail regime
    assert big > 10
    # the path: density -> 1/phi, so the sharp constant is below 13/20
    path = []
    for _ in range(199):
        path = [path]
    y, ell, n = _eval(path, h, g, Fraction(1), Fraction(-1))
    assert n == 200 and -ell / n < Fraction(62, 100) and ell + Fraction(13, 20) * n > 0


# ---- the emitted Lean ----------------------------------------------------------------------

def test_emitted_text_shape():
    txt = _emit_one(PATH_DENSITY_SPEC, "pd")
    for s in ("theorem pooled_induction_core", "theorem minPieces_jensen",
              "theorem pd (b : PTree) (hb : b.AllDeg (fun m => m ≤ 1))",
              "theorem pd_uniform", "theorem pd_hstep", "theorem pd_node2",
              "Professor John L. Goldwasser"):
        assert s in txt, s
    for bad in ("sorry", "native_decide", "admit", "axiom "):
        assert bad not in txt
    assert txt.count("inductive PTree") == 1


def test_generic_section_emitted_once_for_several_instances():
    fam = concave_pooled_induction_family(
        "CPITwo", GridSpec([("case", [0, 1])]), lambda pt: ["a1", "a2"][pt["case"]],
        spec=lambda pt: [MATCHING_DENSITY_SPEC, PATH_DENSITY_SPEC][pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("CPITwo",)),
               [ConcavePooledInductionEmitter()],
               ValidationReport(checks=(("concave_pooled_induction", True),)))
    txt = next(iter(rep.files.values()))
    assert txt.count("theorem pooled_induction_core") == 1
    assert "theorem a1 (b : PTree) :" in txt and "theorem a2 (b : PTree) (hb" in txt


def test_emitter_for_kind():
    assert isinstance(emitter_for("concave_pooled_induction"), ConcavePooledInductionEmitter)


def test_dogfood_is_frozen():
    sys.path.insert(0, str(_EX))
    import generate  # noqa: E402
    assert generate.main(check=True) == 0
    txt = (_EX / "lean" / "ConcavePooledInduction.lean").read_text(encoding="utf-8")
    assert "theorem matching_density_uniform (b : PTree) :" in txt
    assert "theorem synthetic_mdep (b : PTree) (hb : b.AllDeg (fun m => m ≤ 2))" in txt


def test_rendering_edge_cases_regression():
    """Four rendering bugs fixed 2026-09-30 (all rejected by the kernel before, never unsound):
    unused binders, `fin_cases ... <;>` on a single piece, a constant denominator dropped from
    the closed form, and `linarith` after a `rw` that already closed an identically-zero goal."""
    spec = dict(nodes=[(0, 0), (1, 0)], h="1/(1+m)", g="-1", y_leaf=1, l_leaf=-1,
                alpha=1, M=3, tail=False)
    txt = _emit_one(spec, name="edge")
    assert "noncomputable def edge_h : ℕ → ℝ → ℝ := fun m _ =>" in txt
    assert "noncomputable def edge_g : ℕ → ℝ → ℝ := fun _ _ =>" in txt
    assert "fin_cases k <;>" not in txt and "fin_cases k ; norm_num" in txt
    # m = 1: h = 1/(1+1) must render as 1/2, not as the bare numerator 1
    assert "edge_h 1 R = (((1 / 2 : ℝ)))" in txt
    assert "rw [eh, eg] <;> linarith" in txt or "rw [eh, eg]\n" in txt
