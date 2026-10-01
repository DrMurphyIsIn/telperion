"""Tests for the typed_cavity_induction emitter (a finite type table with per-type bounds is an
inductive invariant of a branching recursion over every finite rooted tree).

Offline: exact certificate construction and re-verification, every refusal, independent
brute-force checks of the certified claims (exact rationals): for the Balister-Bollobas-Gerke
instances, R_{-1} computed from the EDGES of every half-tree and every tree up to a size bound
(the table c_d is attained, the Theorem 6 constant is attained); for the synthetic instance,
every rooted tree up to 10 vertices plus stars and brooms far past the band (so the tail is
exercised).  Also the emitted Lean text and the frozen dogfood.  The kernel run is the dogfood
`lake build` (CI) and the lean-gated negative controls (`test_certificate_sensitivity` and
`test_negctrl_typed_cavity_induction`).

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_typed_cavity_induction import (  # noqa: E402
    BBG3_LOWERED_SPEC,
    BBG3_SPEC,
    BBG4_SPEC,
    SYNTH_SPEC,
    TypedCavityInductionEmitter,
    TypedCavityRefusal,
    bbg_c_table,
    bbg_randic_spec,
    typed_cavity_certificate,
    typed_cavity_induction_family,
    verify_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "typed_cavity_induction"
Q = Fraction


@pytest.fixture(scope="module")
def bbg3():
    return typed_cavity_certificate(**BBG3_SPEC)


@pytest.fixture(scope="module")
def bbg4():
    return typed_cavity_certificate(**BBG4_SPEC)


@pytest.fixture(scope="module")
def synth():
    return typed_cavity_certificate(**SYNTH_SPEC)


def _emit_one(spec, name="inst"):
    fam = typed_cavity_induction_family(
        "TCITest", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    rep = emit(certify(fam), LeanProfile(namespace=("TCITest",)),
               [TypedCavityInductionEmitter()],
               ValidationReport(checks=(("typed_cavity_induction", True),)))
    return next(iter(rep.files.values()))


# ---- rooted trees (canonical nested tuples) ------------------------------------------------

@lru_cache(maxsize=None)
def _trees(n: int, maxk: int) -> tuple:
    """All rooted trees with n vertices and every child count <= maxk, as sorted tuples of
    children."""
    if n == 1:
        return ((),)
    out = set()

    def rec(left, maxpart, acc):
        if left == 0:
            if len(acc) <= maxk:
                out.add(tuple(sorted(acc)))
            return
        if len(acc) >= maxk:
            return
        for s in range(min(left, maxpart), 0, -1):
            for t in _trees(s, maxk):
                rec(left - s, s, acc + [t])
    rec(n - 1, n - 1, [])
    return tuple(sorted(out))


def _size(t) -> int:
    return 1 + sum(_size(c) for c in t)


# ---- the BBG instances ---------------------------------------------------------------------

def _randic_half(t) -> Q:
    """R_{-1} of a half-tree from its EDGES: the root's degree counts the dangling edge."""
    d = len(t) + 1
    return sum((_randic_half(c) + Q(1, d * (len(c) + 1)) for c in t), Q(0))


def test_bbg_tables_are_the_published_recursion(bbg3, bbg4):
    assert [t.B for t in bbg3.types] == [sp.Rational(-7, 27), sp.Rational(-1, 54),
                                         sp.Rational(1, 27)]
    assert [t.B for t in bbg4.types] == [sp.Rational(-139, 528), sp.Rational(-7, 264),
                                         sp.Rational(3, 176), sp.Rational(5, 132)]
    # the Theorem 6 additive constants: 73/528 printed for Delta = 4; 5/27 (= 10/54 <= 11/54
    # printed) for Delta = 3
    assert bbg4.join.C == sp.Rational(73, 528)
    assert bbg3.join.C == sp.Rational(5, 27) and bbg3.join.C <= sp.Rational(11, 54)
    assert bbg3.bounded and bbg3.tail is None and bbg3.M_enum == 2
    assert bbg3.types[0].exact and all(not t.exact for t in bbg3.types[1:])
    # every message is exact: every enumeration cell is a point
    assert all(c.point for ob in bbg3.obligations() for c in ob.cells)


@pytest.mark.parametrize("Delta,beta", [(3, Q(7, 27)), (4, Q(139, 528))])
def test_bbg_beta_is_minimal(Delta, beta):
    """beta_Delta is the least beta with condition (6) for 2 <= d <= Delta: tight at d = Delta,
    and 1/1000 less is refused."""
    c = bbg_c_table(Delta, beta)
    d = Delta
    assert c[d - 1] == (d - 1) * (c[d - 1] + sp.Rational(1, d * d)) - sp.Rational(beta.numerator,
                                                                                 beta.denominator)
    with pytest.raises(TypedCavityRefusal, match="FALSE"):
        typed_cavity_certificate(**bbg_randic_spec(Delta, beta - Q(1, 1000)))


@pytest.mark.parametrize("Delta,beta", [(3, Q(7, 27)), (4, Q(139, 528))])
def test_bbg_lemma4_brute_force(Delta, beta):
    """c_T = R_{-1}(T) - beta n <= c_{d(T)} on every half-tree of max degree Delta up to 11
    vertices (exact), and each c_d is attained by BBG's half-tree [d, a_1, ..., 1] (Lemma 1)."""
    c = [Q(int(x.p), int(x.q)) for x in bbg_c_table(Delta, beta)]
    for n in range(1, 12):
        for t in _trees(n, Delta - 1):
            d = len(t) + 1
            cT = _randic_half(t) - beta * n
            assert cT <= c[d - 1], (t, cT, c[d - 1])

    def best_half(d):                      # [d, k, ...]: d - 1 copies of the best [k, ...]
        if d == 1:
            return ()
        k = max(range(1, d), key=lambda k: c[k - 1] + Q(1, k * d))
        return tuple([best_half(k)] * (d - 1))
    for d in range(1, Delta + 1):
        t = best_half(d)
        assert _randic_half(t) - beta * _size(t) == c[d - 1]


@pytest.mark.parametrize("Delta,beta,C", [(3, Q(7, 27), Q(5, 27)),
                                          (4, Q(139, 528), Q(73, 528))])
def test_bbg_theorem6_brute_force(Delta, beta, C):
    """Every tree rooted at a degree-Delta vertex with branches of max degree Delta, up to 12
    vertices: R_{-1}(T) <= beta n + C; and BBG's extremal tree attains it."""
    halves = [t for n in range(1, 11) for t in _trees(n, Delta - 1)]
    best = None

    def rec(i, acc, size):
        nonlocal best
        if len(acc) == Delta:
            R = sum(_randic_half(b) + Q(1, Delta * (len(b) + 1)) for b in acc)
            gap = beta * (size + 1) + C - R
            assert gap >= 0, (acc, gap)
            best = gap if best is None else min(best, gap)
            return
        for j in range(i, len(halves)):
            s = _size(halves[j])
            if size + s + 1 > 12:
                continue
            rec(j, acc + [halves[j]], size + s)
    rec(0, [], 0)
    assert best >= 0
    # attained (BBG, after Theorem 6): Delta copies of the best half-tree [k, ..., 1] joined to
    # one vertex, k the maximiser for c_Delta in (5)
    c = [Q(int(x.p), int(x.q)) for x in bbg_c_table(Delta, beta)]

    def best_half(d):
        if d == 1:
            return ()
        k = max(range(1, d), key=lambda k: c[k - 1] + Q(1, k * d))
        return tuple([best_half(k)] * (d - 1))
    k = max(range(1, Delta), key=lambda k: c[k - 1] + Q(1, k * Delta))
    acc = [best_half(k)] * Delta
    R = sum(_randic_half(b) + Q(1, Delta * (len(b) + 1)) for b in acc)
    assert R == beta * (sum(_size(b) for b in acc) + 1) + C


def test_bbg_join_is_tree_randic(bbg3):
    """The join value sum c_{T_i} + gJ(sum y_i) is R_{-1}(T) - beta n(T) of the joined tree."""
    beta = Q(7, 27)
    for t in _trees(7, 3):
        if len(t) != 3:
            continue
        R = sum(_randic_half(b) + Q(1, 3 * (len(b) + 1)) for b in t)
        joined = sum(_randic_half(b) - beta * _size(b) for b in t) + \
            (-beta + Q(1, 3) * sum(Q(1, len(b) + 1) for b in t))
        assert joined == R - beta * _size(t)


# ---- the synthetic instance ----------------------------------------------------------------

def _synth_eval(t, cache={}):
    """(l, y, k, R) of a rooted tree under the synthetic recursion (exact)."""
    if t in cache:
        return cache[t]
    if not t:
        out = (Q(-3, 5), Q(1), 0, Q(0))
    else:
        ch = [_synth_eval(c) for c in t]
        k = len(t)
        R = sum((c[1] for c in ch), Q(0))
        l = sum((c[0] for c in ch), Q(0)) + R / (1 + R) + Q(1, 4 * (k + 1)) - Q(3, 5)
        out = (l, 1 / (1 + R), k, R)
    cache[t] = out
    return out


def _synth_type(cert, k, R):
    from telperion.emit_typed_cavity_induction import _type_of
    return _type_of(cert.groups, k, sp.Rational(R.numerator, R.denominator))


def _check_synth(cert, t):
    l, y, k, R = _synth_eval(t)
    T = cert.types[_synth_type(cert, k, R)]
    assert l <= Q(int(T.B.p), int(T.B.q)), (t, l, T)
    assert Q(int(T.ylo.p), int(T.ylo.q)) <= y <= Q(int(T.yhi.p), int(T.yhi.q)), (t, y, T)


def test_synth_devices(synth):
    assert synth.M_enum == 2 and synth.M_tail == 4 and not synth.bounded
    assert [b.k for b in synth.band] == [3, 4]
    assert all(b.s != 0 for b in synth.band)               # genuine tangents, not constants
    tl = synth.tail
    assert tl.K0 == 5 and tl.mu <= 0
    # the tail tangent depends on m: its two-variable certificate has a u = m - 5 part
    assert any(len(c.num.parts) > 1 for c in tl.tan.cells)
    assert len(tl.bins) == 2
    # interval messages: Bernstein (non-point) cells in the enumeration
    assert any(not c.point for e in synth.enum for _j, _t, *obs in e.bins
               for ob in obs for c in ob.cells)


def test_synth_brute_force_small_trees(synth):
    for n in range(1, 11):
        for t in _trees(n, 9):
            _check_synth(synth, t)


def test_synth_brute_force_high_degree(synth):
    """Stars, double stars and brooms with up to 40 children: band and tail degrees."""
    leaf = ()
    path2 = (leaf,)
    cherry = (leaf, leaf)
    for k in range(1, 41):
        for kid in (leaf, path2, cherry, (path2,), (cherry, leaf)):
            _check_synth(synth, tuple([kid] * k))
            _check_synth(synth, (tuple([kid] * k),))
            _check_synth(synth, tuple([kid] * k + [tuple([leaf] * 7)]))


def test_every_cert_expands_back_and_is_signed(bbg3, bbg4, synth):
    for c in (bbg3, bbg4, synth):
        for ob in c.obligations():
            for cell in ob.cells:
                assert cell.ok()
                for pc in cell.certs():
                    assert pc.identity_holds() and pc.ok()


def test_verify_rejects_tampering(synth):
    e = synth.enum[3]
    j, ti, ov, olo, ohi = e.bins[0]
    bad_ob = replace(ov, params=(ov.params[0], ov.params[1] - 1))
    bad = replace(synth, enum=synth.enum[:3] + (replace(e, bins=((j, ti, bad_ob, olo, ohi),)
                                                        + e.bins[1:]),) + synth.enum[4:])
    with pytest.raises(TypedCavityRefusal):
        verify_certificate(bad)
    b = synth.band[0]
    with pytest.raises(TypedCavityRefusal, match="band"):
        verify_certificate(replace(synth, band=(replace(b, mu=b.mu - 1),) + synth.band[1:]))


# ---- refusals ------------------------------------------------------------------------------

def _types(**over):
    ts = [dict(t) for t in SYNTH_SPEC["types"]]
    for i, d in over.items():
        ts[int(i[1:])] = dict(ts[int(i[1:])], **d)
    return ts


@pytest.mark.parametrize("override,msg", [
    ({"y_leaf": 1.0}, "float"),
    ({"g": "R/(1+R) + x"}, "other than m, R"),
    ({"types": _types(t5={"deg": (3, 3)})}, "do not cover k = 4"),
    ({"types": _types(t2={"bin": ("4/5", None)})}, "not contiguous"),
    ({"types": _types(t1={"y": (1, "4/7")})}, "ylo = 1 > yhi"),
    ({"types": _types(t0={"exact": ("-7/10", 1)})}, "base fails"),
    ({"types": _types(t6={"B": "-27/10"})}, "tail parent type tail_lo"),
    ({"types": _types(t1={"B": "-7/10"})}, "FALSE"),
    ({"types": _types(t5={"B": "-3/2"})}, "band degree"),
    ({"M_enum": 7}, "M_enum"),
    ({"M_tail": 1}, "M_tail"),
    ({"tail_tangent": (0, 1)}, "mu_T"),
    ({"tail_tangent": (0, 0)}, "tangent g\\(every k >= K0"),
    ({"band_tangents": {9: (0, 0)}}, "outside the band"),
])
def test_refusals(override, msg):
    with pytest.raises(TypedCavityRefusal, match=msg):
        typed_cavity_certificate(**dict(SYNTH_SPEC, **override))


def test_tail_needs_nonnegative_messages():
    ts = _types(t7={"y": ("-1/10", "1/2")})
    with pytest.raises(TypedCavityRefusal, match="ylo >= 0"):
        typed_cavity_certificate(**dict(SYNTH_SPEC, types=ts))


def test_too_many_types_refused():
    ts = [dict(name=f"d{d}", deg=(d, d), B=0, y=(0, 1)) for d in range(8)]
    ts.append(dict(name="rest", deg=(8, None), B=0, y=(0, 1)))
    with pytest.raises(TypedCavityRefusal, match="9 types"):
        typed_cavity_certificate(**dict(SYNTH_SPEC, types=ts))


def test_lowered_beta_refused_and_forgeable():
    with pytest.raises(TypedCavityRefusal, match="FALSE at k = 2"):
        typed_cavity_certificate(**BBG3_LOWERED_SPEC)
    f = typed_cavity_certificate(**BBG3_LOWERED_SPEC, check=False)
    assert not f.checked
    bad = [c for ob in f.obligations() for c in ob.cells if not c.ok() and ob.kind == "val"]
    assert bad and all(c.point for c in bad)
    assert min(c.value for c in bad) == sp.Rational(-3, 500)


# ---- emission ------------------------------------------------------------------------------

def test_emitted_text_shape():
    text = _emit_one(BBG3_SPEC, "d3")
    for s in ("theorem typed_induction_core", "theorem step_of_counts",
              "theorem separable_bound", "theorem join_of_counts", "theorem d3 (b : PTree)",
              "theorem d3_uniform", "theorem d3_join", "theorem d3_cnt2", "theorem d3_hstep",
              "noncomputable def d3_tp", "theorem d3_base"):
        assert s in text, s
    assert "sorry" not in text and "axiom " not in text and "native_decide" not in text


def test_emitted_band_and_tail_shape():
    text = _emit_one(SYNTH_SPEC, "sy")
    for s in ("theorem sy_band3 ", "theorem sy_band4 ", "theorem sy_tail (k : ℕ)",
              "theorem sy_tail_tan", "theorem sy_tail_mu", "(hk : 5 ≤ k)",
              "rcases Nat.lt_or_ge 4 k with hK | hK"):
        assert s in text, s
    assert "sorry" not in text and "native_decide" not in text


def test_generic_section_emitted_once_for_several_instances():
    fam = typed_cavity_induction_family(
        "TCITwo", GridSpec([("case", [0, 1])]),
        lambda pt: ["one", "two"][pt["case"]],
        spec=lambda pt: [BBG3_SPEC, BBG4_SPEC][pt["case"]])
    rep = emit(certify(fam), LeanProfile(namespace=("TCITwo",)),
               [TypedCavityInductionEmitter()],
               ValidationReport(checks=(("typed_cavity_induction", True),)))
    text = next(iter(rep.files.values()))
    assert text.count("theorem typed_induction_core") == 1
    assert "theorem one (b : PTree)" in text and "theorem two (b : PTree)" in text


def test_emitter_for_kind():
    assert type(emitter_for("typed_cavity_induction")).__name__ == "TypedCavityInductionEmitter"


def test_dogfood_is_frozen():
    import subprocess
    r = subprocess.run([sys.executable, str(_EX / "generate.py"), "--check"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr


def test_randic_companion_names_exist():
    """The hand-written R_{-1} companion uses only names the generated file defines."""
    gen = (_EX / "lean" / "TypedCavityInduction.lean").read_text(encoding="utf-8")
    comp = (_EX / "lean" / "TypedCavityInductionRandic.lean").read_text(encoding="utf-8")
    for nm in ("bbg3_h", "bbg3_g", "bbg3_gJ", "bbg3_join", "bbg3_uniform",
               "bbg4_h", "bbg4_g", "bbg4_gJ", "bbg4_join", "bbg4_uniform"):
        assert nm in comp
        assert (f"def {nm} " in gen) or (f"theorem {nm} " in gen), nm
    assert "sorry" not in comp and "native_decide" not in comp
