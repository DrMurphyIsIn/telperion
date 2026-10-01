"""Tests for the anchored_monotone_extension emitter (a parametric tree recursion, its
log-derivative recursion, a two-row inductive invariant, the antitone normalized ratio and the
anchored extension).

Offline: an independent numerical check of every dogfood claim over ALL rooted trees with at most
7 vertices (the recursion, the derivative recursion against a finite difference, both invariant
rows, the antitone ratio, the anchored bound, and the falsity of the too-small normalizer), the
exact certificate construction and re-verification, every refusal, the emitted Lean text and the
frozen dogfood.  Lean-gated: the cell-split tactic generator compiles (subdivided obligations do
not occur in the dogfood).  The kernel run of the dogfood is its `lake build` (CI) and the
negative control (`test_negctrl_anchored_monotone_extension`).

conjecture1_proved = False.
"""
import itertools
import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import mpmath as mp  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_anchored_monotone_extension import (  # noqa: E402
    A_SYM,
    HARDCORE_CUBE_SPEC,
    HARDCORE_SPEC,
    HARDCORE_TOO_SMALL_SPEC,
    MATCHING_SPEC,
    X_SYM,
    AnchoredMonotoneExtensionEmitter,
    AnchoredMonotoneRefusal,
    _mcert,
    _tree_tactic,
    anchored_monotone_extension_certificate,
    anchored_monotone_extension_family,
    cell_identity_holds,
    verify_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "anchored_monotone_extension"
mp.mp.dps = 30


def _spec(spec, **kw):
    s = dict(spec, **kw)
    s.pop("sanity", None)
    return s


@pytest.fixture(scope="module")
def hc():
    return anchored_monotone_extension_certificate(**_spec(HARDCORE_SPEC))


@pytest.fixture(scope="module")
def mt():
    return anchored_monotone_extension_certificate(**_spec(MATCHING_SPEC))


# ---- an independent numerical model of the recursion ----------------------------------------

def _trees(n):
    """All rooted unlabeled trees with n vertices, as nested sorted tuples of children."""
    if n == 1:
        return [()]
    out = set()

    def parts(m, mx):
        if m == 0:
            yield []
            return
        for p in range(min(m, mx), 0, -1):
            for rest in parts(m - p, p):
                yield [p] + rest
    for P in parts(n - 1, n - 1):
        for combo in itertools.product(*[_trees(p) for p in P]):
            out.add(tuple(sorted(combo)))
    return sorted(out)


_ALL = [(n, t) for n in range(1, 8) for t in _trees(n)]


def _model(prod):
    """Return f(tree, x) -> (T, y, D, E): the recursion and the derivative recursion exactly as
    the Lean definitions state them, for g = 1 + x A, h = 1/(1 + x A)."""
    def f(t, x):
        ch = [f(c, x) for c in t]
        if prod:
            A = mp.fprod([c[1] for c in ch]) if ch else mp.mpf(1)
            Ad = A * mp.fsum([c[3] for c in ch])
        else:
            A = mp.fsum([c[1] for c in ch])
            Ad = mp.fsum([c[1] * c[3] for c in ch])
        g = 1 + x * A
        T = mp.fprod([c[0] for c in ch]) * g
        y = 1 / g
        D = mp.fsum([c[2] for c in ch]) + (A + x * Ad) / g
        E = -(A + x * Ad) / g
        return T, y, D, E
    return f


def test_tree_enumeration_counts():
    assert [len(_trees(n)) for n in range(1, 8)] == [1, 1, 2, 4, 9, 20, 48]


def test_hardcore_model_counts_independent_sets():
    """At x = 1, Z_b counts the independent sets of the tree (brute force on the tree)."""
    f = _model(True)

    def edges(t, base=0):
        es, nxt = [], base + 1
        for c in t:
            es.append((base, nxt))
            sub, nxt2 = edges(c, nxt)
            es += sub
            nxt = nxt2
        return es, nxt
    for n, t in _ALL:
        es, m = edges(t)
        assert m == n
        cnt = sum(1 for S in itertools.product([0, 1], repeat=n)
                  if all(not (S[u] and S[v]) for u, v in es))
        assert abs(f(t, mp.mpf(1))[0] - cnt) < mp.mpf(10) ** -20


def test_matching_model_counts_matchings():
    """At x = 1, the sum recursion counts the matchings of the tree."""
    f = _model(False)

    def edges(t, base=0):
        es, nxt = [], base + 1
        for c in t:
            es.append((base, nxt))
            sub, nxt2 = edges(c, nxt)
            es += sub
            nxt = nxt2
        return es, nxt
    for n, t in _ALL:
        es, _ = edges(t)
        cnt = 0
        for k in range(len(es) + 1):
            for M in itertools.combinations(es, k):
                vs = [v for e in M for v in e]
                cnt += len(vs) == len(set(vs))
        assert abs(f(t, mp.mpf(1))[0] - cnt) < mp.mpf(10) ** -20


@pytest.mark.parametrize("prod", [True, False])
def test_derivative_recursion_matches_finite_difference(prod):
    f = _model(prod)
    for n, t in _ALL:
        for x in (mp.mpf("0.3"), mp.mpf(2), mp.mpf(7)):
            h = mp.mpf(10) ** -12
            fd = (mp.log(f(t, x + h)[0]) - mp.log(f(t, x - h)[0])) / (2 * h)
            assert abs(fd - f(t, x)[2]) < mp.mpf(10) ** -8


@pytest.mark.parametrize("prod,lam0", [(True, 0), (False, 1)])
def test_both_invariant_rows_hold_numerically(prod, lam0):
    """row 0: x D <= n c; row 1: x D + x E <= n c - c, with c = x/(1+x), on a grid of x >= lam0."""
    f = _model(prod)
    for n, t in _ALL:
        for i in range(0, 60):
            x = mp.mpf(lam0) + mp.mpf(i) / 6
            T, y, D, E = f(t, x)
            c = x / (1 + x)
            assert x * D <= n * c + mp.mpf(10) ** -20
            assert x * D + x * E <= n * c - c + mp.mpf(10) ** -20


@pytest.mark.parametrize("prod,lam0", [(True, 0), (False, 1)])
def test_ratio_antitone_and_anchored_bound_numerically(prod, lam0):
    f = _model(prod)
    for n, t in _ALL:
        prev = None
        for i in range(0, 80):
            x = mp.mpf(lam0) + mp.mpf(i) / 8
            r = f(t, x)[0] / (1 + x) ** n
            if prev is not None:
                assert r <= prev + mp.mpf(10) ** -20
            prev = r
            assert r <= 1 + mp.mpf(10) ** -20         # the anchor holds at lam0 (Z(0) = 1;
            #                                           matchings <= 2^n at lam = 1)


def test_matching_threshold_is_load_bearing():
    """Below lam = 1 the sum-mode row-0 residual x(1+x)(1+ax)(1+a(x-1)) goes negative for a
    large aggregate: the certificate on [0, oo) is refused (the true bound needs another route)."""
    with pytest.raises(AnchoredMonotoneRefusal, match="obligation res0"):
        anchored_monotone_extension_certificate(**_spec(MATCHING_SPEC, lam0=0,
                                                        anchor={"kind": "hypothesis", "at": 0}))


def test_too_small_normalizer_is_genuinely_false():
    """A single vertex has Z = 1 + x > (1 + 3x/4)^1 for x > 0."""
    f = _model(True)
    for x in (mp.mpf("0.1"), mp.mpf(1), mp.mpf(5)):
        assert f((), x)[0] > 1 + 3 * x / 4


# ---- the certificate -----------------------------------------------------------------------

def test_obligation_lists(hc, mt):
    names = [o.name for o in hc.obligations]
    assert names == ["gN", "gD", "hN", "hD", "hle", "pN", "pD", "mN", "mD", "kD",
                     "K0", "K0le", "res0", "K1", "K1le", "res1", "anchor"]
    assert [o.name for o in mt.obligations] == [n for n in names if n not in ("hle", "anchor")]
    assert hc.checked and mt.checked and hc.prod and not mt.prod


def test_residuals_are_the_expected_polynomials(hc, mt):
    x, a, k = sp.symbols("x a k")
    r0 = hc.obligation("res0").cert.polynomial().as_expr()
    assert sp.expand(r0 - x * (x + 1) * (a * x + 1) * (a * k * x - a + 1)) == 0
    m0 = mt.obligation("res0").cert.polynomial().as_expr()
    assert sp.expand(m0 - x * (x + 1) * (a * x + 1) * (a * x - a + 1)) == 0
    assert hc.obligation("res1").cert.polynomial().is_zero


def test_every_cell_reexpands_and_is_signed(hc, mt):
    for c in (hc, mt):
        for o in c.obligations:
            P = o.cert.polynomial()
            for cell in o.cert.leaves():
                assert cell_identity_holds(P, cell)
            assert o.cert.ok()


def test_verify_certificate_rejects_tampering(hc):
    o = hc.obligation("res0")
    bad_poly = replace(o.cert, poly=o.cert.poly[:-1])
    obs = tuple(replace(ob, cert=bad_poly) if ob.name == "res0" else ob for ob in hc.obligations)
    with pytest.raises(AnchoredMonotoneRefusal, match="does not match"):
        verify_certificate(replace(hc, obligations=obs))
    cell = o.cert.tree
    forged = replace(cell, coeffs=cell.coeffs[:-1])
    obs = tuple(replace(ob, cert=replace(ob.cert, tree=forged)) if ob.name == "res0" else ob
                for ob in hc.obligations)
    with pytest.raises(AnchoredMonotoneRefusal, match="re-expand"):
        verify_certificate(replace(hc, obligations=obs))
    with pytest.raises(AnchoredMonotoneRefusal, match="obligation list"):
        verify_certificate(replace(hc, obligations=hc.obligations[:-1]))


def test_rational_exponent_and_node_anchor():
    c = anchored_monotone_extension_certificate(**_spec(HARDCORE_CUBE_SPEC))
    assert c.rho == sp.Rational(1, 3) and c.anchor == {"kind": "node", "p": 1, "q": 3}


def test_hypothesis_anchor_is_carried(mt):
    assert mt.anchor == {"kind": "hypothesis", "at": 1}


def test_subdivision_is_found_and_verified():
    """A positive polynomial with a negative coefficient at degree: the cover bisects."""
    P = sp.Poly((A_SYM - sp.Rational(1, 2)) ** 2 + sp.Rational(1, 100) + 0 * X_SYM,
                X_SYM, A_SYM, sp.Symbol("k"), domain="QQ")
    dom = ((sp.Rational(0), None), (sp.Rational(0), sp.Rational(1)), (0, 0))
    mc = _mcert(P, dom, True, check=True, what="t")
    assert len(mc.leaves()) > 1 and mc.ok()
    for cell in mc.leaves():
        assert cell_identity_holds(P, cell)


# ---- refusals ------------------------------------------------------------------------------

def test_too_small_normalizer_refused_with_located_violation():
    with pytest.raises(AnchoredMonotoneRefusal, match="obligation res0.*FALSE at"):
        anchored_monotone_extension_certificate(**_spec(HARDCORE_TOO_SMALL_SPEC))


@pytest.mark.parametrize("override,msg", [
    ({"mode": "max"}, "mode"),
    ({"lam0": -1}, "lam0"),
    ({"lam0": 0.5}, "float"),
    ({"rho": 0}, "rho"),
    ({"g": "1 + 0.5*lam*A"}, "float"),
    ({"g": "1 + lam*B"}, "only the symbols"),
    ({"psi": "1 + lam*A"}, "only the symbols"),
    ({"anchor": {"kind": "magic"}}, "kind must be"),
    ({"anchor": {"kind": "hypothesis", "at": -1}}, "anchor point"),
    ({"h": "2/(1 + lam*A)"}, "obligation hle"),          # product mode needs messages <= 1
    ({"g": "1 - lam*A"}, "obligation gN"),               # node factor not positive
    ({"mu": "-1"}, "obligation mN"),                     # mu must be > 0
    ({"psi": "1 + lam/3", "kappa": "-lam/(3 + lam)"}, "obligation res0"),
])
def test_refusals(override, msg):
    with pytest.raises(AnchoredMonotoneRefusal, match=msg):
        anchored_monotone_extension_certificate(**_spec(HARDCORE_SPEC, **override))


def test_matching_node_anchor_refused():
    """The node check g(1, A) = 1 + A <= psi(1) = 2 fails for an unbounded sum aggregate."""
    with pytest.raises(AnchoredMonotoneRefusal, match="obligation anchor"):
        anchored_monotone_extension_certificate(**_spec(MATCHING_SPEC, anchor={"kind": "node"}))


def test_forged_certificate_is_unchecked():
    c = anchored_monotone_extension_certificate(**_spec(HARDCORE_TOO_SMALL_SPEC), check=False)
    assert not c.checked
    assert not c.obligation("res0").cert.ok()
    assert all(o.cert.ok() for o in c.obligations if o.name != "res0")


# ---- emission ------------------------------------------------------------------------------

def _emit(specs_names):
    fam = anchored_monotone_extension_family(
        "AMETest", GridSpec([("case", list(range(len(specs_names))))]),
        lambda pt: specs_names[pt["case"]][1], spec=lambda pt: specs_names[pt["case"]][0])
    rep = emit(certify(fam), LeanProfile(namespace=("AMETest",)),
               [AnchoredMonotoneExtensionEmitter()],
               ValidationReport(checks=(("anchored_monotone_extension", True),)))
    return next(iter(rep.files.values()))


def test_emitted_text_shape():
    text = _emit([(HARDCORE_SPEC, "hc"), (MATCHING_SPEC, "mt")])
    for s in ("theorem hasDeriv_rec", "theorem hasDerivAt_log_T", "theorem invariant",
              "theorem logratio_antitone", "theorem ratio_antitone", "theorem anchored_extension",
              "theorem anchor_of_node", "theorem hc :", "theorem hc_pow :", "theorem hc_anchor",
              "theorem hc_checks", "theorem hc_res0", "theorem hc_deriv_bound",
              "theorem hc_antitone_pow", "theorem hc_sanity1", "theorem mt (hanchor",
              "theorem mt_pow (hanchor", "theorem mt_logderiv"):
        assert s in text, s
    assert text.count("theorem invariant") == 1
    assert "sorry" not in text and "axiom " not in text and "native_decide" not in text
    assert "admit" not in text


def test_emitter_for_kind():
    assert type(emitter_for("anchored_monotone_extension")).__name__ == \
        "AnchoredMonotoneExtensionEmitter"


def test_dogfood_is_frozen():
    import subprocess
    r = subprocess.run([sys.executable, str(_EX / "generate.py"), "--check"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr


def _ready() -> bool:
    from lean_env import lean_env_ready
    return lean_env_ready(_EX / "lean")


@pytest.mark.skipif(not _ready(), reason="anchored_monotone_extension Lean env not built")
def test_split_cells_compile():
    """The le_or_gt cell-split tactic (not exercised by the dogfood) closes a bisected cover."""
    from telperion.verify import verify_lean
    P = sp.Poly((A_SYM - sp.Rational(1, 2)) ** 2 + sp.Rational(1, 100) + 0 * X_SYM,
                X_SYM, A_SYM, sp.Symbol("k"), domain="QQ")
    dom = ((sp.Rational(0), None), (sp.Rational(0), sp.Rational(1)), (0, 0))
    mc = _mcert(P, dom, True, check=True, what="t")
    tac = _tree_tactic(mc.tree, "t", (0, 1), "  ")
    src = ("import Mathlib\n\ntheorem split_probe (x a : ℝ) (hx : (0 : ℝ) ≤ x) (ha0 : 0 ≤ a) "
           "(ha1 : a ≤ 1) :\n    0 < (a - 1 / 2) ^ 2 + 1 / 100 := by\n" + tac + "\n")
    res = verify_lean(src, env_dir=str(_EX / "lean"), decls=("split_probe",))
    assert res.okay and res.axioms_clean, res
