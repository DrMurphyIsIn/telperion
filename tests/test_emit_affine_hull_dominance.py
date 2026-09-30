"""Tests for the affine_hull_dominance emitter (exact tree maxima of a positive multilinear
recursion by convex-hull pruning with convex-combination domination witnesses).

Offline: the recursions against INDEPENDENT graph computations (matchings and edge sums from
the adjacency lists, not the recursion), the certified maxima and maximizer lists against
brute force over every tree, exact certificate re-verification, every refusal, the emitted Lean
text, and the frozen dogfood.  The kernel run is the dogfood `lake build` (CI) and the
lean-gated negative control in `test_certificate_sensitivity`.

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_affine_hull_dominance import (  # noqa: E402
    MATCHING_SUM_RECURSION,
    RANDIC_SUM_RECURSION,
    SYNTHETIC_RECURSION,
    AffineHullDominanceEmitter,
    _canon_unrooted,
    affine_hull_dominance_family,
    eval_pi,
    hull_dominance_certificate,
    hull_recursion,
    kept_points,
    verify_certificate,
    witness_ok,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.negctrl_adapters.adapter_affine_hull_dominance import rooted_trees  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "affine_hull_dominance"


# ---- independent graph computations --------------------------------------------------------

def _adj(tree):
    adj = [[]]

    def add(t, parent):
        v = len(adj)
        adj.append([parent])
        adj[parent].append(v)
        for ch in t:
            add(ch, v)

    for ch in tree:
        add(ch, 0)
    return adj


def _edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def matching_sum_direct(tree) -> Fraction:
    """sum over matchings of prod 1/(deg u deg v), by explicit enumeration of matchings."""
    adj = _adj(tree)
    deg = [len(a) for a in adj]
    E = _edges(adj)

    def go(i, used):
        if i == len(E):
            return Fraction(1)
        u, v = E[i]
        tot = go(i + 1, used)
        if u not in used and v not in used:
            tot += Fraction(1, deg[u] * deg[v]) * go(i + 1, used | {u, v})
        return tot

    return go(0, frozenset())


def randic_plus_one_direct(tree) -> Fraction:
    adj = _adj(tree)
    deg = [len(a) for a in adj]
    return 1 + sum((Fraction(1, deg[u] * deg[v]) for u, v in _edges(adj)), Fraction(0))


@pytest.fixture(scope="module")
def matching():
    return hull_dominance_certificate(recursion=MATCHING_SUM_RECURSION, N=10)


@pytest.fixture(scope="module")
def randic():
    return hull_dominance_certificate(recursion=RANDIC_SUM_RECURSION, N=9)


@pytest.fixture(scope="module")
def synthetic():
    return hull_dominance_certificate(recursion=SYNTHETIC_RECURSION, N=10)


# ---- the recursions compute what they claim ------------------------------------------------

def test_matching_recursion_is_the_matching_sum():
    rec = hull_recursion(**MATCHING_SUM_RECURSION)
    for n in range(2, 9):
        for t in rooted_trees(n):
            assert eval_pi(rec, t) == matching_sum_direct(t)


def test_randic_recursion_is_one_plus_the_edge_sum():
    rec = hull_recursion(**RANDIC_SUM_RECURSION)
    for n in range(2, 9):
        for t in rooted_trees(n):
            assert eval_pi(rec, t) == randic_plus_one_direct(t)


# ---- certified maxima and maximizers against brute force -----------------------------------

@pytest.mark.parametrize("which", ["matching", "randic", "synthetic"])
def test_maxima_and_maximizer_lists_match_brute_force(which, request):
    cert = request.getfixturevalue(which)
    rec = cert.rec
    for n in range(2, min(cert.N, 9) + 1):
        vals = {t: eval_pi(rec, t) for t in rooted_trees(n)}
        best = max(vals.values())
        assert cert.value(n) == best, (which, n)
        brute = {_canon_unrooted(t) for t, v in vals.items() if v == best}
        listed = {_canon_unrooted(t) for t in dict(cert.maximizers)[n]}
        assert listed == brute, (which, n)


def test_known_values(matching):
    # path P4 (5/2) and the unique maximizers are spiders; spot values
    assert matching.value(4) == Fraction(5, 2)
    assert matching.value(6) == Fraction(29, 8)
    assert matching.value(10) == Fraction(65, 8)


def test_certificate_reverifies_and_every_witness_is_sound(matching, randic, synthetic):
    for cert in (matching, randic, synthetic):
        verify_certificate(cert)
        KB, KH = cert.kb(), cert.kh()
        for (s, c), wits in cert.WB:
            assert all(w[0] in ("kept", "dom") for w in wits)
        assert cert.n_candidates > 50
        assert any(w[0] == "dom" for _, ws in cert.WB + cert.WH for w in ws)
        assert all(K for (s, c), K in KB.items() if c <= s and s >= c >= 1 or s == c == 0)
        assert all(K for m, K in KH.items())


def test_nontrivial_hulls_and_ties(synthetic, randic):
    assert max(len(K) for _, K in synthetic.KB) >= 5
    assert any(len(ts) > 1 for _, ts in randic.maximizers)


def test_a_corrupted_witness_is_refused(matching):
    (key, wits) = next((k, w) for k, w in matching.WB if any(x[0] == "dom" for x in w))
    i = next(i for i, x in enumerate(wits) if x[0] == "dom")
    bad = list(wits)
    n = len(bad[i][1])
    bad[i] = ("dom", tuple(Fraction(1, n) - (Fraction(1, 2) if t == 0 else 0) +
                           (Fraction(1, 2) if t == n - 1 else 0) for t in range(n)))
    WB = dict(matching.WB)
    WB[key] = tuple(bad)
    forged = replace(matching, WB=tuple(sorted(WB.items())))
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(forged)


def test_wrong_value_is_refused(matching):
    vals = tuple((n, v - Fraction(1, 1000) if n == 7 else v) for n, v in matching.values)
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(replace(matching, values=vals))


def test_kept_points_are_exactly_the_positively_supported_ones():
    pts = [(Fraction(0), Fraction(2)), (Fraction(1), Fraction(1)), (Fraction(2), Fraction(0)),
           (Fraction(1, 2), Fraction(1, 2)), (Fraction(1), Fraction(1, 2))]
    K = kept_points(pts)
    assert K == [(0, 2), (1, 1), (2, 0)]              # (1,1) lies on the hull edge: kept
    assert witness_ok(K, (Fraction(1, 2), Fraction(1, 2)),
                      ("dom", (Fraction(1, 2), Fraction(1, 2), Fraction(0))))
    three = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (Fraction(1, 4), Fraction(1, 4), Fraction(1, 4))]
    K3 = kept_points([tuple(Fraction(v) for v in p) for p in three])
    assert len(K3) == 3


# ---- refusals ------------------------------------------------------------------------------

def test_refuses_floats():
    with pytest.raises(ValueError, match="REFUSED"):
        hull_recursion(**dict(MATCHING_SUM_RECURSION, e=(1.0, 0)))
    with pytest.raises(ValueError, match="REFUSED"):
        hull_recursion(**dict(MATCHING_SUM_RECURSION, P=(("1", "0.5"), ("1/(c+1)", "0"))))


def test_refuses_negative_coefficient():
    T = dict(MATCHING_SUM_RECURSION["T"])
    T[(1, 1, 0)] = -1
    with pytest.raises(ValueError, match="negative coefficient"):
        hull_dominance_certificate(recursion=dict(MATCHING_SUM_RECURSION, T=T), N=5)


def test_refuses_invisible_column():
    with pytest.raises(ValueError, match="column 1 of P_"):
        hull_dominance_certificate(
            recursion=dict(MATCHING_SUM_RECURSION, P=(("1", "0"), ("1/(c+1)", "0"))), N=5)


def test_refuses_nonstrict_root_for_maximizers_but_allows_value_only():
    plain = dict(RANDIC_SUM_RECURSION, F=("0", "1", "1/k"))     # the edge sum without the + 1
    with pytest.raises(ValueError, match="not strictly positive"):
        hull_dominance_certificate(recursion=plain, N=6)
    cert = hull_dominance_certificate(recursion=plain, N=6, maximizers=False)
    assert cert.value(6) == Fraction(7, 4)                       # the path: 2/2 + 3/4
    text, _ = AffineHullDominanceEmitter()._emit_instance(cert, "plain")
    assert "plain_kept_" not in text and "plain_max_6" in text


def test_refuses_bad_N():
    for N in (1, 17, "5"):
        with pytest.raises(ValueError, match="REFUSED"):
            hull_dominance_certificate(recursion=MATCHING_SUM_RECURSION, N=N)


def test_refuses_shape_errors():
    with pytest.raises(ValueError, match="REFUSED"):
        hull_recursion(**dict(MATCHING_SUM_RECURSION, e=(1, 0, 0)))
    with pytest.raises(ValueError, match="REFUSED"):
        hull_recursion(**dict(MATCHING_SUM_RECURSION, T={(0, 0, 2): 1}))
    with pytest.raises(ValueError, match="REFUSED"):
        hull_recursion(**dict(MATCHING_SUM_RECURSION, F=("1", "1/q")))


# ---- the emitted Lean ----------------------------------------------------------------------

def _emit_one(spec, name="inst"):
    fam = affine_hull_dominance_family(
        "AHDTest", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    rep = emit(certify(fam), LeanProfile(namespace=("AHDTest",)),
               [AffineHullDominanceEmitter()],
               ValidationReport(checks=(("affine_hull_dominance", True),)))
    return next(iter(rep.files.values()))


def test_emitted_text_shape():
    text = _emit_one(dict(recursion=MATCHING_SUM_RECURSION, N=6), name="ms")
    for needle in ("theorem inv_bundle", "theorem kept_bundle", "theorem pi_le",
                   "theorem kept_of_pi_eq", "theorem isGreatest_pi",
                   "theorem ms_valid : ms_C.Valid ms_R 6 (0 : Fin 2) := by decide +kernel",
                   "theorem ms_max_6 :", "theorem ms_kept_6 :", "theorem ms_listed_6 :",
                   "IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ ms_R.pi T = x} (29 / 8 : ℚ)",
                   "theorem ms :"):
        assert needle in text, needle
    assert "sorry" not in text and "native_decide" not in text
    assert not any(0x1F000 <= ord(ch) <= 0x1FAFF or 0x2600 <= ord(ch) <= 0x27BF for ch in text)


def test_emitter_for_resolves_the_kind():
    assert isinstance(emitter_for("affine_hull_dominance"), AffineHullDominanceEmitter)


def test_no_emoji_or_local_paths_in_sources():
    root = Path(__file__).resolve().parents[1]
    files = [root / "src" / "telperion" / "emit_affine_hull_dominance.py",
             root / "src" / "telperion" / "negctrl_adapters" / "adapter_affine_hull_dominance.py",
             _EX / "generate.py"]
    for f in files:
        s = f.read_text(encoding="utf-8")
        assert not any(0x1F000 <= ord(ch) <= 0x1FAFF or 0x2600 <= ord(ch) <= 0x27BF
                       for ch in s), f
        for word in ("CONFIDENTIAL", "/Users/", "~/"):
            assert word not in s, (f, word)


def test_frozen_dogfood_matches_regeneration():
    import importlib.util

    spec = importlib.util.spec_from_file_location("ahd_generate", _EX / "generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    out = _EX / "lean" / "AffineHullDominance.lean"
    assert out.read_text(encoding="utf-8") == mod.build()
