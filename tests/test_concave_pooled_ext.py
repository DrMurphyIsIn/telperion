"""Extension tests (2026-10-01) for concave_pooled_induction: leaf-exempt children and a
log term in the per-node profit g.  Both extensions are backward compatible: the original
specs build byte-identical certificates and the original example regenerates unchanged.

The claims are checked numerically on random trees FIRST (independently of the certificate):
the leaf-exempt bound on every non-leaf tree, the fact that the single leaf violates it (so
no pooled certificate can prove it), and the log-profit bound on every tree.

conjecture1_proved = False.
"""
import math
import random
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.emit_concave_pooled_induction import (  # noqa: E402
    LEAF_EXEMPT_FLAT_SPEC,
    LEAF_EXEMPT_LOG_SPEC,
    LEAF_EXEMPT_SPEC,
    LOG_PROFIT_SPEC,
    MATCHING_DENSITY_SPEC,
    PATH_DENSITY_SPEC,
    ConcavePooledInductionEmitter,
    concave_pooled_certificate,
    verify_certificate,
)
from telperion.negative_control_harness import emit_via_single_instance_family  # noqa: E402

F = Fraction


# ---- independent numerical check of the claims --------------------------------------------

def _tree(rng, depth, maxdeg):
    if depth == 0 or rng.random() < 0.35:
        return []
    return [_tree(rng, depth - 1, maxdeg) for _ in range(rng.randint(1, maxdeg))]


def _eval(t, h, g, y0, l0):
    if not t:
        return y0, l0, 1
    ys, ls, ss = zip(*(_eval(c, h, g, y0, l0) for c in t))
    R, m = sum(ys), len(t)
    return h(m, R), sum(ls) + g(m, R), sum(ss) + 1


def _U(nodes, x):
    xs = [F(int(a.p), int(a.q)) if hasattr(a, "p") else F(a) for a, _ in nodes]
    vs = [F(int(b.p), int(b.q)) if hasattr(b, "p") else F(b) for _, b in nodes]
    for i in range(len(xs) - 1):
        if xs[i] <= x <= xs[i + 1]:
            return vs[i] + (vs[i + 1] - vs[i]) * (x - xs[i]) / (xs[i + 1] - xs[i])
    raise AssertionError(f"{x} outside the witness interval")


def _matched_h(m, R):
    return 1 / (1 + R)


def _matched_g(m, R):
    return -R / (1 + R)


def test_leaf_exempt_claim_holds_numerically_and_the_leaf_breaks_it():
    rng = random.Random(20261001)
    alpha = F(27, 100)
    nodes = LEAF_EXEMPT_SPEC["nodes"]
    worst = None
    for _ in range(3000):
        t = _tree(rng, 7, 2)
        if not t:
            continue
        y, ell, n = _eval(t, _matched_h, _matched_g, F(1), F(0))
        assert F(1, 3) <= y <= F(3, 4)
        val = ell + alpha * n
        assert val <= _U(nodes, y), (t, y, val)
        worst = val if worst is None else max(worst, val)
    assert worst <= F(83, 500)
    # the one-vertex tree: ell + alpha = 27/100 > 83/500 = max U -- a pooled certificate
    # (which must cover it) can never give this uniform bound
    assert F(0) + alpha > F(83, 500)


def test_flat_exempt_claim_is_tight_at_the_cherry():
    # root with two leaf children: y = 1/3, ell = -(1 - 1/3) - 0 - 0, n = 3
    ell = -(1 - F(1, 3))
    assert ell + F(1, 4) * 3 == F(1, 12)


def test_log_profit_claim_holds_numerically():
    rng = random.Random(7)
    U = MATCHING_DENSITY_SPEC["nodes"]
    for _ in range(1500):
        t = _tree(rng, 6, 6)
        y, ell, n = _eval(t, lambda m, R: 1 / (1 + R),
                          lambda m, R: -1 / (1 + R) + math.log(1 + R / 2) / 5, 1.0, -1.0)
        assert ell + 0.5 * n <= float(_U(U, F(y).limit_denominator(10 ** 12))) + 1e-9


def test_leaf_exempt_log_claim_holds_numerically():
    rng = random.Random(11)
    for _ in range(1500):
        t = _tree(rng, 7, 2)
        if not t:
            continue
        y, ell, n = _eval(t, lambda m, R: 1 / (1 + R),
                          lambda m, R: -R / (1 + R) + math.log(1 + R / 2) / 10, 1.0, 0.0)
        assert ell + 0.2 * n <= 0.1 + 1e-9


# ---- certificates ------------------------------------------------------------------------

@pytest.mark.parametrize("spec", [LEAF_EXEMPT_SPEC, LEAF_EXEMPT_FLAT_SPEC, LOG_PROFIT_SPEC,
                                  LEAF_EXEMPT_LOG_SPEC],
                         ids=["exempt", "exempt_flat", "log", "exempt_log"])
def test_extension_certificates_build_and_reverify(spec):
    c = concave_pooled_certificate(**spec)
    verify_certificate(c)
    assert c.checked
    if spec.get("exempt_leaves"):
        assert c.exempt and not c.tail
        assert sorted(a.k for a in c.atom_cases) == list(range(1, c.M + 1))
        assert all(cl.p is not None and cl.p >= 1 and cl.m == cl.p + cl.k for cl in c.cells)
    if "log(" in spec["g"]:
        assert c.logs and all(len(cl.logb) == len(c.logs) for cl in c.cells)


def test_pooled_mode_refuses_the_exempt_claim():
    """The same witness without exemption: the leaf message 1 is outside I; widening I to
    contain it, the base fails (the leaf breaks the pooled witness)."""
    base = {k: v for k, v in LEAF_EXEMPT_SPEC.items() if k != "exempt_leaves"}
    with pytest.raises(ValueError, match="outside I"):
        concave_pooled_certificate(**base)
    wide = dict(base, nodes=[(sp.Rational(1, 3), sp.Rational(83, 500)), (1, sp.Rational(83, 500))])
    with pytest.raises(ValueError, match="base fails"):
        concave_pooled_certificate(**wide)


def test_exempt_refuses_a_tail():
    with pytest.raises(ValueError, match="bounded-degree only"):
        concave_pooled_certificate(**dict(LEAF_EXEMPT_SPEC, tail=True))


def test_exempt_refuses_a_lowered_witness():
    nodes = [(x, v - sp.Rational(1, 1000)) for x, v in LEAF_EXEMPT_FLAT_SPEC["nodes"]]
    with pytest.raises(ValueError, match="all-leaves node k = 2"):
        concave_pooled_certificate(**dict(LEAF_EXEMPT_FLAT_SPEC, nodes=nodes))


@pytest.mark.parametrize("g, why", [
    ("-1/(1+R) - log(1 + R)/5", "<= 0"),
    ("-1/(1+R) + log(1 + R**2)/5", "not affine"),
    ("-1/(1+R) + log(R - 1)/5", "a0 > 0"),
    ("-1/(1+R) + log(1 + m*R)/5", "depend on R only"),
    ("-1/(1+R) + x*log(1 + R)/5", "rational constant"),
])
def test_log_refusals(g, why):
    with pytest.raises(ValueError, match=why):
        concave_pooled_certificate(**dict(MATCHING_DENSITY_SPEC, g=g))


def test_log_needs_nonnegative_messages():
    spec = dict(MATCHING_DENSITY_SPEC, g="-1/(1+R) + log(1 + R/2)/5",
                nodes=[(-1, 0), (0, 0), (1, sp.Rational(-3, 10))])
    with pytest.raises(ValueError, match="lo >= 0"):
        concave_pooled_certificate(**spec)


def test_log_profit_with_too_large_alpha_is_refused():
    with pytest.raises(ValueError, match="REFUSED"):
        concave_pooled_certificate(**dict(LOG_PROFIT_SPEC, alpha=sp.Rational(11, 20)))


# ---- backward compatibility -------------------------------------------------------------

@pytest.mark.parametrize("spec", [MATCHING_DENSITY_SPEC, PATH_DENSITY_SPEC])
def test_original_certificates_carry_default_extension_fields(spec):
    c = concave_pooled_certificate(**spec)
    assert not c.exempt and c.logs == () and c.atom_cases == ()
    assert all(cl.p is None and cl.k == 0 and cl.logb == () for cl in c.cells)


def test_original_emission_has_no_extension_sections():
    c = concave_pooled_certificate(**PATH_DENSITY_SPEC)
    text = emit_via_single_instance_family(ConcavePooledInductionEmitter(), lean_name="t",
                                           instance_kwargs={"payload": c})
    assert "exempt_induction_core" not in text and "log_tangent_le" not in text


def test_extension_emission_sections():
    c = concave_pooled_certificate(**LEAF_EXEMPT_LOG_SPEC)
    text = emit_via_single_instance_family(ConcavePooledInductionEmitter(), lean_name="t",
                                           instance_kwargs={"payload": c})
    for needle in ("theorem exempt_induction_core", "theorem minPieces_jensen_on",
                   "theorem log_tangent_le", "theorem t (b : PTree) (hn : b.isNode = true)",
                   "theorem t_xhstep", "theorem t_xs_0_2", "Real.log", "theorem t_logH0"):
        assert needle in text, needle
    assert "sorry" not in text and "native_decide" not in text


@pytest.mark.parametrize("script", ["generate.py", "generate_ext.py"])
def test_examples_regenerate_byte_for_byte(script):
    r = subprocess.run([sys.executable, str(ROOT / "examples" / "concave_pooled_induction" / script),
                        "--check"], cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
