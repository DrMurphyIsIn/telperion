"""gap_budget_multiplicity emitter -- pruning a multiset optimisation by a tangent-price gap
budget (caps, exclusions, a certified tail, a decided knapsack).

Acceptance is pinned on the dogfood with EXACT certificates: the classical max-product
partition for N = 3t, 3t + 2, 3t + 4 (uniform in t) and a small concave instance at two tangent
points.  Every refusal of the module docstring has a test.  The emitted Lean is pinned by
substring; the Lean kernel is the arbiter (`examples/gap_budget_multiplicity/lean` is compiled,
59 emitted theorems + one cross-check, standard axioms only).

conjecture1_proved = False.
"""
import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    GapBudgetMultiplicityEmitter,
    GapBudgetRefusal,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    gap_budget_multiplicity_certificate,
    gap_budget_multiplicity_family,
)
from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS, emitter_for  # noqa: E402
from telperion.emit_gap_budget_multiplicity import (  # noqa: E402
    CORE_THEOREMS,
    K,
    MAX_ATOMS,
    gb_log,
    gb_logk,
    lean_poly,
    tree_of_constant,
)

T = sp.Symbol("t")
_EX = Path(__file__).resolve().parents[1] / "examples" / "gap_budget_multiplicity"


def _product(M, bench, **kw):
    spec = dict(atoms=(1, None), tail_start=5, w=gb_logk(), ell=K, tau=gb_log(3) / 3,
                params=(T,), M=M, bench=bench)
    spec.update(kw)
    return gap_budget_multiplicity_certificate(**spec)


def _concave(x0, tau, **kw):
    spec = dict(atoms=(1, 6), w=-K ** 2 / 9, ell=1, M=10, bench=((2, 8), (3, 2)),
                tau=tau, concave=("log", 12, x0, K))
    spec.update(kw)
    return gap_budget_multiplicity_certificate(**spec)


def _gen():
    spec = importlib.util.spec_from_file_location("gb_generate", _EX / "generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --- registration -------------------------------------------------------------------------

def test_kind_is_registered_and_dispatches():
    assert "gap_budget_multiplicity" in _SPECIAL_KINDS
    assert _SPECIAL_DISPATCH["gap_budget_multiplicity"][2] == "GapBudgetMultiplicityEmitter"
    assert isinstance(emitter_for("gap_budget_multiplicity"), GapBudgetMultiplicityEmitter)


# --- the classical max-product partition -----------------------------------------------------

def test_mod0_budget_is_zero_and_only_threes_survive():
    c = _product(3 * T, ((3, T),))
    assert c.theta == 0 and c.theta_hi == 0 and c.theta_enc is None
    assert dict(c.caps) == {1: 0, 2: 0, 4: 0}
    assert c.tail_cap == 0 and c.tail.K0 == 5
    assert c.knapsack is None
    assert [a.k for a in c.atoms] == [1, 2, 3, 4]
    assert c.atoms[2].g == 0 and c.atoms[2].enc is None          # the zero-gap atom 3 is exact


def test_mod2_budget_is_gamma2():
    c = _product(3 * T + 2, ((2, 1), (3, T)))
    assert c.theta == sp.expand(2 * gb_log(3) / 3 - gb_log(2))
    assert dict(c.caps) == {1: 0, 2: 1, 4: 0} and c.tail_cap == 0


def test_mod1_budget_is_gamma4_with_the_knapsack():
    c = _product(3 * T + 4, ((3, T), (4, 1)))
    assert c.theta == sp.expand(4 * gb_log(3) / 3 - gb_log(4))
    assert dict(c.caps) == {1: 0, 2: 2, 4: 1} and c.tail_cap == 0
    ks = c.knapsack
    assert ks.atoms == (2, 4) and ks.caps == (2, 1)
    assert set(ks.vectors) == {(0, 0), (0, 1), (1, 0), (2, 0)}
    # the certified numbers are true bounds (checked against mpmath at 50 digits)
    import mpmath as mp
    mp.mp.dps = 50
    gam = {k: k * mp.log(3) / 3 - mp.log(k) for k in range(1, 6)}
    for a in c.atoms:
        assert mp.mpf(a.g.p) / a.g.q <= gam[a.k]
    assert mp.mpf(c.tail.anchor.g.p) / c.tail.anchor.g.q <= gam[5]
    th = 4 * mp.log(3) / 3 - mp.log(4)
    assert th <= mp.mpf(c.theta_hi.p) / c.theta_hi.q


def test_tail_is_certified_by_the_log_tangent():
    c = _product(3 * T + 4, ((3, T), (4, 1)))
    t = c.tail
    assert (t.K0, t.shift, t.c) == (5, 0, 1)
    assert t.P == sp.expand(gb_log(3) / 3)
    assert t.P_lo >= sp.Rational(1, 5)            # slope log3/3 - 1/5 > 0
    assert t.anchor.k == 5 and t.anchor.g > c.theta_hi


# --- the concave instance ------------------------------------------------------------------

def test_concave_sharp_tangent_at_the_benchmark_mean():
    c = _concave(sp.Rational(11, 5), sp.Rational(64, 99))
    assert c.theta == sp.Rational(2, 99)          # the log terms cancel exactly
    assert dict(c.caps) == {1: 0, 3: 2, 4: 0, 5: 0, 6: 0}
    assert c.tail is None and c.knapsack is None


def test_concave_loose_tangent_uses_enclosures_and_the_knapsack():
    c = _concave(2, sp.Rational(4, 5))
    assert c.theta_enc is not None
    assert dict(c.caps) == {1: 1, 2: 9, 4: 2, 5: 0, 6: 0}
    ks = c.knapsack
    assert ks.atoms == (1, 2, 4) and ks.caps == (1, 9, 2)
    assert len(ks.vectors) == 21 and (0, 0, 0) in ks.vectors
    for v in ks.vectors:
        assert sum(x * p for x, p in zip(v, ks.ints)) <= ks.bound


def test_benchmark_satisfies_its_own_consequences():
    for c in (_product(3 * T + 4, ((3, T), (4, 1))), _concave(2, sp.Rational(4, 5))):
        counts = {a: m for a, m in c.bench}
        for k0, cap in c.caps:
            v = counts.get(k0, 0)
            assert sp.sympify(v).subs(T, 7) <= cap


# --- refusals ------------------------------------------------------------------------------

def _refused(match, fn, *a, **kw):
    with pytest.raises(GapBudgetRefusal, match=match):
        fn(*a, **kw)


def test_refuses_floats_and_bools_and_sympy_log():
    _refused("float", _product, 3 * T, ((3, T),), tau=0.366)
    _refused("function", _product, 3 * T, ((3, T),), w=sp.log(K))
    _refused("bool", _concave, True, sp.Rational(4, 5))


def test_refuses_non_concave_or_degenerate_concave_parts():
    _refused("CONVEX", _concave, 2, sp.Rational(4, 5), concave=("log", -12, 2, K))
    _refused("separable", _concave, 2, sp.Rational(4, 5), concave=("log", 0, 2, K))
    _refused("not certified concave", _concave, 2, sp.Rational(4, 5),
             concave=("sqrt", 12, 2, K))
    _refused("domain", _concave, 0, sp.Rational(4, 5))


def test_refuses_a_negative_gap():
    # a price below the best atom: gamma(3) = 2 - 3 < 0 while theta = 0
    _refused("price does not dominate", gap_budget_multiplicity_certificate, atoms=(1, 3),
             w=K, ell=1, tau=2, M=1, bench=((2, 1),))
    # a too-small concave price makes theta negative first: inconsistent input
    _refused("NEGATIVE", _concave, 2, sp.Rational(3, 5))


def test_refuses_a_claimed_gap_bound_the_fold_does_not_imply():
    _refused("fold refuses", _product, 3 * T + 2, ((2, 1), (3, T)),
             gap_lo={2: sp.Rational(1, 20)})
    # a TRUE weaker claim is accepted and becomes the statement
    c = _product(3 * T + 2, ((2, 1), (3, T)), gap_lo={2: sp.Rational(3, 100)})
    assert c.atoms[1].g == sp.Rational(3, 100)


def test_refuses_a_claimed_theta_hi_below_the_truth():
    _refused("fold refuses", _product, 3 * T + 2, ((2, 1), (3, T)),
             theta_hi=sp.Rational(39, 1000))
    _refused("below the exact theta", _concave, sp.Rational(11, 5), sp.Rational(64, 99),
             theta_hi=sp.Rational(1, 99))


def test_refuses_a_parameter_dependent_budget():
    _refused("not uniform", _product, 3 * T + 4, ((3, T), (4, 1)),
             tau=gb_log(3) / 3 + sp.Rational(1, 100))


def test_refuses_an_uncertified_tail():
    # from K0 = 2 the slope log3/3 = 0.366 is below 1/2: monotonicity not certified
    _refused("monotonicity", _product, 3 * T + 4, ((3, T), (4, 1)), tail_start=2,
             atoms=(1, None))
    _refused("needs a certified tail", _product, 3 * T, ((3, T),), tail_start=None)
    _refused("tail_start given", _product, 3 * T, ((3, T),), atoms=(1, 9))


def test_refuses_a_tail_with_a_power_of_log_k():
    """Skeptic repro: (log k)^2 used to slip past the first-power coefficient read, giving a
    false tail bound (gap(5) = -0.090)."""
    _refused("power of log", gap_budget_multiplicity_certificate, atoms=(1, None),
             tail_start=2, w=gb_logk() ** 2, ell=K, tau=sp.Rational(1, 2), M=2,
             bench=((1, 2),), knapsack=False)


def test_enclosure_names_are_instance_scoped():
    txt = _gen().build()
    assert "theorem concave_knapsack_enc0 :" in txt
    assert "price tau = log(3)/3" in txt and "GBL_" not in txt


def test_refuses_benchmark_errors():
    _refused("outside the alphabet", _product, 3 * T, ((0, 1), (3, T)))
    _refused("is not M", _product, 3 * T + 1, ((3, T),))
    _refused("natural-number", _product, 3 * T, ((3, T - 1),))
    _refused("repeated", _product, 3 * T, ((3, T), (3, 1)))


def test_refuses_log_domain_violations():
    _refused("junk", gap_budget_multiplicity_certificate, atoms=(1, 3), w=gb_logk(-1), ell=K,
             tau=1, M=3, bench=((3, 1),))
    _refused("<= 0", gb_log, 0)
    _refused("= 0 exactly", gb_log, 1)


def test_refuses_budgets_that_prune_nothing_and_oversized_inputs():
    _refused("prunes nothing", gap_budget_multiplicity_certificate, atoms=(1, 3), w=K, ell=K,
             tau=1, M=3, bench=((3, 1),))
    _refused("exceed", gap_budget_multiplicity_certificate, atoms=(1, MAX_ATOMS + 1), w=0,
             ell=K, tau=1, M=3, bench=((3, 1),))


def test_refuses_unknown_spec_keys_via_certify():
    fam = gap_budget_multiplicity_family(
        "X", GridSpec([("c", [0])]), lambda pt: "x",
        spec=lambda pt: dict(atoms=(1, 3), w=0, ell=K, tau=1, M=3, bench=((3, 1),), typo=1))
    with pytest.raises(Exception, match="unknown"):
        certify(fam)


# --- rendering -----------------------------------------------------------------------------

def test_lean_poly_rendering_is_deterministic():
    assert lean_poly(gb_log(3) / 3) == "1 / 3 * Real.log 3"
    assert lean_poly(-K ** 2 / 9) == "-(1 / 9 * (k : ℝ) ^ 2)"
    assert lean_poly(gb_logk(1) - 2) == "Real.log ((k : ℝ) + 1) - 2"
    assert lean_poly(3 * T + 4, (T,)) == "3 * (t : ℝ) + 4"
    assert lean_poly(12 * gb_log(sp.Rational(11, 5)) - sp.Rational(50, 9)) \
        == "12 * Real.log (11 / 5) - 50 / 9"


def test_constant_trees_fold_logs_into_atoms():
    tr = tree_of_constant(gb_log(3))
    assert tr.op == "log" and tr.factors is not None      # 3 = 2^2 * 3/4


def test_emitted_text_shape():
    txt = _gen().build()
    assert "sorry" not in txt and "native_decide" not in txt and "axiom " not in txt
    assert txt.count("theorem gapBudget_log_tangent") == 1       # the core, once per file
    assert "theorem maxprod_mod1 (t : ℕ) (m : Multiset ℕ)" in txt
    assert "[m.count 2, m.count 4] ∈ [[0, 0], [0, 1], [1, 0], [2, 0]]" in txt
    assert "(∀ k ∈ m, k < 5)" in txt
    assert "gapBudget_of_concave m concave_knapsack_w" in txt
    assert "Professor" not in txt                                  # credit lives in the docs
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the dogfood file"


def test_theorem_count():
    fam = gap_budget_multiplicity_family(
        "C", GridSpec([("c", [0])]), lambda pt: "cx",
        spec=lambda pt: dict(atoms=(1, 6), w=-K ** 2 / 9, ell=1, M=10,
                             bench=((2, 8), (3, 2)), tau=sp.Rational(64, 99),
                             concave=("log", 12, sp.Rational(11, 5), K)))
    body, n = GapBudgetMultiplicityEmitter().emit_body(certify(fam), LeanProfile())
    # core + 6 exact gap lemmas + bench + main (no enclosures: theta and gaps are rational)
    assert n == CORE_THEOREMS + 6 + 2
    assert body.count("\ntheorem ") + body.startswith("theorem ") == n


def test_dogfood_is_regenerable_byte_for_byte():
    gen = _gen()
    assert gen.main(check=True) == 0


def test_fraction_inputs_are_exact():
    c = _concave(Fraction(11, 5), Fraction(64, 99))
    assert c.theta == sp.Rational(2, 99)


def test_family_emits_through_the_workflow():
    gen = _gen()
    fam = gap_budget_multiplicity_family(
        "GB", GridSpec([("c", [0])]), lambda pt: "gb_mod2",
        spec=lambda pt: gen.SPECS["maxprod_mod2"])
    rep = emit(certify(fam), LeanProfile(namespace=("GB",)), [GapBudgetMultiplicityEmitter()],
               ValidationReport(checks=(("gap_budget_multiplicity", True),)))
    txt = next(iter(rep.files.values()))
    assert "theorem gb_mod2 (t : ℕ)" in txt and "m.count 2 ≤ 1" in txt
