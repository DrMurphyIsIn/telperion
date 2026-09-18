"""Robin-growth emitter — RH Face 2 (temperedness).

Certifies a rung of Robin's theorem (RH ⟺ σ(n) < e^γ·n·log log n for all
n > 5040): the exact divisor sum σ(n) and a rigorous rational lower bound `Llo`
(flint/Arb) on the transcendental RHS, carried as the trust-seam hypothesis
`hR : Llo ≤ R`.  A finite rung, NOT RH.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    RobinGrowthEmitter,
    ValidationReport,
    certify,
    emit,
    robin_growth_certificate,
    robin_growth_family,
)
from telperion.emit_robin_growth import (  # noqa: E402
    ROBIN_THRESHOLD,
    robin_refutation_atom_lean,
    sigma_exact,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_PROFILE = LeanProfile(namespace=("Robin",), imports=("Mathlib",))


def _emit(fam):
    report = emit(certify(fam), _PROFILE,
                  [RobinGrowthEmitter()], ValidationReport(checks=(("robin", True),)))
    return next(iter(report.files.values()))


def test_sigma_exact_is_integer_divisor_sum():
    assert sigma_exact(6) == 12          # 1+2+3+6
    assert sigma_exact(5041) == 5113     # 5041 = 71^2 -> 1+71+5041 ... check
    # 71^2: divisors 1,71,5041 -> 5113
    assert sigma_exact(5041) == 1 + 71 + 5041


def test_certificate_refuses_below_threshold():
    """NEGATIVE CONTROL: n ≤ 5040 is outside Robin's RH-equivalent range."""
    for bad_n in (5040, 12, 5040):
        with pytest.raises(ValueError):
            robin_growth_certificate(bad_n, Fraction(10**9))
    assert ROBIN_THRESHOLD == 5040


def test_certificate_refuses_nonstrict_lower_bound():
    """NEGATIVE CONTROL: a lower bound at or below σ(n) cannot witness σ(n) < R."""
    n = 10080
    sig = sigma_exact(n)
    with pytest.raises(ValueError):
        robin_growth_certificate(n, Fraction(sig))        # Llo = σ(n): not strict
    with pytest.raises(ValueError):
        robin_growth_certificate(n, Fraction(sig - 1))    # Llo < σ(n)
    # a strictly-larger Llo is accepted
    cert = robin_growth_certificate(n, Fraction(sig + 1))
    assert cert.n == n and cert.sigma == sig


def test_certificate_refuses_wrong_supplied_sigma():
    with pytest.raises(ValueError):
        robin_growth_certificate(5041, Fraction(10**9), sigma=9999)


def test_certify_refuses_bad_family():
    fam = robin_growth_family("Bad", GridSpec([("_", [0])]), lambda pt: "robin_bad",
                              spec=lambda pt: {"n": 5040, "Llo": Fraction(10**9)})
    with pytest.raises(Exception):
        certify(fam)


def test_emit_is_load_bearing_and_deterministic():
    n = 5041
    sig = sigma_exact(n)
    lo = Fraction(sig) + 1  # a rigorous-for-this-test strict lower bound
    fam = robin_growth_family("R", GridSpec([("n", [n])]),
                              lambda pt: f"robin_n{pt['n']}",
                              spec=lambda pt: {"n": pt["n"], "Llo": lo})
    text = _emit(fam)
    assert f"theorem robin_n{n}" in text
    # the emitted claim is about σ(n) (the exact integer), non-vacuous
    assert f"({sig} : ℝ)" in text
    # trust seam explicit + trivial kernel step
    assert "hR" in text and "lt_of_lt_of_le" in text and "norm_num" in text
    # ties to Robin's equivalence in the provenance
    assert "5040" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert _emit(fam) == text


def test_refutation_atom_shape():
    txt = robin_refutation_atom_lean()
    assert "theorem robin_neg_refutes" in txt
    assert "¬P" in txt
    assert "hRobin" in txt and "le_trans" in txt


def test_arb_lower_bound_is_rigorous():
    """The flint/Arb driver returns a genuine LOWER bound of e^γ·n·log log n."""
    pytest.importorskip("flint")
    mp = pytest.importorskip("mpmath")
    from telperion.emit_robin_growth import robin_rhs_lower_bound

    mp.mp.dps = 60
    for n in (5041, 10080, 55440):
        lo = robin_rhs_lower_bound(n)
        true_rhs = mp.e ** mp.euler * n * mp.log(mp.log(n))
        assert mp.mpf(lo.numerator) / lo.denominator <= true_rhs
        assert Fraction(sigma_exact(n)) < lo  # and it clears Robin at these n


def test_emitter_is_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "RobinGrowthEmitter" in REGISTRY
    assert "RobinGrowthEmitter" not in set(unclassified_emitters())


def test_generated_example_builds_rungs():
    pytest.importorskip("flint")
    import importlib.util as _u
    gen_path = (Path(__file__).resolve().parents[1]
                / "examples" / "robin_growth" / "generate.py")
    spec = _u.spec_from_file_location("robin_growth_generate", gen_path)
    mod = _u.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert text.count("theorem robin_neg_refutes") == 1
    # all rungs are above the threshold and each emits its own theorem
    for n in mod.RUNGS:
        assert n > ROBIN_THRESHOLD
        assert f"theorem robin_n{n} " in text
    # exactly len(RUNGS) rung theorems (exclude the refutation atom)
    assert sum(f"theorem robin_n{n} " in text for n in mod.RUNGS) == len(mod.RUNGS)
