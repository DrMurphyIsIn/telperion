"""Báez-Duarte emitter — RH Face 6 (spectral / approximation).

Certifies a rung of the Báez-Duarte / Bagchi criterion (RH ⟺ d²_N → 0, with
g_k(x) = {1/(kx)} − {1/x}/k in L²(0,1); Bagchi 2006, Thm 7): a rigorous rational
UPPER bound on d²_N from an explicit coefficient vector whose quadratic-form
value Q(c) ≥ d²_N is bounded with exact rationals.  A finite rung, NOT RH.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BaezDuarteEmitter,
    ValidationReport,
    baez_duarte_certificate,
    baez_duarte_family,
    certify,
    emit,
)
from telperion.emit_baez_duarte import (  # noqa: E402
    baez_duarte_refutation_atom_lean,
    baez_duarte_upper_bound,
    form_value,
    optimal_coeffs,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_PROFILE = LeanProfile(namespace=("BD",), imports=("Mathlib",))


def _emit(fam):
    report = emit(certify(fam), _PROFILE,
                  [BaezDuarteEmitter()], ValidationReport(checks=(("bd", True),)))
    return next(iter(report.files.values()))


def _coeffs(N):
    pytest.importorskip("mpmath")
    return optimal_coeffs(N)


ALL_RUNGS = (2, 3, 4, 5, 6, 7)


def test_upper_bound_is_rigorous_tight_and_monotone():
    """Over EVERY rung: the certified bound is ≥ the closed-form Q(c) (a numerical
    cross-check of the rigorous sum), within 10⁻⁸ of it, and non-increasing in N
    (the true d²_N are, since the spans are nested)."""
    import mpmath as mp
    prev = None
    for N in ALL_RUNGS:
        cs = _coeffs(N)
        U, Nret = baez_duarte_upper_bound(cs)
        assert Nret == N
        assert 0 < U < 1
        Q = form_value(cs)
        assert mp.mpf(U.numerator) / U.denominator >= Q
        assert mp.mpf(U.numerator) / U.denominator - Q < mp.mpf("1e-8")
        if prev is not None:
            assert U < prev, f"d²_{N} bound {float(U)} not below d²_{N-1} bound {float(prev)}"
        prev = U


def test_family_is_piecewise_constant_on_harmonic_intervals():
    """Bagchi eq. (5), the identity the certified sum rests on: for x in
    (1/(n+1), 1/n], g_k(x) = {1/(kx)} − {1/x}/k equals the constant {n/k}.
    Checked exactly at interior rational points and at the endpoint x = 1/n."""
    def frac(q):
        return q - (q.numerator // q.denominator)

    for n in range(1, 60):
        pts = [Fraction(1, n)] + [Fraction(1, n + 1) + Fraction(i, 7) * (Fraction(1, n) - Fraction(1, n + 1))
                                  for i in range(1, 7)]
        for x in pts:
            for k in range(2, 13):
                assert frac(1 / (k * x)) - frac(1 / x) / k == frac(Fraction(n, k))


def test_n2_matches_bagchi_closed_form():
    """N = 2: d²_2 = 1 − ln 2 (h_n = 1 for even n, 1 − c/2 for odd n, and
    Σ_{n odd} 1/(n(n+1)) = ln 2), attained at c_2 = 2.  The certified U_2 must be
    ≥ 1 − ln 2 (rigorous Arb comparison) and close to it."""
    flint = pytest.importorskip("flint")
    cs = _coeffs(2)
    assert cs == {2: Fraction(2)}
    U, _ = baez_duarte_upper_bound(cs)
    one_minus_ln2 = 1 - flint.arb(2).log()
    gap = flint.arb(U.numerator) / U.denominator - one_minus_ln2
    assert gap > 0                       # U_2 ≥ 1 − ln 2, rigorously
    assert gap < flint.arb("1e-9")


def test_old_family_has_unconditional_floor():
    """NEGATIVE CONTROL for the pre-fix family {1/(kx)}, k ≥ 2 (no −{1/x}/k term).
    On (1/2, 1), 1/(kx) < 1 so {1/(kx)} = 1/(kx): every element of its span is
    C/x there (checked exactly at rational points), hence for every N and c
        ‖1 − Σ c_k{1/(kx)}‖²_{L²(0,1)} ≥ min_C ∫_{1/2}^1 (1 − C/x)² dx
                                      = 1/2 − (ln 2)²  ≈ 0.019547 > 0,
    so that family's d²_N cannot tend to 0 and is not an RH criterion.  The new
    family restricts to the CONSTANTS 1/k on (1/2, 1), so this obstruction is
    absent for it (its d²_N is ~0.0244 at N = 7 and ~0.0165 at N = 20, below
    the floor, per the 2026-10-14 review's float table; not certified here)."""
    flint = pytest.importorskip("flint")

    def frac(q):
        return q - (q.numerator // q.denominator)

    for x in (Fraction(1, 2) + Fraction(i, 97) for i in range(1, 49)):
        assert x < 1
        for k in range(2, 30):
            assert frac(1 / (k * x)) == 1 / (k * x)                  # old: C/x
            g = frac(1 / (k * x)) - frac(1 / x) / k                   # new: 1/k
            assert g == Fraction(1, k)
    # ∫_{1/2}^1 (1 − C/x)² dx = 1/2 − 2C ln 2 + C², minimised at C = ln 2
    ln2 = flint.arb(2).log()
    floor = flint.arb(1) / 2 - ln2 * ln2
    assert floor > flint.arb("0.019546") and floor < flint.arb("0.019548")
    for C in (Fraction(0), Fraction(7, 10), Fraction(-3, 2), Fraction(5)):
        Ca = flint.arb(C.numerator) / C.denominator
        assert flint.arb(1) / 2 - 2 * Ca * ln2 + Ca * Ca >= floor


def test_certificate_refuses_bound_below_enclosure():
    """NEGATIVE CONTROL: a U below the certified enclosure upper endpoint is not
    actually established."""
    cs = _coeffs(4)
    Uexact, _ = baez_duarte_upper_bound(cs)
    with pytest.raises(ValueError):
        baez_duarte_certificate(cs, U=Uexact - Fraction(1, 10**6))
    with pytest.raises(ValueError):
        baez_duarte_certificate(cs, U=Fraction(1, 1000))
    # a larger U (rounded up) is accepted
    cert = baez_duarte_certificate(cs, U=Uexact + Fraction(1, 1000))
    assert cert.U >= cert.Uexact


def test_certificate_refuses_degenerate():
    """NEGATIVE CONTROL: coefficients must be indexed by k ≥ 2."""
    with pytest.raises(ValueError):
        baez_duarte_certificate({1: Fraction(1, 2)})
    with pytest.raises(ValueError):
        baez_duarte_certificate({})


def test_certify_refuses_bad_family():
    fam = baez_duarte_family("Bad", GridSpec([("_", [0])]), lambda pt: "bd_bad",
                             spec=lambda pt: {"coeffs": {1: Fraction(1, 2)}, "U": None})
    with pytest.raises(Exception):
        certify(fam)


def test_emit_is_load_bearing_and_deterministic():
    cs = _coeffs(4)
    fam = baez_duarte_family("B", GridSpec([("N", [4])]),
                             lambda pt: f"bd_N{pt['N']}",
                             spec=lambda pt: {"coeffs": cs, "U": None})
    text = _emit(fam)
    assert "theorem bd_N4" in text
    # trust seam + trivial kernel step
    assert "hval" in text and "le_trans" in text and "norm_num" in text
    # ties to the Báez-Duarte / Bagchi equivalence in the provenance
    assert "d²_N → 0" in text and "{1/(kx)} − {1/x}/k" in text and "Bagchi" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert _emit(fam) == text


def test_refutation_atom_shape():
    txt = baez_duarte_refutation_atom_lean()
    assert "theorem bd_neg_refutes" in txt
    assert "¬P" in txt
    assert "hRH" in txt and "le_trans" in txt


def test_emitter_is_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "BaezDuarteEmitter" in REGISTRY
    assert "BaezDuarteEmitter" not in set(unclassified_emitters())


def test_generated_example_names_and_monotone_bounds():
    """The generated file has every rung's theorem plus one refutation atom, and
    the EMITTED readable bounds U_N are non-increasing over all rungs."""
    pytest.importorskip("mpmath")
    import re
    import importlib.util as _u
    gen_path = (Path(__file__).resolve().parents[1]
                / "examples" / "baez_duarte" / "generate.py")
    spec = _u.spec_from_file_location("baez_duarte_generate", gen_path)
    mod = _u.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert text.count("theorem bd_neg_refutes") == 1
    for N in mod.RUNGS:
        assert f"theorem bd_N{N} " in text
    caps = [Fraction(int(a), int(b)) for a, b in re.findall(
        r"theorem bd_N\d+ .*?: dN2 ≤ \(\((\d+) / (\d+)\) : ℝ\) :=", text)]
    assert len(caps) == len(mod.RUNGS)
    assert all(b < a for a, b in zip(caps, caps[1:])), [float(c) for c in caps]
