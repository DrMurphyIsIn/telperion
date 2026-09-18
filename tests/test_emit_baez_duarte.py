"""Báez-Duarte emitter — RH Face 6 (spectral / approximation).

Certifies a rung of the Nyman–Beurling–Báez-Duarte criterion (RH ⟺ d²_N → 0):
a rigorous rational UPPER bound on d²_N from an explicit coefficient vector whose
L²(0,1) quadratic-form value Q(c) ≥ d²_N is Arb-enclosed.  A finite rung, NOT RH.
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
    pytest.importorskip("flint")
    pytest.importorskip("mpmath")
    return optimal_coeffs(N)


def test_upper_bound_is_rigorous_and_decreasing():
    """The certified upper bounds on d²_N should shrink as N grows (the RH-consistent
    trend), and each must be a valid Q(c) ≥ d²_N enclosure endpoint."""
    pytest.importorskip("flint")
    prev = None
    for N in (2, 3, 4, 5):
        cs = optimal_coeffs(N)
        U, Nret = baez_duarte_upper_bound(cs)
        assert Nret == N
        assert 0 < U < 1
        if prev is not None:
            assert U < prev, f"d²_{N} bound {float(U)} not below d²_{N-1} bound {float(prev)}"
        prev = U


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
    # ties to the Báez-Duarte equivalence in the provenance
    assert "d²_N → 0" in text or "d²_N" in text
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


def test_generated_example_decreasing_sequence():
    pytest.importorskip("flint")
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
