"""Lehmer-pair emitter — RH Face 5 (de Bruijn–Newman / criticality).

Certifies a Lehmer pair (two consecutive zeros anomalously close): the quality
δ²·C_n < 1 from Arb-certified ordinates, emitted as a rational ``norm_num``
inequality.  The de Bruijn–Newman Λ lower bound is shipped only as a documented
WIP skeleton (the CNV constant is unverified this pass).  A finite witness, NOT RH.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    LehmerPairEmitter,
    ValidationReport,
    certify,
    emit,
    lehmer_pair_certificate,
    lehmer_pair_family,
)
from telperion.emit_lehmer_pair import (  # noqa: E402
    LEHMER_QUALITY_CAP,
    find_closest_pair,
    lehmer_lambda_bound_wip_lean,
    lehmer_pair_quality,
    lehmer_refutation_atom_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_PROFILE = LeanProfile(namespace=("LP",), imports=("Mathlib",))


def _emit(fam):
    report = emit(certify(fam), _PROFILE,
                  [LehmerPairEmitter()], ValidationReport(checks=(("lp", True),)))
    return next(iter(report.files.values()))


def _need_platt():
    """Skip (not error) where libflint lacks the Platt machinery: `flint` can
    import while `acb_dirichlet_platt_*` is absent from the bundled library."""
    from telperion.arb_platt import PLATT_AVAILABLE
    if not PLATT_AVAILABLE:
        pytest.skip("libflint with Platt machinery not found")


def _close_pair():
    _need_platt()
    n, ratio = find_closest_pair(1, 500)
    return n, ratio


def test_close_pair_is_a_lehmer_pair():
    n, ratio = _close_pair()
    assert ratio < 1.0  # closer than the mean spacing
    quality, gap, info = lehmer_pair_quality(n)
    assert 0 < quality < LEHMER_QUALITY_CAP
    assert info["gap"] < info["mean_spacing"]


def test_certificate_refuses_non_lehmer_pair():
    """NEGATIVE CONTROL: a wide (typical) pair with quality ≥ 1 is not a Lehmer pair."""
    _need_platt()
    wide_n = None
    for n in range(2, 200):
        q, _, _ = lehmer_pair_quality(n)
        if q >= LEHMER_QUALITY_CAP:
            wide_n = n
            break
    assert wide_n is not None, "expected a non-Lehmer pair in n<200"
    with pytest.raises(ValueError):
        lehmer_pair_certificate(wide_n)


def test_certificate_refuses_bad_qcap():
    """NEGATIVE CONTROLS: qcap below the (rounded) quality, or ≥ the Lehmer threshold."""
    n, _ = _close_pair()
    cert = lehmer_pair_certificate(n)
    with pytest.raises(ValueError):
        lehmer_pair_certificate(n, qcap=cert.quality_short - Fraction(1, 10**6))
    with pytest.raises(ValueError):
        lehmer_pair_certificate(n, qcap=Fraction(2))  # ≥ threshold 1
    # a valid qcap in (quality_short, 1) is accepted
    ok = lehmer_pair_certificate(n, qcap=(cert.quality_short + Fraction(1, 100)))
    assert ok.qcap > ok.quality_short < LEHMER_QUALITY_CAP


def test_emit_is_substantive_and_deterministic():
    n, _ = _close_pair()
    fam = lehmer_pair_family("L", GridSpec([("n", [n])]),
                             lambda pt: f"lehmer_n{pt['n']}",
                             spec=lambda pt: {"n_index": pt["n"]})
    text = _emit(fam)
    assert f"theorem lehmer_n{n}" in text
    assert "norm_num" in text
    # substantive (not reflexive x ≤ x)
    cert = lehmer_pair_certificate(n)
    assert cert.qcap > cert.quality_short
    # ties to Face 5 in the provenance
    assert "de Bruijn" in text or "Λ ≤ 0" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert _emit(fam) == text


def test_wip_and_refutation_atoms():
    wip = lehmer_lambda_bound_wip_lean()
    assert "theorem lehmer_lambda_bound_wip" in wip
    assert "hCNV" in wip and "le_trans" in wip
    assert "WIP" in wip and "UNVERIFIED" in wip
    ref = lehmer_refutation_atom_lean()
    assert "theorem lehmer_neg_refutes" in ref
    assert "¬P" in ref


def test_emitter_is_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "LehmerPairEmitter" in REGISTRY
    assert "LehmerPairEmitter" not in set(unclassified_emitters())


def test_generated_example_builds():
    _need_platt()
    import importlib.util as _u
    gen_path = (Path(__file__).resolve().parents[1]
                / "examples" / "lehmer_pair" / "generate.py")
    spec = _u.spec_from_file_location("lehmer_pair_generate", gen_path)
    mod = _u.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert text.count("theorem lehmer_lambda_bound_wip") == 1
    assert text.count("theorem lehmer_neg_refutes") == 1
    assert text.count("theorem lehmer_n") >= 1
