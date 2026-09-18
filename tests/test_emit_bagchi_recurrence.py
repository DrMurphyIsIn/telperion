"""Bagchi-recurrence emitter — RH Face 4 (recurrence).

Certifies a finite recurrence observation (Bagchi 1981: RH ⟺ ζ strongly recurrent
in the strip): sup over a rational grid of |ζ(s+iτ) − ζ(s)| ≤ ε, each per-point
deviation an Arb acb_zeta upper bound.  A finite observation, NOT RH.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BagchiRecurrenceEmitter,
    ValidationReport,
    bagchi_recurrence_certificate,
    bagchi_recurrence_family,
    certify,
    emit,
)
from telperion.emit_bagchi_recurrence import (  # noqa: E402
    bagchi_grid_max,
    bagchi_refutation_atom_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_PROFILE = LeanProfile(namespace=("BR",), imports=("Mathlib",))
_SIGMAS = [Fraction(3, 5), Fraction(13, 20), Fraction(7, 10)]
_TS = [Fraction(10), Fraction(11), Fraction(12)]


def _emit(fam):
    report = emit(certify(fam), _PROFILE,
                  [BagchiRecurrenceEmitter()], ValidationReport(checks=(("br", True),)))
    return next(iter(report.files.values()))


def test_grid_max_is_rigorous_upper_bound():
    """The certified grid-max M is a positive rational; each acb_zeta bound folds in."""
    pytest.importorskip("flint")
    M, pts = bagchi_grid_max(3, _SIGMAS, _TS)
    assert M > 0
    assert len(pts) == len(_SIGMAS) * len(_TS)
    assert all(u <= M for _s, _t, u in pts)


def test_certificate_refuses_eps_below_gridmax():
    """NEGATIVE CONTROL: an ε below the certified grid-max makes M ≤ ε false."""
    pytest.importorskip("flint")
    M, _ = bagchi_grid_max(3, _SIGMAS, _TS)
    with pytest.raises(ValueError):
        bagchi_recurrence_certificate(3, _SIGMAS, _TS, eps=M / 2)
    # ε ≥ M accepted
    cert = bagchi_recurrence_certificate(3, _SIGMAS, _TS, eps=M + Fraction(1, 100))
    assert cert.eps >= cert.M


def test_certificate_refuses_empty_grid():
    pytest.importorskip("flint")
    with pytest.raises(ValueError):
        bagchi_recurrence_certificate(3, [], _TS)
    with pytest.raises(ValueError):
        bagchi_recurrence_certificate(3, _SIGMAS, [])


def test_certify_refuses_bad_family():
    fam = bagchi_recurrence_family("Bad", GridSpec([("_", [0])]), lambda pt: "br_bad",
                                   spec=lambda pt: {"tau": 3, "sigmas": [], "ts": _TS})
    with pytest.raises(Exception):
        certify(fam)


def test_emit_is_load_bearing_and_deterministic():
    pytest.importorskip("flint")
    M, _ = bagchi_grid_max(3, _SIGMAS, _TS)
    eps = M + Fraction(1, 100)
    fam = bagchi_recurrence_family("B", GridSpec([("tau", [3])]),
                                   lambda pt: f"bagchi_tau{pt['tau']}",
                                   spec=lambda pt: {"tau": pt["tau"], "sigmas": _SIGMAS,
                                                    "ts": _TS, "eps": eps})
    text = _emit(fam)
    assert "theorem bagchi_tau3" in text
    assert "hdev" in text and "le_trans" in text and "norm_num" in text
    # ties to Face 4 / honest scope
    assert "Bagchi" in text and "GRID" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert _emit(fam) == text


def test_refutation_atom_shape():
    txt = bagchi_refutation_atom_lean()
    assert "theorem bagchi_recurrence_refutes" in txt
    assert "¬P" in txt
    assert "hRH" in txt and "le_trans" in txt


def test_emitter_is_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "BagchiRecurrenceEmitter" in REGISTRY
    assert "BagchiRecurrenceEmitter" not in set(unclassified_emitters())


def test_generated_example_builds():
    pytest.importorskip("flint")
    import importlib.util as _u
    gen_path = (Path(__file__).resolve().parents[1]
                / "examples" / "bagchi_recurrence" / "generate.py")
    spec = _u.spec_from_file_location("bagchi_recurrence_generate", gen_path)
    mod = _u.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert text.count("theorem bagchi_recurrence_refutes") == 1
    assert text.count("theorem bagchi_tau") >= 1
