"""FinitePrefixAbsorption emitter: certify → emit → lint (single fixed atom)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    finite_prefix_absorption_family,
)
from telperion.emit_finite_prefix_absorption import (  # noqa: E402
    FinitePrefixAbsorptionEmitter,
)
from telperion.lean_lint import check_lean_text


def _family():
    return finite_prefix_absorption_family(
        name="PrefixChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "prefix_absorb")


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "Prefix")),
                [FinitePrefixAbsorptionEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family().kind == "finite_prefix_absorption"


def test_emits_atom_with_witness():
    res = _emit(_family())
    text = res.files["PrefixChk.lean"]
    assert "theorem finite_prefix_absorption" in text
    assert "Finset.single_le_sum" in text  # the explicit prefix witness
    assert "HYPOTHESIS" in text
    assert "github.com/openai/NavierStokesAndEuler" in text
    assert res.n_theorems == 1


def test_lean_text_clean():
    check_lean_text(_emit(_family()).files["PrefixChk.lean"])


def test_byte_stability():
    assert _emit(_family()).files["PrefixChk.lean"] == _emit(_family()).files["PrefixChk.lean"]
