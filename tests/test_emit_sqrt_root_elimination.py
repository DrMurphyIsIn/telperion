"""SqrtRootElimination emitter (NS ConeAlgebra true_cone_iff shape): certify →
emit → lint, with the NS cone instance as positive control and a corrupted-Q
refusal as the certificate-sensitivity negative control."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    sqrt_root_elim_certificate,
    sqrt_root_elimination_family,
)
from telperion.emit_sqrt_root_elimination import SqrtRootEliminationEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text

P, J, v = sp.symbols("P J v", real=True)

# The NS cone instance (ConeAlgebra.lean): E = P + J²/4, u = J, rad = (P−2)/2 + J²/16.
_E = P + J ** 2 / 4
_U = J
_RAD = (P - 2) / 2 + J ** 2 / 16
_Q = sp.expand((_E - v) ** 2 - _U ** 2 * _RAD)


def _family(Q=None):
    return sqrt_root_elimination_family(
        name="ConeElim",
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "true_cone_elim",
        spec=lambda pt: ((P, J, v), v, _E, _U, _RAD, _Q if Q is None else Q),
    )


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("NS", "SqrtElim")),
        [SqrtRootEliminationEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_kind():
    assert _family().kind == "sqrt_root_elimination"


def test_certifies_ns_cone_instance():
    cert = certify(_family()).instances[0].payload
    assert sp.simplify((cert.E - cert.v) ** 2 - cert.u ** 2 * cert.rad - cert.Q) == 0


def test_emits_prelude_and_specialization():
    text = _emit(_family()).files["ConeElim.lean"]
    assert "theorem sqrt_shift_lt_iff" in text
    assert "theorem sqrt_amplitude_transfer" in text
    assert "theorem true_cone_elim" in text
    assert "Real.sqrt" in text
    assert "by ring" in text  # the load-bearing identity
    assert "github.com/openai/NavierStokesAndEuler" in text  # attribution


def test_honesty_seam_side_conditions_are_hypotheses():
    text = _emit(_family()).files["ConeElim.lean"]
    assert "(hu : 0 ≤" in text
    assert "(hrad : 0 ≤" in text
    assert "HYPOTHESES" in text


def test_lean_text_clean():
    check_lean_text(_emit(_family()).files["ConeElim.lean"])


def test_byte_stability():
    assert _emit(_family()).files["ConeElim.lean"] == _emit(_family()).files["ConeElim.lean"]


def test_negative_control_corrupted_Q_refused():
    with pytest.raises(ValueError, match="corrupted Q"):
        sqrt_root_elim_certificate((P, J, v), v, _E, _U, _RAD, _Q + 1)


def test_negative_control_v_not_in_variables():
    with pytest.raises(ValueError, match="v must be one of"):
        sqrt_root_elim_certificate((P, J), v, _E, _U, _RAD, _Q)


def test_simple_instance_certifies():
    # E = x, u = 1, rad = x: v < x - sqrt(x) <-> (v < x and 0 < (x-v)^2 - x)
    x, w = sp.symbols("x w", real=True)
    Q = sp.expand((x - w) ** 2 - x)
    cert = sqrt_root_elim_certificate((x, w), w, x, sp.Integer(1), x, Q)
    assert cert.Q == Q
