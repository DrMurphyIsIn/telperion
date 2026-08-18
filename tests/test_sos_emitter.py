"""First-class SOS/SDP emitter: pipeline flow, honesty pins, byte-stability.

The Lean kernel is the arbiter (CI `lake build`); these are the pre-CI
self-checks — exact rational SOS verification, the tight-variety honesty pin,
and the two negative controls (non-SOS refusal, overclaim refusal)."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

# The SDP certifier needs cvxpy (the `sdp` extra); the cvxpy-free CI test job
# skips this file — the frozen SOSSDP.lean is compile-gated in production instead.
pytest.importorskip("cvxpy")

from telperion import (  # noqa: E402
    CertificationError,
    GridSpec,
    LeanProfile,
    SOSEmitter,
    ValidationReport,
    certify,
    emit,
    sos_family,
)

x, y = sp.symbols("x y")


def _pencil(a: int) -> sp.Expr:
    return sp.expand((x - a) ** 2 + (y - 1) ** 2 + (x - y - (a - 1)) ** 2)


def _family(ties=None):
    return sos_family(
        name="SOSTest",
        symbols=(x, y),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"sos_a{pt['a']}",
        target=lambda pt: _pencil(pt["a"]),
        half_deg=1,
        ties=ties if ties is not None else (lambda pt: [{x: pt["a"], y: 1}]),
    )


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("G1", "SOSTest")),
                [SOSEmitter()], ValidationReport(checks=(("spot", True),)))


def test_kind_is_sos():
    assert _family().kind == "sos"


def test_certify_emit_produces_positivity_theorems():
    res = _emit(_family())
    assert res.n_theorems == 3
    text = res.files["SOSTest.lean"]
    # one theorem per instance, in the proven SOS shape
    assert text.count("theorem sos_a") == 3
    assert text.count("rw [hsos]; positivity") == 3
    assert "have hsos" in text
    # tight variety (SDP dual) documented, not the trivial "strictly positive"
    assert "Tight variety" in text


def test_exact_sos_identity_holds():
    # every emitted `have hsos : p = Σ dᵢℓᵢ² := by ring` is an exact identity
    fam = _family()
    cf = certify(fam)
    for inst in cf.instances:
        p = sp.expand(fam.target(inst.point))
        assert sp.expand(inst.sos.as_expr() - p) == 0
        # complementary slackness: declared tie is a common zero of the bases
        tie = {x: inst.point["a"], y: 1}
        for _, base in inst.sos.terms:
            assert sp.expand(base.subs(tie)) == 0


def test_byte_stability():
    a = _emit(_family()).files["SOSTest.lean"]
    b = _emit(_family()).files["SOSTest.lean"]
    assert a == b


def test_negative_control_A_non_sos_refused():
    # x*y is indefinite (no PSD Gram) -> certification must refuse
    bad = sos_family(
        name="Bad", symbols=(x, y), grid=GridSpec([("a", [0])]),
        lean_name=lambda pt: "bad", target=lambda pt: x * y, half_deg=1,
    )
    with pytest.raises(CertificationError):
        certify(bad)


def test_negative_control_B_overclaim_refused():
    # a valid SOS family but a declared tie the certificate cannot achieve
    over = _family(ties=lambda pt: [{x: 0, y: 0}])  # p(0,0) = 2 != 0
    with pytest.raises(CertificationError):
        certify(over)
