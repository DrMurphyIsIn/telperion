"""twofreq_offline emitter -- certified OFF-line displacement of a two-frequency section.

The exact complement of `selfinversive_rigidity`: there, |c1|^2 = |c2|^2 EXACTLY forces
real-rootedness; here, |c1|^2 != |c2|^2 EXACTLY REFUTES it (every zero sits off the real
line).  The two emitters partition the coefficient space and neither can emit a false
theorem: each REFUSES precisely the other's regime.

conjecture1_proved = False -- a finite section fact about one Euler factor; nothing about
zeta or RH.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

from telperion import (  # noqa: E402
    TwoFreqOfflineEmitter, ValidationReport, certify, emit,
)
from telperion.emit_twofreq_offline import (  # noqa: E402
    gauss, inv_sqrt, neglog, rat, real_sqrt,
    twofreq_offline_certificate, twofreq_offline_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_NODE = (Path(__file__).resolve().parents[1] / "missions" / "mirrormere" / "lean"
         / "Statements" / "MM_euler_factor_section_offline.lean")


def _euler_spec(p, mode="displacement"):
    return {"c1": gauss(1, 0), "c2": inv_sqrt(p, sign=-1),
            "lam1": rat(0), "lam2": neglog(p), "p": p, "mode": mode}


def _emit_one(spec, name="tfo_demo"):
    fam = twofreq_offline_family("TFO", GridSpec([("_", [0])]), lambda pt: name,
                                 spec=lambda pt: spec)
    report = emit(certify(fam),
                  LeanProfile(namespace=("TFO",), imports=("Mathlib", "TwoFreqRigidity"),
                              prelude="open Quasicrystal\n"),
                  [TwoFreqOfflineEmitter()],
                  ValidationReport(checks=(("twofreq_offline", True),)))
    return next(iter(report.files.values()))


# --------------------------------------------------------------------------- positive

def test_positive_cert_p2_normsq():
    cert = twofreq_offline_certificate(**_euler_spec(2))
    assert cert.normsq1 == 1
    assert cert.normsq2 == pytest.approx(0.5)
    assert cert.normsq1 != cert.normsq2
    assert cert.p == 2
    assert cert.displacement == pytest.approx(0.5)
    assert cert.mode == "displacement"


def test_positive_cert_gauss_and_real_sqrt():
    # Gaussian-rational vs real: |c1|^2 = 1, |c2|^2 = 4.
    c = twofreq_offline_certificate(c1=gauss("3/5", "4/5"), c2=gauss(2, 0),
                                    lam1=rat(1), lam2=rat(2))
    assert (c.normsq1, c.normsq2) == (1, 4)
    # q * sqrt s: |c1|^2 = (3/2)^2 * 3 = 27/4.
    c2 = twofreq_offline_certificate(c1=real_sqrt("-3/2", 3), c2=gauss(1, 0),
                                     lam1=rat(0), lam2=rat(7))
    assert c2.normsq1 == pytest.approx(27 / 4) and c2.normsq2 == 1


# --------------------------------------------------------------------------- refusals

def test_refuses_equal_modulus():
    # THE anti-phantom refusal: equal modulus means the sum IS real-rooted, so the
    # emitted negation would be FALSE.  Exact complement of selfinversive_rigidity.
    with pytest.raises(ValueError, match="equal modulus"):
        twofreq_offline_certificate(c1=gauss("3/5", "4/5"), c2=gauss(1, 0),
                                    lam1=rat(1), lam2=rat(2))


def test_refuses_zero_coefficient():
    with pytest.raises(ValueError, match="nonzero"):
        twofreq_offline_certificate(c1=gauss(0, 0), c2=gauss(1, 0),
                                    lam1=rat(1), lam2=rat(2))


def test_refuses_equal_frequencies():
    with pytest.raises(ValueError, match="differ"):
        twofreq_offline_certificate(c1=gauss(1, 0), c2=gauss(2, 0),
                                    lam1=rat(3), lam2=rat(3))
    # log 1 = 0, so ('neglog', 1) IS ('rat', 0) -- the disguised degeneracy.
    with pytest.raises(ValueError):
        twofreq_offline_certificate(c1=gauss(1, 0), c2=gauss(2, 0),
                                    lam1=rat(0), lam2=neglog(1))


def test_refuses_nonpositive_radicand():
    with pytest.raises(ValueError):
        twofreq_offline_certificate(c1=real_sqrt(1, -3), c2=gauss(1, 0),
                                    lam1=rat(0), lam2=rat(1))


def test_refuses_displacement_mode_outside_p_family():
    # Honest scope: the certified displacement 1/2 is a fact about 1 - p^(-1/2) e^(-i log p x)
    # ONLY.  Any other shape is refused rather than guessed at.
    with pytest.raises(ValueError, match="displacement"):
        twofreq_offline_certificate(c1=gauss("3/5", "4/5"), c2=gauss(2, 0),
                                    lam1=rat(1), lam2=rat(2), mode="displacement")


def test_refuses_p_below_two():
    with pytest.raises(ValueError):
        twofreq_offline_certificate(**_euler_spec(1))


def test_refuses_negative_rational_frequency_against_a_log():
    # The emitted separation 0 <= r < log p needs the rational side nonnegative.
    with pytest.raises(ValueError, match="nonnegative"):
        twofreq_offline_certificate(c1=gauss(1, 0), c2=gauss(2, 0),
                                    lam1=rat("-5"), lam2=neglog(3))


# --------------------------------------------------------------------------- emission

def test_statement_matches_mm_node():
    """The p = 2 theorem must be byte-identical (modulo the missions normalizer) to the
    registry's MM_euler_factor_section_offline statement."""
    from telperion.missions.verify import normalize_lean

    text = _emit_one(_euler_spec(2), name="euler_factor_section_offline")
    node_body = "\n".join(
        ln for ln in _NODE.read_text(encoding="utf-8").splitlines()[1:]
        if not ln.strip().startswith(("import ", "open ")))
    assert normalize_lean(node_body) in normalize_lean(text)


def test_emit_is_lint_clean_and_deterministic():
    text = _emit_one(_euler_spec(2))
    again = _emit_one(_euler_spec(2))
    assert text == again
    assert "twoFreq_realRooted_iff" in text
    assert "conjecture1_proved = False" in text
    assert "sorry" not in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_displacement_and_existence_theorems_are_emitted():
    text = _emit_one(_euler_spec(3), name="tfo_p3")
    assert "theorem tfo_p3 :" in text
    assert "theorem tfo_p3_offline_zero :" in text
    assert "theorem tfo_p3_displacement :" in text
    assert "x.im = 1 / 2" in text
    # 'offline' mode drops the displacement theorem but keeps the existence corollary.
    plain = _emit_one({**_euler_spec(3), "mode": "offline"}, name="tfo_p3")
    assert "theorem tfo_p3_displacement :" not in plain
    assert "theorem tfo_p3_offline_zero :" in plain


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY
    assert "TwoFreqOfflineEmitter" in REGISTRY
    stance = REGISTRY["TwoFreqOfflineEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
