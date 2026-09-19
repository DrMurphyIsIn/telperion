"""ExpLaurentIdentity emitter (MIRRORMERE W3d): certify -> emit -> lint + refusals.

The shape: identities in ``e^d`` and ``e^(-d)`` certified as an exact reduction of
``lhs - rhs`` modulo the single relation ``e^d * e^(-d) = 1``, with the quotient
(cofactor) carried into the emitted ``linear_combination``.

The load-bearing refusal is the mistake QC_RECURRENCE section 6 caught in itself:
the SUM of the two off-line clearances is NOT the amplification excess -- only
their PRODUCT is.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_exp_laurent_identity import (  # noqa: E402
    RELATION,
    Y,
    Z,
    ExpLaurentIdentityEmitter,
    exp_laurent_certificate,
    exp_laurent_identity_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_G_PLUS = Y - 1
_G_MINUS = 1 - Z
_EXCESS = Y + Z - 2


def test_recurrence_deficit_row_cofactor_is_minus_one():
    """(e^d - 1)(1 - e^(-d)) = e^d + e^(-d) - 2 with the exact cofactor -1."""
    cert = exp_laurent_certificate(_G_PLUS * _G_MINUS, _EXCESS, name="row")
    assert cert.cofactor == -1
    # the certificate re-multiplies exactly: lhs - rhs = cofactor * (y*z - 1)
    assert sp.expand(cert.cofactor * RELATION - (cert.lhs - cert.rhs)) == 0


def test_squared_row_cofactor_is_exact():
    """The Weil-energy square is certified too, with a nontrivial cofactor."""
    cert = exp_laurent_certificate((_G_PLUS * _G_MINUS) ** 2, _EXCESS ** 2,
                                   name="row_sq")
    assert cert.cofactor != 0
    assert sp.expand(cert.cofactor * RELATION - (cert.lhs - cert.rhs)) == 0


def test_refuses_the_sum_of_the_clearances():
    """NEGATIVE CONTROL -- the memo's own corrected mistake.

    `(e^d - 1) + (1 - e^(-d))` is `2d + O(d^3)`, not the excess; the reduction
    leaves the residue `2 - 2*e^(-d)`, so the certifier must refuse.
    """
    with pytest.raises(ValueError) as exc:
        exp_laurent_certificate(_G_PLUS + _G_MINUS, _EXCESS, name="sum")
    assert "does not reduce to 0" in str(exc.value)


def test_refuses_a_plain_ring_identity():
    """A claim that never uses the relation has cofactor 0 and is refused: the
    certificate would carry no information (that shape is IdentityEmitter's)."""
    with pytest.raises(ValueError) as exc:
        exp_laurent_certificate((Y - 1) * (Y + 1), Y ** 2 - 1, name="ring")
    assert "NOT load-bearing" in str(exc.value)


def test_refuses_symbols_outside_the_exp_generators():
    with pytest.raises(ValueError) as exc:
        exp_laurent_certificate(Y * sp.Symbol("q"), Y, name="alien")
    assert "outside the exp generators" in str(exc.value)


def test_refuses_a_non_polynomial_side():
    with pytest.raises(ValueError) as exc:
        exp_laurent_certificate(Y / (Z - 1), Y, name="nonpoly")
    assert "not a polynomial" in str(exc.value)


def _emit_rows(rows):
    fam = exp_laurent_identity_family(
        "TestExpLaurent",
        GridSpec([("row", range(len(rows)))]),
        lambda pt: rows[pt["row"]][0],
        spec=lambda pt: (rows[pt["row"]][1], rows[pt["row"]][2], "d"),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("TestExpLaurent",)),
        [ExpLaurentIdentityEmitter()],
        ValidationReport(checks=(("exp_laurent_identity", True),)),
    )
    return next(iter(report.files.values()))


def test_emitted_lean_is_structure_preserving_and_sorry_free():
    """The STATEMENT must read as the mathematics was written (Lean `*` is not
    definitionally commutative, so the emitted order is fixed and deterministic),
    and the certified cofactor must appear in the proof."""
    text = _emit_rows((("row", _G_PLUS * _G_MINUS, _EXCESS),))
    assert ("theorem row (d : ℝ) :\n"
            "    (Real.exp d - 1) * (1 - Real.exp (-d)) = "
            "Real.exp d + Real.exp (-d) - 2") in text
    assert "have hrel : Real.exp d * Real.exp (-d) = 1" in text
    assert "linear_combination (-1 : ℝ) * hrel" in text
    assert "sorry" not in text


def test_emission_is_deterministic():
    rows = (("row", _G_PLUS * _G_MINUS, _EXCESS),
            ("row_sq", (_G_PLUS * _G_MINUS) ** 2, _EXCESS ** 2))
    assert _emit_rows(rows) == _emit_rows(rows)


def test_adapter_is_registered_for_the_generic_negative_control():
    """The kernel-gated two-sided control is wired (it RUNS in
    tests/test_certificate_sensitivity.py::test_generic_negative_control_holds)."""
    from telperion.negative_control_harness import registered_adapters

    import telperion.negctrl_adapters  # noqa: F401  (registers every adapter)

    adapters = registered_adapters()
    assert "ExpLaurentIdentityEmitter" in adapters
    adapter = adapters["ExpLaurentIdentityEmitter"]
    # the forged twin really is the sum-for-product substitution
    assert sp.expand(adapter.make_false_cert().lhs
                     - (_G_PLUS + _G_MINUS)) == 0
    assert sp.expand(adapter.make_true_cert().lhs
                     - _G_PLUS * _G_MINUS) == 0
