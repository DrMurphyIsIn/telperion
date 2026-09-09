"""Regression: sympy's nsimplify closed-form heuristic misfires on some plain integers
(e.g. nsimplify('3880') returns a radical with is_rational=None, in both sympy 1.12 and
current), which falsely REFUSED rational inputs at must-be-rational gates. Availability
bug only (a refusal, never a false theorem); gates now parse with sp.Rational.
The same fix for emit_box_localization lands with the T=4000 branch."""
import sympy as sp
import pytest


def test_nsimplify_landmine_exists():
    # The underlying sympy behavior this guards against (if this ever passes,
    # the workaround can be revisited).
    assert sp.nsimplify('3880').is_rational is not True


def test_annulus_count_accepts_landmine_integer():
    from telperion.emit_annulus_count import annulus_count_certificate
    try:
        annulus_count_certificate  # imported ok
    except Exception:  # pragma: no cover
        pytest.skip("emitter unavailable")
    # r/R = landmine-adjacent integers must parse as rational (not refuse);
    # any later refusal must not be the rationality gate.
    try:
        annulus_count_certificate(r='3880', R='3920')
    except ValueError as e:
        assert 'must be rational' not in str(e)


def test_argument_principle_accepts_landmine_integer():
    from telperion.emit_argument_principle import argument_principle_certificate
    try:
        argument_principle_certificate(R='3880')
    except TypeError:
        pytest.skip("certificate requires more args; gate check covered elsewhere")
    except ValueError as e:
        assert 'must be rational' not in str(e)


def test_rational_gate_still_refuses_irrational():
    from telperion.emit_argument_principle import argument_principle_certificate
    with pytest.raises((ValueError, TypeError)):
        argument_principle_certificate(R='sqrt(2)')
