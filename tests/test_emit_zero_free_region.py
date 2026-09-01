"""emit_zero_free_region: the zero-free-region assembly emitter.

From the three elementary bounds (pole c1, growth c2, Cauchy c4) + the 3-4-1 positivity, the region
rate 1 - c/|t|^{5θ} is DERIVED; the region constant 16 c1^3 c2 c4^4 is re-derived exactly by symbolic
expansion (anti-phantom) before any Lean is emitted.
"""
import sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.emit_zero_free_region import (  # noqa: E402
    ZeroFreeRegionCert, verify_region, emit_zero_free_region_lean)


def test_actual_instance_constant_and_exponent():
    ok, const, expo = verify_region(ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24)))
    assert ok and const == 212336640 and expo == 5   # 16*8*5*24^4 = 212336640


def test_sharper_growth_power_improves_exponent():
    # theta < 1 (a sharper growth bound) lowers the exponent 5*theta -> better region.
    _, _, e_half = verify_region(ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24), sp.Rational(1, 2)))
    assert e_half == sp.Rational(5, 2)


def test_emitted_lean_has_verified_constant():
    lean = emit_zero_free_region_lean(ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24)),
                                      "zeta_zero_free_poly_emitted")
    assert "212336640" in lean and "nlinarith [h1]" in lean and "field_simp; ring" in lean


def test_nonpositive_coefficient_refused():
    for bad in [ZeroFreeRegionCert(sp.Integer(0), sp.Integer(5), sp.Integer(24)),
                ZeroFreeRegionCert(sp.Integer(2), sp.Integer(-1), sp.Integer(24))]:
        assert not verify_region(bad)[0]
        try:
            emit_zero_free_region_lean(bad, "forged"); assert False
        except ValueError:
            pass
