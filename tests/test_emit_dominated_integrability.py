"""emit_dominated_integrability: integrable-by-rpow-domination.

The convergence condition 1 < Re p is an EXACT gate; a divergent instance (Re p <= 1) is refused.
"""
import sys
from pathlib import Path
from fractions import Fraction
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.emit_dominated_integrability import (  # noqa: E402
    DominatedIntegrand, verify_convergence, emit_instance_lean, emit_integrability_lemma)


def test_convergent_instance_verifies_and_emits():
    inst = DominatedIntegrand(Fraction(2), Fraction(1), Fraction(1), "s + 1")
    assert verify_convergence(inst)
    assert "IntegrableOn" in emit_instance_lean(inst, "integrableOn_fractIntegrand_Ioi")


def test_reusable_shape_lemma_present():
    assert "integrableOn_bounded_div_cpow" in emit_integrability_lemma()


def test_divergent_instance_refused():
    div = DominatedIntegrand(Fraction(1), Fraction(1), Fraction(1), "s + 1")   # Re p = 1: ∫x^{-1} = ∞
    assert not verify_convergence(div)
    try:
        emit_instance_lean(div, "forged"); assert False
    except ValueError:
        pass


def test_nonpositive_ray_refused():
    assert not verify_convergence(DominatedIntegrand(Fraction(2), Fraction(0), Fraction(1), "s + 1"))
