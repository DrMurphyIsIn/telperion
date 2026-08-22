"""The primality emitter: Pratt witness -> a lucas_primality-discharged theorem."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

from telperion.emit_primality import primality_module, primality_theorem  # noqa: E402


def test_emits_a_lucas_primality_theorem_for_a_prime():
    lean = primality_theorem(1009)

    assert "theorem isPrime_1009 : Nat.Prime 1009" in lean
    assert "lucas_primality 1009 (11 : ZMod 1009)" in lean   # the found witness
    assert "Nat.divisors (1009 - 1)" in lean
    assert "fin_cases hmem <;> revert hq <;> decide" in lean


def test_refuses_a_composite():
    with pytest.raises(ValueError):
        primality_theorem(1001)          # 7 * 11 * 13


def test_module_wraps_each_prime_in_a_namespace():
    lean = primality_module([5, 23], namespace="Primality")

    assert "import Mathlib" in lean
    assert "namespace Primality" in lean and "end Primality" in lean
    assert "isPrime_5" in lean and "isPrime_23" in lean
