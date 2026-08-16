"""Property/fuzz tests: the certifier and serializer under random inputs.

Seeded stdlib randomness (no hypothesis dependency — audit surface).  Three
properties:

1. SOUND-BY-CONSTRUCTION ACCEPTANCE: expressions built from positive atoms
   (sums/products/quotients of positive-coefficient polynomials) must certify.
2. NO FALSE ACCEPTANCE: expressions with a planted rational counterexample
   must be refused by certification (a certificate for a false claim would be
   caught by Lean anyway — but the earlier gate must hold too).
3. DETERMINISM: rendering is byte-identical across repeated runs and stable
   under re-parsing (sympy expression identity does not depend on build
   order of the expression tree).
"""
import random
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import polya_certify  # noqa: E402
from telperion.diagnose import find_counterexample  # noqa: E402
from telperion.expr import expr_lean_factored  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
SYMS = (u, v)


def _pos_poly(rng: random.Random, degree: int = 2) -> sp.Expr:
    """Random polynomial with all-POSITIVE integer coefficients."""
    terms = [sp.Integer(rng.randint(1, 9))]
    for _ in range(rng.randint(1, 4)):
        e1, e2 = rng.randint(0, degree), rng.randint(0, degree)
        terms.append(rng.randint(1, 9) * u**e1 * v**e2)
    return sp.Add(*terms)


def _pos_rational(rng: random.Random, depth: int = 2) -> sp.Expr:
    """Random positive rational function: sums/products/quotients of positive
    polynomials — nonneg on the domain by construction."""
    if depth == 0:
        return _pos_poly(rng)
    op = rng.randrange(3)
    a, b = _pos_rational(rng, depth - 1), _pos_rational(rng, depth - 1)
    if op == 0:
        return a + b
    if op == 1:
        return a * b
    return a / b


def test_positive_constructions_always_certify():
    rng = random.Random(2026)
    for i in range(40):
        e = _pos_rational(rng)
        cert = polya_certify(e, SYMS)  # must not raise
        assert sp.Poly(cert.numerator, *SYMS).coeffs()  # nonempty
        # and the certificate is faithful: num/den == e
        assert sp.simplify(cert.numerator / cert.denominator - e) == 0


def test_planted_counterexamples_are_refused():
    rng = random.Random(4051)
    refused = 0
    for i in range(25):
        # e = pos - (pos + margin) at a planted point: strictly negative there
        base = _pos_rational(rng, 1)
        pu, pv = sp.Rational(rng.randint(0, 8), 4), sp.Rational(rng.randint(0, 8), 4)
        val = base.subs({u: pu, v: pv})
        e = base - val - sp.Rational(1, 3)
        with pytest.raises(ValueError):
            polya_certify(e, SYMS)
        refused += 1
        # and diagnose can prove falsity with an exact witness
        wit = find_counterexample(e, SYMS, trials=300, seed=i)
        if wit is not None:
            assert e.subs({u: wit["u"], v: wit["v"]}) < 0
    assert refused == 25


def test_rendering_deterministic_and_order_independent():
    rng = random.Random(77)
    for _ in range(20):
        e = _pos_rational(rng)
        s1 = expr_lean_factored(e, SYMS)
        s2 = expr_lean_factored(sp.sympify(sp.srepr(e)), SYMS)  # rebuilt tree
        s3 = expr_lean_factored(sp.expand(e) if e.is_polynomial(*SYMS) else e, SYMS)
        assert s1 == s2
        assert s1 == s3
        assert "«" not in s1 and "**" not in s1
