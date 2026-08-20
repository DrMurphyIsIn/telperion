"""Real-Nullstellensatz certificate FINDER — checker → searcher.

`find_real_nullstellensatz_certificate` searches for `(m, s)` with
`p^{2m} + s ∈ ⟨gens⟩` and `s` an exact sum of squares (via `sos_decompose`,
sympy-only — no SDP).  The finder is untrusted: the certifier re-reduces and
re-checks everything, so a miss is a refusal, never a wrong theorem.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, RealNullstellensatzEmitter,
    ValidationReport, certify, check_lean_text, emit,
    find_real_nullstellensatz_certificate, real_nullstellensatz_family,
)

GREEN = ValidationReport(checks=(("spot", True),))
x, y = sp.symbols("x y")


def test_finder_flagship_case():
    # x vanishes on the real variety of x^2 + y^2 (just the origin):
    # x^2 + y^2 in the ideal, so m=1, s=y^2.
    found = find_real_nullstellensatz_certificate(x, [x ** 2 + y ** 2], (x, y))
    assert found is not None
    m, terms = found
    assert m == 1
    s = sum(sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in terms)
    _, rem = sp.reduced(sp.expand(x ** (2 * m) + s), [x ** 2 + y ** 2], x, y)
    assert sp.expand(rem) == 0
    assert all(sp.nsimplify(c) >= 0 for c, _b in terms)


def test_finder_escalates_multiplicity():
    # x on V(x^3): x^2 not in <x^3> but x^4 = x * x^3 is — m=2, s=0.
    found = find_real_nullstellensatz_certificate(x, [x ** 3], (x,), max_m=2)
    assert found is not None
    m, terms = found
    assert m == 2 and terms == []


def test_finder_refuses_nonvanishing_p():
    # x + 1 does NOT vanish at the origin = the real variety of x^2 + y^2.
    assert find_real_nullstellensatz_certificate(
        x + 1, [x ** 2 + y ** 2], (x, y)) is None


def test_finder_is_deterministic():
    a = find_real_nullstellensatz_certificate(x, [x ** 2 + y ** 2], (x, y))
    b = find_real_nullstellensatz_certificate(x, [x ** 2 + y ** 2], (x, y))
    assert a == b


def _family(p, gens, sos):
    return real_nullstellensatz_family(
        "RN", (x, y), GridSpec([("i", [0])]), lambda pt: "rn_case",
        lambda pt: (p, None, sos, gens))


def test_finder_mode_certifies_and_emits():
    res = emit(certify(_family(x, [x ** 2 + y ** 2], None)),
               LeanProfile(namespace=("T",)), [RealNullstellensatzEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "pow_eq_zero_iff" in body


def test_finder_mode_refuses_when_no_certificate():
    with pytest.raises(CertificationError):
        certify(_family(x + 1, [x ** 2 + y ** 2], None))
