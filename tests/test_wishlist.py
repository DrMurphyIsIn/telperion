"""Wishlist 3-7 tests: latex, tails, SOS, interchange+recheck, parallel."""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    TailFrom,
    TailNatEmitter,
    ValidationReport,
    certify,
    emit,
    tail_family,
)
from telperion.interchange import export_certificates  # noqa: E402
from telperion.latex import latex_appendix  # noqa: E402
from telperion.provenance import family_hash  # noqa: E402
from telperion.recheck import recheck  # noqa: E402
from telperion.sos import sos_certify, sos_decompose  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


def fam2():
    return InequalityFamily(
        name="W",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"W_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


# ---- 3: latex ---------------------------------------------------------------
def test_latex_appendix_carries_hash_and_ties():
    cf = certify(fam2())
    ihash = family_hash(cf.family, LeanProfile())
    tex = latex_appendix(cf, ihash)
    assert ihash[:16] in tex
    assert "W\\_a1" in tex or "W_a1" in tex
    assert "\\begin{tabular}" in tex


def test_latex_blueprint_mode():
    cf = certify(fam2())
    tex = latex_appendix(cf, "f" * 64, blueprint=True)
    assert "\\lean{W_a1}" in tex and "\\leanok" in tex


# ---- 4: symbolic tails ------------------------------------------------------
def test_tail_family_certifies_finite_plus_symbolic():
    fam = tail_family(
        name="T",
        axis="K",
        tail=TailFrom(threshold=5, lo=3),
        symbols=(),
        target=lambda pt: (pt["K"] - 2) / (pt["K"] + 1),
        lean_name=lambda pt: f"T_K{pt['K']}",
    )
    cf = certify(fam)
    names = sorted(i.lean_name for i in cf.instances)
    assert names == ["T_K3", "T_K4", "T_Kge5"]
    # the tail certificate is over the fresh symbol t_K
    tail = next(i for i in cf.instances if i.lean_name == "T_Kge5")
    assert sp.Symbol("t_K", nonnegative=True) in tail.corners[0].expr.free_symbols


def test_tail_nat_emitter_renders_quantified_theorem():
    fam = tail_family(
        name="T",
        axis="K",
        tail=TailFrom(threshold=5),
        symbols=(),
        target=lambda pt: (pt["K"] - 2) / (pt["K"] + 1),
        lean_name=lambda pt: f"T_K{pt['K']}",
    )
    res = emit(
        certify(fam),
        LeanProfile(),
        [DirectPolyaEmitter(), TailNatEmitter(axis="K", threshold=5)],
        GREEN,
    )
    text = next(iter(res.files.values()))
    assert "theorem T_Kge5_nat (K : ℕ) (hK : 5 ≤ K)" in text
    assert "push_cast [Nat.cast_sub hK]" in text
    assert "exact T_Kge5 ((K - 5 : ℕ) : ℝ) himg" in text


# ---- 5: SOS -----------------------------------------------------------------
def test_sos_even_power():
    cert = sos_decompose((u - 1) ** 2, (u,))
    assert cert is not None
    assert sp.simplify(cert.as_expr() - (u - 1) ** 2) == 0


def test_sos_quadratic_completion_two_vars():
    e = sp.expand(u**2 - u * v + v**2)  # positive definite, interior-tight at 0
    cert = sos_decompose(e, (u, v))
    assert cert is not None
    assert sp.simplify(cert.as_expr() - e) == 0


def test_sos_certify_with_denominator():
    out = sos_certify((u - 1) ** 2 / (u + 1), (u,))
    assert out is not None
    cert, den = out
    assert sp.simplify(den - (u + 1)) == 0


def test_sos_refuses_negative():
    assert sos_decompose(u - 3, (u,)) is None


# ---- 6: interchange + recheck ----------------------------------------------
def test_export_recheck_roundtrip_and_tamper():
    cf = certify(fam2())
    doc = export_certificates(cf, "a" * 64)
    assert recheck(doc, trials=15) == []
    # tamper with a coefficient -> identity check must catch it
    key = next(iter(doc["instances"][0]["corners"][0]["numerator"]))
    doc["instances"][0]["corners"][0]["numerator"][key] = "99/1"
    problems = recheck(doc, trials=15)
    assert any("IDENTITY FAILS" in p for p in problems)


def test_export_covers_lifted_certificates():
    fam = InequalityFamily(
        name="WL",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "WL_a1",
        target=lambda pt: (u**2 - u + 1) / (u + 1),
        auto_lift=2,
    )
    doc = export_certificates(certify(fam), "b" * 64)
    assert doc["instances"][0]["corners"][0]["lift_n"] == 1
    assert recheck(doc, trials=15) == []  # lifted num/den still satisfy the identity


# ---- 7: parallel certify ----------------------------------------------------
def test_parallel_certify_matches_serial():
    fam = fam2()
    serial = certify(fam)
    parallel = certify(fam, workers=2)
    assert [i.lean_name for i in serial.instances] == [
        i.lean_name for i in parallel.instances
    ]
    for a, b in zip(serial.instances, parallel.instances):
        assert sp.expand(a.corners[0].numerator - b.corners[0].numerator) == 0
    assert serial.checks_passed == parallel.checks_passed
