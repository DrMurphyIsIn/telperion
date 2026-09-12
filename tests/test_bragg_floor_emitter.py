"""Bragg-floor emitter (Route P Brick D3 part 2): certificate, pipeline, forge, negative control.

The order-`n` diffraction rung `floorHi ≤ braggLo − tailHi` is the FINITE claim that the truncated
log-prime (von Mangoldt / Bragg) amplitude at a fixed base point `s0 > 1`, net of a certified tail,
clears the explicit archimedean floor `-(1 + Re taylorCoeff Γℝ n)`.  The Lean kernel is the arbiter
(CI `lake build` of the `li_positivity` island); these are the pre-CI self-checks — the exact
rational margin, the honest refusals (the forge face), byte-stable rendering, and full registry
wiring.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    BraggFloorEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    bragg_floor_certificate,
    bragg_floor_family,
    certify,
    emit,
)
from telperion.bragg_coeff import (  # noqa: E402
    BASE_S0,
    BraggFloorData,
    enclose_arch_floors,
    enclose_bragg_truncation,
    _is_prime_power,
)
from telperion.certify import emitter_for  # noqa: E402


# --- registry wiring --------------------------------------------------------

def test_kind_is_bragg_floor():
    fam = bragg_floor_family("T", GridSpec([("n", [0])]), lambda pt: "t", spec=lambda pt: None)
    assert fam.kind == "bragg_floor"


def test_emitter_for_round_trips():
    assert emitter_for("bragg_floor").kind == "bragg_floor"


def test_emitter_is_classified_and_has_adapter():
    from telperion.emitter_sensitivity import REGISTRY
    from telperion.negative_control_harness import ADAPTERS
    assert "BraggFloorEmitter" in REGISTRY
    assert "BraggFloorEmitter" in ADAPTERS


# --- the prime-power support helper ----------------------------------------

def test_is_prime_power():
    assert _is_prime_power(2) == 2
    assert _is_prime_power(4) == 2
    assert _is_prime_power(8) == 2
    assert _is_prime_power(9) == 3
    assert _is_prime_power(27) == 3
    assert _is_prime_power(49) == 7
    assert _is_prime_power(6) is None      # 2·3, not a prime power
    assert _is_prime_power(12) is None
    assert _is_prime_power(1) is None


# --- the certificate: honest margin + refusals (the forge face) -------------

def _data(n, bragg_lo, tail_hi, floor_hi, cutoff=1000, s0=BASE_S0):
    return BraggFloorData(
        n=n, s0=s0, cutoff=cutoff,
        bragg_lo=Fraction(bragg_lo), tail_hi=Fraction(tail_hi), floor_hi=Fraction(floor_hi),
    )


def test_certificate_accepts_positive_margin():
    cert = bragg_floor_certificate(_data(0, "0.57", "0.01", "0.55"))
    assert cert.n == 0
    assert cert.margin == sp.Rational("0.57") - sp.Rational("0.01") - sp.Rational("0.55")
    assert cert.margin > 0


def test_forge_refuses_non_positive_margin():
    # floor exceeds the net amplitude => refused (the fixed-s0 amplitude does not clear this floor)
    with pytest.raises(ValueError, match="margin.*≤ 0|does not clear"):
        bragg_floor_certificate(_data(1, "0.57", "0.01", "0.90"))
    # exact tie (margin == 0) is also refused (strict clearance required)
    with pytest.raises(ValueError, match="margin.*≤ 0|does not clear"):
        bragg_floor_certificate(_data(1, "0.57", "0.07", "0.50"))


def test_forge_perturb_tail_breaks_it():
    # a genuine rung...
    bragg_floor_certificate(_data(0, "0.569", "0.008", "0.554"))
    # ...perturb the tail up past the margin and it is refused
    with pytest.raises(ValueError, match="margin.*≤ 0|does not clear"):
        bragg_floor_certificate(_data(0, "0.569", "0.020", "0.554"))


def test_certificate_refuses_bad_base_point_and_cutoff():
    with pytest.raises(ValueError, match="s0 > 1"):
        bragg_floor_certificate(_data(0, "0.57", "0.01", "0.55", s0=Fraction(1)))
    with pytest.raises(ValueError, match="cutoff ≥ 2"):
        bragg_floor_certificate(_data(0, "0.57", "0.01", "0.55", cutoff=1))


# --- the Arb backend: enclosures + anchors ----------------------------------

def test_arch_floors_enclose_known_signs():
    floors = enclose_arch_floors(12)
    # floor(0) ≈ +0.554, floor(7) flips negative, floor(11) ≈ -2.09 (see the probe)
    assert float(floors[0][0]) > 0.5 and float(floors[0][1]) < 0.6
    assert float(floors[7][1]) < 0
    assert float(floors[11][1]) < -2


def test_bragg_truncation_brackets_and_tail_shrinks():
    lo50, hi50, tail50 = enclose_bragg_truncation(50)
    lo1000, hi1000, tail1000 = enclose_bragg_truncation(1000)
    # partial sum rises toward -ζ'/ζ(2) ≈ 0.56996 and the tail shrinks with N
    assert lo50 <= lo1000
    assert tail1000 < tail50
    assert 0.55 < float(lo1000) < 0.57


def test_bragg_truncation_tail_is_a_real_upper_bound():
    # the certified tail must upper-bound the true omitted mass: (full - partial) ≤ tail_hi.
    import mpmath as mp
    mp.mp.dps = 30
    full = -mp.zeta(2, derivative=1) / mp.zeta(2)   # -ζ'/ζ(2) = Σ Λ(m) m^-2
    lo, hi, tail = enclose_bragg_truncation(1000)
    omitted = float(full) - float(hi)               # true tail ≤ full - partial_hi
    assert omitted <= float(tail) + 1e-12


# --- the full pipeline: certify -> emit renders the expected theorems -------

def _mk(n, cutoff, floors):
    lo, _hi, tail = enclose_bragg_truncation(cutoff)
    return BraggFloorData(
        n=n, s0=BASE_S0, cutoff=cutoff,
        bragg_lo=lo, tail_hi=tail, floor_hi=floors[n][1],
    )


def _emit(ns, cutoff=1000):
    floors = enclose_arch_floors(max(ns) + 1)
    fam = bragg_floor_family(
        "BraggFloorTest",
        GridSpec([("n", list(ns))]),
        lambda pt: f"bragg_rung_{pt['n']}",
        spec=lambda pt: _mk(pt["n"], cutoff, floors),
    )
    rep = emit(
        certify(fam),
        LeanProfile(namespace=("BraggFloorTest",), imports=("RvMRoutePFalsify",)),
        [BraggFloorEmitter()],
        ValidationReport(checks=(("bragg_floor", True),)),
    )
    return next(iter(rep.files.values()))


def test_emit_renders_expected_theorems():
    text = _emit([0, 8, 11])
    assert "bragg_rung_0" in text
    assert "bragg_rung_11" in text
    assert "by norm_num" in text
    # the honesty disclaimers are in every rung
    assert "conjecture1_proved = False" in text
    assert "CONDITIONAL" in text
    assert "taylorCoeff_companion_bragg_of_exhaustion_limits" in text


def test_emit_refuses_uncleared_order():
    # n=2's floor (~+1.01) exceeds the fixed-s0 amplitude (~0.57); certify must fail honestly.
    from telperion.certify import CertificationError
    with pytest.raises(CertificationError, match="margin|does not clear"):
        _emit([2])


def test_refutation_atom_text_carries_conditional_seam():
    from telperion import bragg_below_floor_refutes_rh_lean
    atom = bragg_below_floor_refutes_rh_lean()
    assert "bragg_below_floor_refutes_rh" in atom
    assert "companion_below_floor_refutes_rh" in atom
    assert "hcomp" in atom                 # the conditional seam is an explicit hypothesis
    assert "NEVER discharged" in atom
    assert "conjecture1_proved = False" in atom


# --- the generated example + frozen-output drift guard ----------------------

def _load_generator():
    import importlib.util as _u
    gen_path = (Path(__file__).resolve().parents[1]
                / "examples" / "li_positivity" / "generate_bragg_floor.py")
    spec = _u.spec_from_file_location("bragg_floor_generate", gen_path)
    mod = _u.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_generated_ladder_emits_cleared_rungs_and_atom():
    pytest.importorskip("flint")
    text = _load_generator().build()
    # the refutation atom, once, wired to the conditional seam
    assert text.count("theorem bragg_below_floor_refutes_rh") == 1
    assert "RvMCompanionBraggLimit" in text
    assert "import RvMRoutePFalsify" in text
    # n=0 clears; the mid-range orders n=1..5 are honestly refused (not emitted)
    assert "theorem bragg_rung_0 " in text
    for n in (1, 2, 3, 4, 5):
        assert f"theorem bragg_rung_{n} " not in text
    # the high orders (floor goes negative) all clear
    for n in (6, 11, 19):
        assert f"theorem bragg_rung_{n} " in text
    # short decimal literals, not thousand-digit dyadics
    assert "00000000000000000" not in text


def test_frozen_output_matches_regeneration():
    pytest.importorskip("flint")
    assert _load_generator().main(check=True) == 0, (
        "BraggFloor.lean drifted from its generator — regenerate with "
        "`python examples/li_positivity/generate_bragg_floor.py`")
