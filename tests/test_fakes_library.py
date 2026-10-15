"""Tests for telperion.fakes_library (the standing calibration-fake library).

conjecture1_proved = False.  Every zero-box test below is an ARB certification (arb_fakes' segment-enclosure
winding at 128 bits, rechecked at 192).  An entry flagged ``slow`` is opt-in (TELPERION_ARB_SLOW=1, the
TELPERION_PM_KERNEL-style convention); none is at present: every registered box certifies in under a second.
"""
import os
from fractions import Fraction as F

import pytest

flint = pytest.importorskip("flint")

from telperion import arb_fakes  # noqa: E402
from telperion import fakes_library as L  # noqa: E402
from telperion.fakes_library import Box, Claim  # noqa: E402

_SLOW = os.environ.get("TELPERION_ARB_SLOW") == "1"
slow = pytest.mark.skipif(not _SLOW, reason="slow Arb certification (opt-in: TELPERION_ARB_SLOW=1)")

EXPECTED = {"EP5", "EPQ2", "DH", "TW_raw", "TW_fix", "ZP", "ZP5", "SH", "SYM", "FF", "H", "N8"}


def _params(entries):
    return [pytest.param(e.name, marks=slow) if e.slow else e.name for e in entries]


# ------------------------------------------------------------------------------------------------ registry shape
def test_registry_has_every_object():
    assert set(L.names()) == EXPECTED


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_metadata_complete(name):
    e = L.get(name)
    assert set(e.ingredients) == set(L.INGREDIENTS)
    assert all(st in L.STATUSES and ev for st, ev in e.ingredients.values())
    assert e.provenance.get("memo") and e.provenance.get("review")
    assert e.conditional and e.known_zeros and e.pole_basis
    zb = e.zero_box
    assert zb is not None and zb.re0 > F(1, 2), "registered zero box must be off-line (right of 1/2)"
    assert e.region is None or e.region.contains_box(zb)
    assert "zero_box" not in e.public_meta() and "known_zeros" not in e.public_meta()
    assert "/Users/" not in repr(e.meta())


def test_rho0_full_precision():
    """rho0 is built from the exact decimal at the CALLER's working precision (evaluators run at arb_fakes' prec)."""
    assert L.RHO0_IM == "14.134725141734693" and L.G0 == F("14.134725141734693")
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = 128
        r = L._rho0()
        assert r.imag.rad() < 1e-30 and r.imag.contains(arb("14134725141734693/1000000000000000"))
    finally:
        ctx.prec = old


# ------------------------------------------------------------------------------------------------ (a) zero boxes
@pytest.mark.parametrize("name", _params(L.REGISTRY.values()))
def test_registered_zero_box_certifies(name):
    c = L.certify_entry_box(name, prec=128)
    assert c["zeros_in_box"] == 1 and c["trust_class"] == "arb" and c["off_line"]
    assert c["prec"] == 128 and c["recheck_prec"] == 192


@pytest.mark.parametrize("name", ["TW_raw", "TW_fix", "SYM"])
def test_pole_exclusion_boxes_certify(name):
    """The region's pole list is complete because zeta is certified zero-free on every shifted image box."""
    cs = L.certify_pole_exclusion(name)
    assert len(cs) == (4 if name == "SYM" else 2)
    assert all(c["zeros_in_box"] == 0 for c in cs)
    assert sum(c["poles_in_box"] for c in cs) == 1          # zeta's pole w = 1, i.e. the zero s = rho0


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_registered_zero_box_certifies_256(name):
    assert L.certify_entry_box(name, prec=256)["zeros_in_box"] == 1


def test_zp_count_matches_factor():
    """ZP in [0.7, 3/2] x [1/20, 100]: exactly the factor's zeros log2(alpha) + 2 pi i k / log 2, k = 1..11
    (S/T's count, here with the library's pole handling; zeta has no zeros there)."""
    c = L.count_entry("ZP", Box.of("0.7", "3/2", "1/20", "100"), cuts=["25", "50", "75"])
    assert c["total"] == 11


# ------------------------------------------------------------------------------------------------ definitions
def test_tw_no_fe_value_matches_bb():
    """bb's ARB: TW(1 - conj rho0) = 0.0875640 + 0.0706352i != 0 (selberg.md 3.4)."""
    v = L.get("TW_raw").eval(1 - L._rho0().conjugate())
    assert v.real.overlaps(flint.arb("0.0875640", "1e-7")) and v.imag.overlaps(flint.arb("0.0706352", "1e-7"))


def test_sym_not_zero_at_reflected_points():
    """1 - rho0 and rho0 - 1 are zeros of Lambda_SYM only, not of SYM (bb N: |SYM| = 0.0544, 0.199)."""
    r = L._rho0()
    e = L.get("SYM")
    a, b = abs(e.eval(1 - r)), abs(e.eval(r - 1))
    assert a.overlaps(flint.arb("0.0544", "1e-4")) and b.overlaps(flint.arb("0.1995", "1e-3"))


def test_tw_fix_small_primes():
    ps = L._small_primes()
    assert ps[0] == 2 and ps[-1] == 101 and len(ps) == 26   # p < 2^(1/0.15) = 101.59; 103 is twisted


def test_ff_and_h_box_contains_algebraic_zero():
    """The FF / H zero box contains -log(T0)/log 3 for the root T0 of P_fake with Re -log T0/log 3 = 0.8748 (ARB
    root isolation, independent of the winding)."""
    from flint import acb, ctx, fmpz_poly
    ctx.prec = 128
    zs = [-r.log() / acb(3).log() for r, _ in fmpz_poly(list(L.P_FAKE)).complex_roots()]
    b = L.get("FF").zero_box
    re0, re1, im0, im1 = map(L._arbq, b.tuple())
    inside = [z for z in zs if re0 < z.real and z.real < re1 and im0 < z.imag and z.imag < im1]
    assert len(inside) == 1 and L.get("H").zero_box == b


def test_n8_branches_agree():
    """N8's near (entire Ein) and far (E1 = e^-w U(1,1,w)) forms agree where both are valid: at s = rho0 + 1/2 the
    default uses the Ein form for the rho0 term (|w| = 2.3) and near=False uses E1 for it; and the far form matches
    acb.expint at 256 bits (the lead's 'acb exponential integral')."""
    from flint import acb, acb_series, arb, ctx
    old = (ctx.prec, ctx.cap)
    try:
        ctx.prec, ctx.cap = 128, 1
        s = L._rho0() + arb("1/2")
        a = L._n8_series(acb_series([s])).coeffs()[0]
        b = L._n8_series(acb_series([s]), near=False).coeffs()[0]
        assert a.overlaps(b) and a.rad() < 1e-20 and b.rad() < 1e-20
        ctx.prec = 256
        w = acb(arb("5.3"), arb("79.4"))
        assert ((-w).exp() * w.hypgeom_u(1, 1)).overlaps(w.expint(1))
    finally:
        ctx.prec, ctx.cap = old


def test_n8_matches_e1_formula_right_halfplane():
    """At s = 2 + 3i: zeta_P = exp(E1((s-1)v0) - E1((s-rho0)v0) - E1((s-conj rho0)v0)) evaluated directly with
    acb.expint at 256 bits (no cut is crossed there)."""
    from flint import acb, ctx
    s = acb(2, 3)
    r = L._rho0()
    old = ctx.prec
    try:
        ctx.prec = 256
        v0 = acb(103).log()
        direct = (((s - 1) * v0).expint(1) - ((s - r) * v0).expint(1) - ((s - r.conjugate()) * v0).expint(1)).exp()
    finally:
        ctx.prec = old
    assert L.get("N8").eval(s).overlaps(direct)


# ------------------------------------------------------------------------------------------------ (b) calibrate
GRID = Box.of("51/100", "149/100", "1", "100")


def toy_rh_prover(f, meta):
    """'Proves' RH on GRID: |F| > 0 at every point of a coarse grid, so 'no off-line zeros'.  Unsound by design."""
    from flint import acb, arb
    re = [F(51, 100) + F(k, 4) for k in range(4)]
    im = [F(1) + k for k in range(100)]
    for x in re:
        for y in im:
            try:
                v = f(acb(arb(f"{x.numerator}/{x.denominator}"), arb(y.numerator)), prec=64)
            except Exception:
                continue                       # 'a pole, skip it' -- also unsound
            if v.contains(0):
                return None
    return Claim(GRID)


def honest(f, meta):
    return None


def test_toy_rh_prover_caught_by_every_entry():
    rep = L.calibrate(toy_rh_prover)
    assert set(rep["contradicted"]) == EXPECTED, rep["rows"]
    assert not rep["errors"] and not rep["declined"] and not rep["inconclusive"]


def test_honest_mechanism_never_contradicted():
    rep = L.calibrate(honest)
    assert rep["contradicted"] == [] and set(rep["declined"]) == EXPECTED


def test_calibrate_reports_errors_and_partial_overlap():
    def crash(f, meta):
        raise RuntimeError("boom")

    assert L.calibrate(crash, entries=["EP5"])["errors"] == ["EP5"]
    zb = L.get("ZP").zero_box
    half = Box(zb.re0, zb.re1, zb.im0, (zb.im0 + zb.im1) / 2)   # covers only half of the zero box
    rep = L.calibrate(lambda f, m: Claim(half), entries=["ZP"])
    assert rep["inconclusive"] == ["ZP"] and rep["contradicted"] == []
    far = Box.of("2", "3", "0", "1")
    assert L.calibrate(lambda f, m: Claim(far), entries=["ZP"])["rows"][0]["status"] == "not_contradicted"


def test_calibrate_recertify_is_arb_end_to_end():
    rep = L.calibrate(lambda f, m: Claim(GRID), entries=["EP5", "N8"], recertify=True)
    assert rep["contradicted"] == ["EP5", "N8"] and rep["recertified"]


def test_mechanism_does_not_see_the_answer():
    seen = []
    L.calibrate(lambda f, m: seen.append(m), entries=["DH"])
    assert "zero_box" not in seen[0] and "known_zeros" not in seen[0]


# ------------------------------------------------------------------------------------------------ (c) poles
NEAR_ONE = Box.of("9/10", "11/10", "-1/10", "1/10")


@pytest.mark.parametrize("name", ["ZP", "ZP5", "H", "N8", "EP5"])
def test_nearby_pole_is_passed_automatically(name):
    c = L.certify_entry_box(name, NEAR_ONE, expected=0)
    assert c["winding"] == -1 and c["poles_in_box"] == 1 and c["zeros_in_box"] == 0
    assert c["declared_poles_passed"] == [("1", "0")]


def test_without_declared_poles_the_raw_callable_is_refused():
    """The same box through arb_fakes with the bare callable (no poles=): winding -1 != 0 zeros -> refused.  The
    library is what supplies the pole."""
    with pytest.raises(ValueError, match="refused"):
        arb_fakes.certify_zero_box(L.get("ZP").series, *NEAR_ONE.tuple(), expected=0, prec=96)


def test_pole_on_boundary_refused():
    with pytest.raises(ValueError, match="boundary"):
        L.certify_entry_box("ZP", Box.of("1", "11/10", "-1/10", "1/10"), expected=0)
    with pytest.raises(ValueError, match="boundary"):
        L.count_entry("N8", NEAR_ONE, cuts=["0"])               # the cut runs through s = 1


def test_box_outside_region_refused():
    """TW's poles rho_zeta + rho0 - 1 (e.g. 0.35 + i(gamma0 - gamma1), within 1e-15 of the real axis) are not
    declared; any box outside the certified region is refused rather than counted as zeros minus poles."""
    with pytest.raises(ValueError, match="region"):
        L.certify_entry_box("TW_raw", Box.of("0.3", "0.4", "-0.1", "0.1"), expected=0)
    with pytest.raises(ValueError, match="region"):
        L.count_entry("SYM", Box.of("0.6", "0.9", "14", "14.3"))
    with pytest.raises(ValueError, match="region"):
        L.certify_entry_box("FF", Box.of("0.9", "1.1", "-0.1", "0.1"), expected=0)


def test_count_entry_adds_poles():
    c = L.count_entry("N8", NEAR_ONE, cuts=["1/20"])
    assert c["total"] == 0 and sum(s["poles"] for s in c["strips"]) == 1


def test_resolve_provenance_uses_env(monkeypatch, tmp_path):
    monkeypatch.setenv("TELPERION_RH_TEAM", str(tmp_path))
    p = L.resolve_provenance("rh-team:wall4/S/selberg.md 3.2")
    assert p == tmp_path / "wall4/S/selberg.md"
    assert L.resolve_provenance("bb in-session check") is None


def test_repo_provenance_paths_exist():
    """Every repo-relative provenance path (telperion/...) points at a committed file; rh-team / e9-research paths
    are checked only when that checkout is present."""
    for e in L.REGISTRY.values():
        for v in e.provenance.values():
            for part in v.split(";"):
                p = L.resolve_provenance(part.strip())
                if p is None:
                    continue
                prefix = part.strip().split(":", 1)[0]
                root = L.resolve_provenance(prefix + ":.") if prefix in ("rh-team", "e9-research") else None
                if part.strip().startswith("telperion/") or (root is not None and root.is_dir()):
                    assert p.exists(), (e.name, part)
