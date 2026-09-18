"""winding_box_zero emitter — Arb-trust-class winding-number box certificate (turing_band trust class).

Rigorous winding-number zero count on a rational-cornered box; ships a .cert.json sidecar + a doc stub
(NO kernel theorem).  Self-check re-runs the winding at DOUBLED precision + density; a claimed count
the argument principle does not support is the negative control and is refused.
"""
import cmath
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import WindingBoxZeroEmitter  # noqa: E402
from telperion.emit_winding_box_zero import (  # noqa: E402
    winding_box_zero_certificate, winding_box_zero_family,
    certify_winding_box_zero_point, register_winding_fn,
)
from telperion.family import GridSpec  # noqa: E402


def _analytic_winding(z0):
    """Libflint-free winding double: quadrant-advance argument principle for f(z)=z−z0."""
    def _wind(re0, re1, im0, im1, prec, n_per_side):
        r0, r1, i0, i1 = map(float, (re0, re1, im0, im1))
        N = n_per_side
        pts = []
        for k in range(N):
            pts.append(complex(r0 + (r1 - r0) * k / N, i0))
        for k in range(N):
            pts.append(complex(r1, i0 + (i1 - i0) * k / N))
        for k in range(N):
            pts.append(complex(r1 - (r1 - r0) * k / N, i1))
        for k in range(N):
            pts.append(complex(r0, i1 - (i1 - i0) * k / N))
        total = 0.0
        for a in range(len(pts)):
            b = (a + 1) % len(pts)
            va, vb = pts[a] - z0, pts[b] - z0
            d = cmath.phase(vb) - cmath.phase(va)
            while d > cmath.pi:
                d -= 2 * cmath.pi
            while d < -cmath.pi:
                d += 2 * cmath.pi
            total += d
        return round(total / (2 * cmath.pi))
    return _wind


_WIND = _analytic_winding(complex(0.5, 0.5))


def test_positive_cert_winding_one_reverified():
    cert = winding_box_zero_certificate(
        re0="0", re1="1", im0="0", im1="1", expected_winding=1,
        prec=64, n_per_side=32, winding_fn=_WIND)
    assert cert.winding == 1
    assert cert.trust_class == "arb"
    assert cert.edge_samples == 4 * 32
    js = cert.to_json_dict()
    assert js["kind"] == "winding_box_zero" and js["trust_class"] == "arb"


def test_positive_cert_winding_zero_outside():
    cert = winding_box_zero_certificate(
        re0="2", re1="3", im0="2", im1="3", expected_winding=0,
        prec=64, n_per_side=32, winding_fn=_WIND)
    assert cert.winding == 0


def test_refuses_winding_one_claimed_as_zero():
    # NEGATIVE CONTROL: a winding-1 box presented as winding-0.
    try:
        winding_box_zero_certificate(
            re0="0", re1="1", im0="0", im1="1", expected_winding=0,
            prec=64, n_per_side=32, winding_fn=_WIND)
        raised = False
    except Exception:
        raised = True
    assert raised, "a winding-1 box claimed as winding-0 must be refused"


def test_refuses_winding_zero_claimed_as_one():
    # NEGATIVE CONTROL: a winding-0 box (z0 outside) presented as winding-1.
    try:
        winding_box_zero_certificate(
            re0="2", re1="3", im0="2", im1="3", expected_winding=1,
            prec=64, n_per_side=32, winding_fn=_WIND)
        raised = False
    except Exception:
        raised = True
    assert raised, "a winding-0 box claimed as winding-1 must be refused"


def test_emit_ships_sidecar_and_no_kernel_theorem():
    register_winding_fn("_test_double", _WIND)
    fam = winding_box_zero_family(
        "WBZ", GridSpec([("_", [0])]), lambda pt: "winding_one",
        spec=lambda pt: {"re0": "0", "re1": "1", "im0": "0", "im1": "1",
                         "expected_winding": 1, "prec": 64, "n_per_side": 32,
                         "winding_fn": "_test_double"})
    inst, checks = certify_winding_box_zero_point(fam, {"_": 0}, "winding_one")
    em = WindingBoxZeroEmitter()

    class _V:
        instances = [inst]

    body, nthm = em.emit_body(_V())
    # Arb sidecar carries NO kernel theorem (honest trust accounting).
    assert nthm == 0
    assert "Arb-trust-class, NOT kernel" in body
    assert "NO kernel theorem" in body
    assert len(em._cert_sink) == 1 and em._cert_sink[0]["trust_class"] == "arb"


def test_registered_as_first_class_kind():
    # Arb-trust-class sidecar kind: registered in the dispatch AND classified in the
    # sensitivity registry (a normal discovered Emitter subclass, STRUCTURALLY_NONVACUOUS).
    from telperion.certify import _SPECIAL_KINDS, _SPECIAL_DISPATCH
    from telperion.emitter_sensitivity import REGISTRY
    assert "winding_box_zero" in _SPECIAL_KINDS
    assert "winding_box_zero" in _SPECIAL_DISPATCH
    assert "WindingBoxZeroEmitter" in REGISTRY
