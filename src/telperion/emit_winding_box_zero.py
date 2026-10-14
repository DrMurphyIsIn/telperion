"""Winding-box-zero emitter — Arb-trust-class winding-number box certificate for a zero.

The zero-localization sidecar distilled from `arb_dh.certify_offline_zero` (QC_DH_SCOUT): for an analytic
function `f` and a rational-cornered box on whose boundary `f` does not vanish, the number of zeros strictly
inside equals the winding number `(1/2π)·Δ_∂box arg f`.

**Method.**  The default backend (``"arb_dh"``) is `arb_dh.winding_number_rigorous`, the segment-enclosure
argument principle of `telperion.arb_winding`: f and f' are enclosed in Arb balls on every boundary SEGMENT, so
the argument change along each segment is bounded, and a segment that cannot be certified is bisected or
refused.  A returned integer `k` is then an Arb-trust-class count for the open rectangle.  Every certificate
records the ``method`` that produced it and the backend's ``trust_class``.

**Correction (2026-10-14).**  Until this date the default backend was `arb_dh.winding_number`, which sampled f
only at boundary NODES and summed quadrant advances.  Its ball values were rigorous but its count was a
heuristic: nothing bounded the argument change between nodes, and an independent audit built a box holding 2
zeros that it certified as 1, doubled recheck included.  That routine is now
`arb_dh.winding_number_sampled_heuristic` and is not a registered backend.  Earlier text here and in the
emitted stubs called its integer rigorous; that was wrong.

**This is an Arb-trust-class kind, NOT a kernel theorem** — the same trust class as `turing_band`'s
Arb sidecars.  The emitter therefore produces:

  * a ``.cert.json`` SIDECAR recording the box corners, the method, the initial boundary subdivision, the
    working precision, the winding integer, and the backend's ``trust_class`` label; and
  * a documentation STUB (a Lean comment block, NO theorem, NO kernel claim) honestly stating the
    trust boundary — mirroring how `campaign.py verify-bands` documents turing_band sidecars.

Self-check: the winding integer is re-run at DOUBLED precision AND a DOUBLED initial subdivision; the two runs
must reproduce the SAME integer, or certification is REFUSED.  The recheck guards against resolution
artefacts only.  It cannot make a non-rigorous method rigorous (the node-sampling heuristic passed it with a
wrong count), so rigor rests on the method.

NEGATIVE CONTROL: a claimed winding that does not match the (re-verified) computed winding — e.g. a
winding-0 box presented as winding-1 — is REFUSED.  conjecture1_proved = False — a finite zero-count,
nothing about RH.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable

from dataclasses import dataclass as _dataclass

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

#: The method label of the default backend (identical to `telperion.arb_winding.METHOD`; repeated here so
#: this module imports without python-flint).
SEGMENT_METHOD = "segment-enclosure (centred form, |f - c| <= |c|/2 per segment)"


@dataclass(frozen=True)
class WindingBackend:
    """A winding backend: ``fn(re0, re1, im0, im1, prec, n_per_side) -> int`` plus the honest labels its
    certificates carry.  ``method`` says how the integer was computed; ``trust_class`` says what it is
    worth ("arb" only for a rigorous Arb method)."""

    fn: Callable
    method: str
    trust_class: str


@dataclass(frozen=True)
class WindingBoxZeroCertificate:
    """A verified winding-number box certificate.

    ``winding`` is the zero count for the OPEN rectangle `[re0,re1] × [im0,im1]` computed by ``method``,
    reproduced at doubled precision and a doubled initial subdivision.  ``trust_class`` is the backend's
    label: ``"arb"`` for the rigorous segment-enclosure default; anything else (e.g. ``"float-demo"``) is
    NOT a rigorous count.  Never kernel."""

    re0: str
    re1: str
    im0: str
    im1: str
    prec: int
    n_per_side: int            # initial boundary segments (segment method) or sample nodes per side
    edge_samples: int          # 4 · n_per_side
    winding: int
    trust_class: str = "arb"
    method: str = "unspecified"

    def to_json_dict(self) -> dict:
        return {
            "kind": "winding_box_zero", "trust_class": self.trust_class, "method": self.method,
            "box": {"re0": self.re0, "re1": self.re1, "im0": self.im0, "im1": self.im1},
            "prec": self.prec, "n_per_side": self.n_per_side,
            "edge_samples": self.edge_samples, "winding": self.winding,
        }


def _arb_dh_rigorous(re0, re1, im0, im1, prec, n_per_side):
    from .arb_dh import winding_number_rigorous
    return winding_number_rigorous(re0, re1, im0, im1, prec=prec, init_per_side=n_per_side)


#: The production default: Davenport-Heilbronn by the rigorous segment-enclosure method.
ARB_DH_BACKEND = WindingBackend(fn=_arb_dh_rigorous, method=SEGMENT_METHOD, trust_class="arb")


def winding_box_zero_certificate(
    *, re0, re1, im0, im1, expected_winding: int, prec: int = 200, n_per_side: int = 24,
    winding_fn: Callable | WindingBackend | None = None, method: str | None = None,
    trust_class: str | None = None,
) -> WindingBoxZeroCertificate:
    """Build and EXACTLY re-verify a winding-box-zero certificate.

    ``winding_fn`` is a `WindingBackend`, or a bare ``fn(re0, re1, im0, im1, prec, n_per_side) -> int``, or
    ``None`` for the default `ARB_DH_BACKEND` (DH by the rigorous segment-enclosure method, trust class
    "arb").  A bare function carries no labels of its own: unless ``method`` / ``trust_class`` are given it is
    recorded as method "unspecified (caller-supplied backend)", trust class "unverified" — never "arb" by
    default.  Certification computes the winding at the given resolution AND re-runs it at DOUBLED precision +
    DOUBLED subdivision; both must equal ``expected_winding``.

    REFUSES (``ValueError`` / propagated ``RuntimeError``):
      * an inverted box (`re0 ≥ re1` or `im0 ≥ im1`), or non-positive `prec`/`n_per_side`;
      * a computed winding ≠ ``expected_winding`` (the negative control: a claimed count the
        argument principle does not support);
      * a doubled-resolution winding that disagrees with the base run (a non-reproducible count);
      * (via the backend) a boundary segment that cannot be certified zero-free — a zero may lie on the
        contour.
    """
    r0, r1 = Fraction(re0), Fraction(re1)
    i0, i1 = Fraction(im0), Fraction(im1)
    if not (r0 < r1 and i0 < i1):
        raise ValueError(f"winding_box_zero: inverted box [{r0},{r1}]×[{i0},{i1}]")
    if prec < 1 or n_per_side < 1:
        raise ValueError(f"winding_box_zero: need prec≥1, n_per_side≥1; got {prec}, {n_per_side}")
    if not isinstance(expected_winding, int):
        raise ValueError(f"winding_box_zero: expected_winding must be an int; got {expected_winding!r}")

    if winding_fn is None:
        backend = ARB_DH_BACKEND
    elif isinstance(winding_fn, WindingBackend):
        backend = winding_fn
    else:
        backend = WindingBackend(fn=winding_fn, method="unspecified (caller-supplied backend)",
                                 trust_class="unverified")
    if method is not None or trust_class is not None:
        backend = WindingBackend(fn=backend.fn, method=method or backend.method,
                                 trust_class=trust_class or backend.trust_class)

    w = backend.fn(r0, r1, i0, i1, prec, n_per_side)
    if w != expected_winding:
        raise ValueError(
            f"winding_box_zero: computed winding {w} ≠ claimed {expected_winding} — the argument "
            f"principle does not support this count (the negative control); refused")
    # Re-run at doubled precision AND doubled subdivision (guards resolution artefacts, not method flaws).
    w2 = backend.fn(r0, r1, i0, i1, 2 * prec, 2 * n_per_side)
    if w2 != w:
        raise ValueError(
            f"winding_box_zero: doubled-resolution winding {w2} ≠ base {w} — non-reproducible count; "
            f"refused (raise prec / n_per_side)")
    return WindingBoxZeroCertificate(
        re0=str(r0), re1=str(r1), im0=str(i0), im1=str(i1),
        prec=prec, n_per_side=n_per_side, edge_samples=4 * n_per_side, winding=w,
        trust_class=backend.trust_class, method=backend.method)


# A registry of winding backends, keyed by a STABLE STRING name so the family spec stays
# byte-serializable (a bare function object in the spec would inject its memory address into the
# provenance input hash, making it non-deterministic).  Production uses "arb_dh" (the default, the
# rigorous segment method); examples / tests register a libflint-free double under their own name, with
# labels that say what it is.
_WINDING_FNS: dict[str, WindingBackend] = {}


def register_winding_fn(name: str, fn: Callable, *, method: str = "unspecified (caller-registered backend)",
                        trust_class: str = "unverified") -> None:
    """Register a winding backend under a stable string name (for spec-serializable dispatch).

    ``method`` and ``trust_class`` are recorded in every certificate the backend produces.  Pass
    ``trust_class="arb"`` only for a backend whose integer is rigorous in Arb arithmetic."""
    if name == "arb_dh":
        raise ValueError("winding_box_zero: 'arb_dh' is the built-in rigorous backend; register under another name")
    _WINDING_FNS[name] = WindingBackend(fn=fn, method=method, trust_class=trust_class)


def _resolve_winding_fn(name) -> WindingBackend:
    if name is None or name == "arb_dh":
        return ARB_DH_BACKEND
    if name in _WINDING_FNS:
        return _WINDING_FNS[name]
    raise ValueError(f"winding_box_zero: unknown winding backend {name!r} "
                     f"(register it via register_winding_fn or use 'arb_dh')")


def certify_winding_box_zero_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys ``re0, re1, im0, im1,
    expected_winding`` and optional ``prec``, ``n_per_side``, ``winding_fn`` (a STRING backend name;
    default ``"arb_dh"``, the rigorous segment method, resolved via ``_resolve_winding_fn``)."""
    spec = family.special[1](pt)
    cert = winding_box_zero_certificate(
        re0=spec["re0"], re1=spec["re1"], im0=spec["im0"], im1=spec["im1"],
        expected_winding=int(spec["expected_winding"]),
        prec=int(spec.get("prec", 200)), n_per_side=int(spec.get("n_per_side", 24)),
        winding_fn=_resolve_winding_fn(spec.get("winding_fn")))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _method_paragraph(cert: WindingBoxZeroCertificate) -> str:
    if cert.method == SEGMENT_METHOD:
        return (
            f"    Computed by the argument principle with SEGMENT enclosures\n"
            f"    ({cert.method}): the boundary starts as {cert.n_per_side} segments per\n"
            f"    side; on each, f and f' are enclosed in Arb balls at working precision {cert.prec},\n"
            f"    so the argument change along the whole segment is bounded; a segment that fails is\n"
            f"    bisected, and refused past the depth limit.  RE-RUN at doubled precision\n"
            f"    ({2 * cert.prec}) and a doubled initial subdivision ({2 * cert.n_per_side} per side) —\n"
            f"    both runs give the same integer.\n"
        )
    if cert.trust_class == "float-demo":
        return (
            f"    Computed by a FLOAT demonstration double ({cert.method}),\n"
            f"    {cert.edge_samples} boundary samples ({cert.n_per_side} per side).  This is NOT a rigorous count;\n"
            f"    it exercises the emitter without python-flint.  Re-run at doubled density\n"
            f"    ({2 * cert.n_per_side} per side) with the same integer.\n"
        )
    return (
        f"    Computed by method: {cert.method}\n"
        f"    ({cert.n_per_side} per side, precision {cert.prec}); re-run at doubled resolution with\n"
        f"    the same integer.  Trust class {cert.trust_class}: rigor is only what that method gives.\n"
    )


def render_winding_box_zero_stub(cert: WindingBoxZeroCertificate, *, name: str) -> str:
    """Render the documentation STUB (a Lean comment block — NO theorem, NO kernel claim) that
    honestly states the method and trust boundary, mirroring the turing_band sidecar documentation."""
    label = "Arb-trust-class, NOT kernel" if cert.trust_class == "arb" else \
        f"trust class {cert.trust_class}, NOT rigorous, NOT kernel"
    return (
        f"/-  {name} — WINDING-BOX-ZERO certificate ({label}).\n"
        f"\n"
        f"    Winding-number zero count for the OPEN rectangle\n"
        f"        [{cert.re0}, {cert.re1}] × [{cert.im0}, {cert.im1}]:\n"
        f"        winding = {cert.winding}   (i.e. exactly {cert.winding} zero(s) strictly inside).\n"
        f"\n"
        + _method_paragraph(cert) +
        f"\n"
        f"    TRUST CLASS: {cert.trust_class}.  This is a SIDECAR record\n"
        f"    (see the .cert.json), documented here the way `campaign.py verify-bands` documents\n"
        f"    turing_band sidecars.  There is NO kernel theorem and NO RH claim.\n"
        f"    conjecture1_proved = False.  -/\n"
    )


@_dataclass
class WindingBoxZeroEmitter(Emitter):
    """Emit the Arb-trust-class winding-box-zero SIDECAR (.cert.json) + documentation stub.

    Ships NO kernel theorem (``nthm = 0``); the winding integer is an Arb-trust-class sidecar fact
    (the same trust class as turing_band's sidecars).  A normal discovered Emitter subclass — its
    sensitivity stance is STRUCTURALLY_NONVACUOUS (an Arb sidecar with no corruptible Lean identity;
    the winding is re-verified at doubled resolution at certify time)."""

    def __post_init__(self):
        self.kind = "winding_box_zero"
        self.emit_statement_gate = False  # no kernel statement to gate
        self._cert_sink: list[dict] = []

    def emit_body(self, fam, profile=None) -> tuple[str, int]:
        texts: list[str] = []
        for inst in fam.instances:
            cert: WindingBoxZeroCertificate = inst.payload  # type: ignore[assignment]
            self._cert_sink.append(cert.to_json_dict())
            texts.append(render_winding_box_zero_stub(cert, name=inst.lean_name))
        # nthm = 0: an Arb sidecar carries no kernel theorem (honest trust accounting).
        return "\n".join(texts), 0


def winding_box_zero_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a winding_box_zero family (kind='winding_box_zero').  ``spec``: ``pt -> dict`` with keys
    ``re0, re1, im0, im1, expected_winding`` and optional ``prec``, ``n_per_side``, ``winding_fn``.
    Certification re-verifies the winding at doubled resolution and REFUSES a mismatched claim."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("winding_box_zero", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # A pure-Python FLOAT winding double (no libflint needed, NOT rigorous): winding = zeros of a supplied
    # analytic f inside the box, by node-sampled float phases (the scheme of the old node-sampling
    # heuristic).  Labelled float-demo, so its certificates never claim the "arb" trust class.
    import cmath

    def _demo_winding(re0, re1, im0, im1, prec, n_per_side):
        # f(z) = z - z0 with z0 strictly inside -> winding 1; z0 outside -> winding 0.
        z0 = complex(0.5, 0.5)
        pts = []
        r0, r1, i0, i1 = map(float, (re0, re1, im0, im1))
        N = n_per_side
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

    _DEMO_METHOD = "float-demo (node-sampled float phase of z - z0; NOT rigorous)"
    _demo = WindingBackend(fn=_demo_winding, method=_DEMO_METHOD, trust_class="float-demo")

    print("=== positive cert (box around z0=0.5+0.5i, winding 1) ===")
    c = winding_box_zero_certificate(
        re0="0", re1="1", im0="0", im1="1", expected_winding=1,
        prec=64, n_per_side=32, winding_fn=_demo)
    print(f"cert OK: winding={c.winding} trust={c.trust_class} sidecar={c.to_json_dict()}")

    print("\n=== NEGATIVE CONTROL: winding-1 box claimed as winding-0 (must raise) ===")
    try:
        winding_box_zero_certificate(
            re0="0", re1="1", im0="0", im1="1", expected_winding=0,
            prec=64, n_per_side=32, winding_fn=_demo)
        raise SystemExit("FAIL: mismatched winding not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: winding-0 box (z0 outside) claimed as winding-1 (must raise) ===")
    try:
        winding_box_zero_certificate(
            re0="2", re1="3", im0="2", im1="3", expected_winding=1,
            prec=64, n_per_side=32, winding_fn=_demo)
        raise SystemExit("FAIL: winding-0-as-1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted documentation stub (nthm=0, float-demo sidecar) ===")
    register_winding_fn("demo", _demo_winding, method=_DEMO_METHOD, trust_class="float-demo")
    fam = winding_box_zero_family(
        "T", GridSpec([("case", [0])]), lambda pt: "winding_demo",
        spec=lambda pt: {"re0": "0", "re1": "1", "im0": "0", "im1": "1",
                         "expected_winding": 1, "prec": 64, "n_per_side": 32,
                         "winding_fn": "demo"})
    inst, _ = certify_winding_box_zero_point(fam, {"case": 0}, "winding_demo")

    class _V:
        instances = [inst]

    em = WindingBoxZeroEmitter()
    body, nthm = em.emit_body(_V())
    print(f"\n-- {nthm} theorems (sidecar only) --\n{body}")
