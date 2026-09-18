"""Winding-box-zero emitter — Arb-trust-class winding-number box certificate for a zero.

The rigorous zero-localization sidecar distilled from `arb_dh.certify_offline_zero` /
`arb_dh.winding_number` (QC_DH_SCOUT): for an analytic function `f` and a rational-cornered box on
whose boundary `f` does not vanish, the number of zeros strictly inside equals the winding number
`(1/2π)·Δ_∂box arg f`, computed by sampling `f` in balls at rational boundary nodes and summing
signed quadrant advances.  A returned integer `k` is a RIGOROUS count for the open rectangle.

**This is an Arb-trust-class kind, NOT a kernel theorem** — the same trust class as `turing_band`'s
Arb sidecars.  The emitter therefore produces:

  * a ``.cert.json`` SIDECAR recording the box corners, the boundary edge-sample count, the working
    precision, the certified winding integer, and the ``trust_class = "arb"`` label; and
  * a documentation STUB (a Lean comment block, NO theorem, NO kernel claim) honestly stating the
    trust boundary — mirroring how `campaign.py verify-bands` documents turing_band sidecars.

Self-check (the negative-control discipline for an Arb kind): the winding integer is INDEPENDENTLY
re-run at DOUBLED precision AND DOUBLED boundary density; the two runs must reproduce the SAME integer,
or certification is REFUSED.  A box whose true winding is 0 presented as 1 (or vice versa) either
fails the doubled-resolution reproduction or is caught by the `expected_winding` cross-check.

NEGATIVE CONTROL: a claimed winding that does not match the (re-verified) computed winding — e.g. a
winding-0 box presented as winding-1 — is REFUSED.  conjecture1_proved = False — a finite rigorous
zero-count, nothing about RH.
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


@dataclass(frozen=True)
class WindingBoxZeroCertificate:
    """A verified Arb-trust-class winding-number box certificate.

    ``winding`` is the rigorous zero count for the OPEN rectangle `[re0,re1] × [im0,im1]`, reproduced
    at doubled precision and doubled boundary density.  ``trust_class`` is always ``"arb"`` — this
    certificate is interval-arithmetic-trust, not kernel."""

    re0: str
    re1: str
    im0: str
    im1: str
    prec: int
    n_per_side: int
    edge_samples: int          # 4 · n_per_side
    winding: int
    trust_class: str = "arb"

    def to_json_dict(self) -> dict:
        return {
            "kind": "winding_box_zero", "trust_class": self.trust_class,
            "box": {"re0": self.re0, "re1": self.re1, "im0": self.im0, "im1": self.im1},
            "prec": self.prec, "n_per_side": self.n_per_side,
            "edge_samples": self.edge_samples, "winding": self.winding,
        }


def winding_box_zero_certificate(
    *, re0, re1, im0, im1, expected_winding: int, prec: int = 200, n_per_side: int = 24,
    winding_fn: Callable | None = None,
) -> WindingBoxZeroCertificate:
    """Build and EXACTLY re-verify a winding-box-zero certificate.

    ``winding_fn(re0, re1, im0, im1, prec, n_per_side) -> int`` computes the rigorous winding integer
    (defaults to `arb_dh.winding_number`, which raises on any sign-ambiguous / diagonal-jump node —
    so a returned integer is already rigorous).  Certification computes the winding at the given
    resolution AND re-runs it at DOUBLED precision + DOUBLED density; both must equal
    ``expected_winding``.

    REFUSES (``ValueError`` / propagated ``RuntimeError``):
      * an inverted box (`re0 ≥ re1` or `im0 ≥ im1`), or non-positive `prec`/`n_per_side`;
      * a computed winding ≠ ``expected_winding`` (the negative control: a claimed count the
        argument principle does not support);
      * a doubled-resolution winding that disagrees with the base run (a non-reproducible count);
      * (via ``winding_fn``) any boundary node whose value box straddles an axis or jumps
        diagonally — the count is not rigorous, refine requested.
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
        from .arb_dh import winding_number as winding_fn  # type: ignore[assignment]

    w = winding_fn(r0, r1, i0, i1, prec, n_per_side)
    if w != expected_winding:
        raise ValueError(
            f"winding_box_zero: computed winding {w} ≠ claimed {expected_winding} — the argument "
            f"principle does not support this count (the negative control); refused")
    # INDEPENDENT re-verification at doubled precision AND doubled boundary density.
    w2 = winding_fn(r0, r1, i0, i1, 2 * prec, 2 * n_per_side)
    if w2 != w:
        raise ValueError(
            f"winding_box_zero: doubled-resolution winding {w2} ≠ base {w} — non-reproducible count; "
            f"refused (raise prec / n_per_side)")
    return WindingBoxZeroCertificate(
        re0=str(r0), re1=str(r1), im0=str(i0), im1=str(i1),
        prec=prec, n_per_side=n_per_side, edge_samples=4 * n_per_side, winding=w)


# A registry of winding backends, keyed by a STABLE STRING name so the family spec stays
# byte-serializable (a bare function object in the spec would inject its memory address into the
# provenance input hash, making it non-deterministic).  Production uses "arb_dh" (the default);
# examples / tests register a libflint-free double under their own name.
_WINDING_FNS: dict[str, Callable] = {}


def register_winding_fn(name: str, fn: Callable) -> None:
    """Register a winding backend under a stable string name (for spec-serializable dispatch)."""
    _WINDING_FNS[name] = fn


def _resolve_winding_fn(name):
    if name is None or name == "arb_dh":
        from .arb_dh import winding_number
        return winding_number
    if name in _WINDING_FNS:
        return _WINDING_FNS[name]
    raise ValueError(f"winding_box_zero: unknown winding backend {name!r} "
                     f"(register it via register_winding_fn or use 'arb_dh')")


def certify_winding_box_zero_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys ``re0, re1, im0, im1,
    expected_winding`` and optional ``prec``, ``n_per_side``, ``winding_fn`` (a STRING backend name;
    default ``"arb_dh"``, resolved via ``_resolve_winding_fn``)."""
    spec = family.special[1](pt)
    cert = winding_box_zero_certificate(
        re0=spec["re0"], re1=spec["re1"], im0=spec["im0"], im1=spec["im1"],
        expected_winding=int(spec["expected_winding"]),
        prec=int(spec.get("prec", 200)), n_per_side=int(spec.get("n_per_side", 24)),
        winding_fn=_resolve_winding_fn(spec.get("winding_fn")))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def render_winding_box_zero_stub(cert: WindingBoxZeroCertificate, *, name: str) -> str:
    """Render the documentation STUB (a Lean comment block — NO theorem, NO kernel claim) that
    honestly states the Arb trust boundary, mirroring the turing_band sidecar documentation."""
    return (
        f"/-  {name} — WINDING-BOX-ZERO certificate (Arb-trust-class, NOT kernel).\n"
        f"\n"
        f"    Rigorous winding-number zero count for the OPEN rectangle\n"
        f"        [{cert.re0}, {cert.re1}] × [{cert.im0}, {cert.im1}]:\n"
        f"        winding = {cert.winding}   (i.e. exactly {cert.winding} zero(s) strictly inside).\n"
        f"\n"
        f"    Computed by the argument principle: {cert.edge_samples} rational boundary samples\n"
        f"    ({cert.n_per_side} per side) at working precision {cert.prec}, each evaluated in an Arb\n"
        f"    ball; the signed quadrant advance / 4 is the winding integer.  A sign-ambiguous or\n"
        f"    diagonal-jump node ABORTS (refine), so the integer is rigorous.  RE-VERIFIED at doubled\n"
        f"    precision ({2 * cert.prec}) and doubled density ({2 * cert.n_per_side} per side) —\n"
        f"    both runs reproduce the same integer.\n"
        f"\n"
        f"    TRUST CLASS: {cert.trust_class} (interval arithmetic).  This is a SIDECAR fact\n"
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
    # A pure-Python winding double (no libflint needed): winding = zeros of a supplied analytic f
    # inside the box, computed by the SAME quadrant-advance argument principle as arb_dh.
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

    print("=== positive cert (box around z0=0.5+0.5i, winding 1) ===")
    c = winding_box_zero_certificate(
        re0="0", re1="1", im0="0", im1="1", expected_winding=1,
        prec=64, n_per_side=32, winding_fn=_demo_winding)
    print(f"cert OK: winding={c.winding} trust={c.trust_class} sidecar={c.to_json_dict()}")

    print("\n=== NEGATIVE CONTROL: winding-1 box claimed as winding-0 (must raise) ===")
    try:
        winding_box_zero_certificate(
            re0="0", re1="1", im0="0", im1="1", expected_winding=0,
            prec=64, n_per_side=32, winding_fn=_demo_winding)
        raise SystemExit("FAIL: mismatched winding not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: winding-0 box (z0 outside) claimed as winding-1 (must raise) ===")
    try:
        winding_box_zero_certificate(
            re0="2", re1="3", im0="2", im1="3", expected_winding=1,
            prec=64, n_per_side=32, winding_fn=_demo_winding)
        raise SystemExit("FAIL: winding-0-as-1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted documentation stub (nthm=0, Arb sidecar) ===")
    register_winding_fn("demo", _demo_winding)
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
    print(f"\n-- {nthm} theorems (Arb sidecar) --\n{body}")
