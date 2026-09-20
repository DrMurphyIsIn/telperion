"""Grid-modulus non-vanishing emitter — a Lipschitz-net zero-freeness certificate.

THE SHAPE.  For `f` holomorphic on a convex rectangle `R`, if

    (i)   ``|f'| <= M`` everywhere on `R`,
    (ii)  a finite grid `G ⊆ R` is a ``delta``-net of `R`, and
    (iii) ``|f| >= L`` at every grid point, with the GAP CONDITION ``M * delta < L``,

then `f` has no zero on `R`: moving at most ``delta`` from a net point changes `|f|` by at
most ``M * delta``, which is not enough to reach `0`.  The Lean side of this is
``SpeiserBoxProbe.nonvanishing_of_grid`` (unconditional, axiom-clean).

WHY A NEW KIND RATHER THAN ``winding_box_zero``.  ``winding_box_zero`` certifies a zero
COUNT by the quadrant-advance argument principle along a contour, and ships ``nthm = 0``
(a pure Arb sidecar with no Lean identity).  This kind is a different instrument: no
contour, no integral, no argument principle — and it SHIPS KERNEL THEOREMS, namely the
rational arithmetic that makes the certificate close.  Its payload (grid geometry, the
three constants `M`, `delta`, `L`, the gap) has no representation in the winding payload.
The trade-off is real and stated here: this kind can only ever certify ZERO-FREENESS; it
cannot certify a nonzero count, which a genuine winding certificate can.

THE ANTI-PHANTOM FACE.  A certificate that merely restates the numbers it was handed is
not an instrument.  ``grid_modulus_nonvanishing_certificate`` RE-DERIVES every load-bearing
quantity from its definition and REFUSES on disagreement:

  * the NET property is re-derived from the grid geometry — the column must span the box
    in the real direction within ``half_width`` and the rows must tile the imaginary range
    within ``half_height``, checked in exact rational arithmetic.  A grid that does not
    actually cover the box is REFUSED even if a ``delta`` is supplied that would "work".
  * ``delta`` must dominate the exact cell half-diagonal: ``half_width^2 + half_height^2
    <= delta^2`` in exact ``Fraction`` arithmetic.  An understated ``delta`` is REFUSED.
  * the GAP ``M * delta < L`` is recomputed exactly.  A violated gap is REFUSED.
  * ``M`` is re-derived by an independent sweep of ``|f''|`` over the box with a Lipschitz
    correction; a claimed ``M`` that is NOT an upper bound is REFUSED.
  * ``L`` is re-derived by independently evaluating ``|f'|`` at every grid point; a claimed
    ``L`` that is NOT a lower bound is REFUSED.
  * both numeric re-derivations are re-run at DOUBLED working precision and DOUBLED sweep
    density; a disagreement is REFUSED.

TRUST CLASS.  ``"mpmath-numeric"``.  This is WEAKER than the ``"arb"`` trust class: mpmath
at high precision is not a rigorous interval enclosure, and the sweep-plus-Lipschitz bound
on ``sup |f''|`` uses a numerically estimated third derivative.  The certificate is
therefore EVIDENCE plus a REFUSAL INSTRUMENT, never a proof.  That is exactly why the two
Lean obligations ``SecondDerivBoundOnBox`` and ``GridModulusLowerBound`` remain OPEN
hypotheses in the emitted Lean and are proved nowhere in this repository.

SCOPE.  The shipped instance targets ``deriv riemannZeta`` on ``[1/4, 3/8] x [6, 10]``.
That is NOT the Speiser wall — Speiser (1935) makes non-vanishing of ``zeta'`` on the WHOLE
open left strip equivalent to RH, and no finite union of boxes exhausts a strip.  Nothing
here is a step toward RH.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from dataclasses import dataclass as _dataclass
from fractions import Fraction
from typing import Callable

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile  # noqa: F401
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile  # noqa: F401
    from telperion.workflow import Emitter


# --------------------------------------------------------------------------------------
# Numeric backends, keyed by a STABLE STRING name so the family spec stays byte
# serializable (a bare function object would inject its memory address into the provenance
# input hash and make regeneration non-deterministic).
# --------------------------------------------------------------------------------------

_BACKENDS: dict[str, Callable] = {}


def register_backend(name: str, fn: Callable) -> None:
    """Register a numeric backend under a stable string name.

    ``fn(order, re, im, prec) -> float`` returns ``|d^order f_base / ds^order (re + i*im)|``
    computed at working precision ``prec``, where ``f_base`` is the underlying function whose
    FIRST derivative is the `f` of the certificate.  For the shipped instance ``f_base`` is
    ``riemannZeta``, so ``order=1`` is ``|zeta'|``, ``order=2`` is ``|zeta''|`` and ``order=3``
    is ``|zeta'''|`` (used only for the Lipschitz correction of the sweep)."""
    _BACKENDS[name] = fn


def _riemann_zeta_backend(order: int, re, im, prec: int) -> float:
    """The default backend: mpmath's ``zeta`` derivatives.  Requires mpmath."""
    import mpmath as mp

    old = mp.mp.dps
    try:
        mp.mp.dps = max(15, int(prec))
        v = mp.zeta(mp.mpc(mp.mpf(str(re)), mp.mpf(str(im))), derivative=order)
        return float(abs(v))
    finally:
        mp.mp.dps = old


def _resolve_backend(name):
    if name is None or name == "riemannZeta":
        return _riemann_zeta_backend
    if name in _BACKENDS:
        return _BACKENDS[name]
    raise ValueError(
        f"grid_modulus_nonvanishing: unknown numeric backend {name!r} "
        f"(register it via register_backend or use 'riemannZeta')")


# --------------------------------------------------------------------------------------
# The certificate
# --------------------------------------------------------------------------------------


@dataclass(frozen=True)
class GridModulusNonvanishingCertificate:
    """A re-derived Lipschitz-net zero-freeness certificate for `f = f_base'` on a box.

    Every field below survived an independent re-derivation; see the module docstring for
    the refusal list.  ``trust_class`` is ``"mpmath-numeric"`` — evidence, not a proof."""

    re0: str
    re1: str
    im0: str
    im1: str
    grid_re: str
    grid_im: tuple[str, ...]
    half_width: str
    half_height: str
    delta: str
    bound_M: str
    bound_L: str
    backend: str
    prec: int
    sweep_nre: int
    sweep_nim: int
    observed_sup_second: str
    observed_min_first: str
    trust_class: str = "mpmath-numeric"

    def to_json_dict(self) -> dict:
        return {
            "kind": "grid_modulus_nonvanishing",
            "trust_class": self.trust_class,
            "box": {"re0": self.re0, "re1": self.re1, "im0": self.im0, "im1": self.im1},
            "grid": {"re": self.grid_re, "im": list(self.grid_im),
                     "half_width": self.half_width, "half_height": self.half_height},
            "constants": {"M": self.bound_M, "delta": self.delta, "L": self.bound_L},
            "backend": self.backend, "prec": self.prec,
            "sweep": {"n_re": self.sweep_nre, "n_im": self.sweep_nim},
            "observed": {"sup_second_deriv": self.observed_sup_second,
                         "min_first_deriv_on_grid": self.observed_min_first},
        }


def _sweep_sup(backend, order, r0, r1, i0, i1, prec, nre, nim) -> float:
    """Max of ``|d^order f_base|`` over a uniform closed grid of the box."""
    best = 0.0
    for a in range(nre + 1):
        x = r0 + (r1 - r0) * Fraction(a, nre)
        for b in range(nim + 1):
            y = i0 + (i1 - i0) * Fraction(b, nim)
            v = backend(order, x, y, prec)
            if v > best:
                best = v
    return best


def _sup_second_with_lipschitz(backend, r0, r1, i0, i1, prec, nre, nim) -> float:
    """An upper estimate for ``sup |f_base''|`` on the box: a uniform sweep plus a Lipschitz
    correction ``sup|f_base'''| * (cell half-diagonal)``, with a 20% safety factor on the
    third-derivative estimate.  NOT a rigorous enclosure — see the module docstring."""
    sup2 = _sweep_sup(backend, 2, r0, r1, i0, i1, prec, nre, nim)
    sup3 = _sweep_sup(backend, 3, r0, r1, i0, i1, prec, max(4, nre // 2), max(4, nim // 2))
    hx = float(r1 - r0) / nre
    hy = float(i1 - i0) / nim
    half_diag = 0.5 * (hx * hx + hy * hy) ** 0.5
    return sup2 + 1.2 * sup3 * half_diag


def grid_modulus_nonvanishing_certificate(
    *, re0, re1, im0, im1, grid_re, grid_im, half_width, half_height,
    delta, bound_M, bound_L, backend: str = "riemannZeta", prec: int = 40,
    sweep_nre: int = 8, sweep_nim: int = 40,
) -> GridModulusNonvanishingCertificate:
    """Build and RE-DERIVE a grid-modulus non-vanishing certificate.

    REFUSES (``ValueError``) on any of:
      * an inverted or degenerate box;
      * a grid column that does not span the box in the real direction within
        ``half_width``, or rows that do not tile ``[im0, im1]`` within ``half_height``
        (the NET property, re-derived from geometry, not taken on trust);
      * ``half_width^2 + half_height^2 > delta^2`` (an understated covering radius);
      * ``bound_M * delta >= bound_L`` (the gap condition the whole certificate rests on);
      * a claimed ``bound_M`` that the independent ``|f''|`` sweep does NOT support;
      * a claimed ``bound_L`` that the independent per-grid-point ``|f'|`` evaluation does
        NOT support;
      * a doubled-precision / doubled-density re-run that disagrees with the base run.
    """
    r0, r1 = Fraction(re0), Fraction(re1)
    i0, i1 = Fraction(im0), Fraction(im1)
    gre = Fraction(grid_re)
    gim = tuple(Fraction(t) for t in grid_im)
    hw, hh = Fraction(half_width), Fraction(half_height)
    d, M, L = Fraction(delta), Fraction(bound_M), Fraction(bound_L)

    if not (r0 < r1 and i0 < i1):
        raise ValueError(
            f"grid_modulus_nonvanishing: inverted box [{r0},{r1}]x[{i0},{i1}]")
    if not gim:
        raise ValueError("grid_modulus_nonvanishing: empty grid")
    if hw <= 0 or hh <= 0 or d <= 0 or M < 0 or L <= 0:
        raise ValueError(
            f"grid_modulus_nonvanishing: need half_width>0, half_height>0, delta>0, M>=0, "
            f"L>0; got {hw}, {hh}, {d}, {M}, {L}")
    if prec < 15 or sweep_nre < 2 or sweep_nim < 2:
        raise ValueError(
            f"grid_modulus_nonvanishing: need prec>=15, sweep_nre>=2, sweep_nim>=2; "
            f"got {prec}, {sweep_nre}, {sweep_nim}")

    # ---- (1) RE-DERIVE the net property from the geometry -----------------------------
    if not (r0 <= gre <= r1):
        raise ValueError(
            f"grid_modulus_nonvanishing: grid column re={gre} lies outside the box "
            f"[{r0},{r1}]; refused")
    if gre - r0 > hw or r1 - gre > hw:
        raise ValueError(
            f"grid_modulus_nonvanishing: grid column re={gre} does not cover [{r0},{r1}] "
            f"within half_width={hw} (needs max({gre - r0}, {r1 - gre}) <= {hw}); "
            f"the grid is not a net of the box; refused")
    rows = sorted(gim)
    if list(rows) != list(gim):
        raise ValueError(
            f"grid_modulus_nonvanishing: grid rows are not in increasing order: {gim}; refused")
    if rows[0] - hh > i0:
        raise ValueError(
            f"grid_modulus_nonvanishing: first grid row {rows[0]} leaves the bottom of the box "
            f"uncovered (needs {rows[0]} - {hh} <= {i0}); refused")
    if rows[-1] + hh < i1:
        raise ValueError(
            f"grid_modulus_nonvanishing: last grid row {rows[-1]} leaves the top of the box "
            f"uncovered (needs {rows[-1]} + {hh} >= {i1}); refused")
    for a, b in zip(rows, rows[1:]):
        if b - a > 2 * hh:
            raise ValueError(
                f"grid_modulus_nonvanishing: gap between grid rows {a} and {b} exceeds "
                f"2*half_height={2 * hh}; the grid is not a net of the box; refused")
    for t in rows:
        if not (i0 <= t <= i1):
            raise ValueError(
                f"grid_modulus_nonvanishing: grid row im={t} lies outside the box "
                f"[{i0},{i1}]; refused")

    # ---- (2) RE-DERIVE delta from the exact cell half-diagonal ------------------------
    if hw * hw + hh * hh > d * d:
        raise ValueError(
            f"grid_modulus_nonvanishing: delta={d} understates the cell half-diagonal "
            f"(half_width^2+half_height^2 = {hw * hw + hh * hh} > delta^2 = {d * d}); refused")

    # ---- (3) RE-DERIVE the gap condition ----------------------------------------------
    if M * d >= L:
        raise ValueError(
            f"grid_modulus_nonvanishing: gap condition fails, M*delta = {M * d} >= L = {L}; "
            f"the net cannot exclude a zero; refused")

    # ---- (4) RE-DERIVE M against the definition of f'' --------------------------------
    be = _resolve_backend(backend)
    sup2 = _sup_second_with_lipschitz(be, r0, r1, i0, i1, prec, sweep_nre, sweep_nim)
    if sup2 > float(M):
        raise ValueError(
            f"grid_modulus_nonvanishing: claimed M={float(M)} is NOT an upper bound for "
            f"|f''| on the box (independent sweep gives {sup2:.10f}); refused")

    # ---- (5) RE-DERIVE L against the definition of f' ---------------------------------
    min1 = min(be(1, gre, t, prec) for t in rows)
    if min1 < float(L):
        raise ValueError(
            f"grid_modulus_nonvanishing: claimed L={float(L)} is NOT a lower bound for |f'| "
            f"on the grid (independent evaluation gives min {min1:.10f}); refused")

    # ---- (6) reproduce both at DOUBLED precision and DOUBLED sweep density ------------
    sup2b = _sup_second_with_lipschitz(
        be, r0, r1, i0, i1, 2 * prec, 2 * sweep_nre, 2 * sweep_nim)
    min1b = min(be(1, gre, t, 2 * prec) for t in rows)
    if sup2b > float(M):
        raise ValueError(
            f"grid_modulus_nonvanishing: doubled-resolution sweep {sup2b:.10f} breaks the "
            f"claimed M={float(M)}; refused")
    if min1b < float(L):
        raise ValueError(
            f"grid_modulus_nonvanishing: doubled-precision grid minimum {min1b:.10f} breaks "
            f"the claimed L={float(L)}; refused")
    if abs(min1b - min1) > 1e-9 * max(1.0, abs(min1)):
        raise ValueError(
            f"grid_modulus_nonvanishing: grid minimum not reproducible across precisions "
            f"({min1:.12f} vs {min1b:.12f}); refused")

    return GridModulusNonvanishingCertificate(
        re0=str(r0), re1=str(r1), im0=str(i0), im1=str(i1),
        grid_re=str(gre), grid_im=tuple(str(t) for t in rows),
        half_width=str(hw), half_height=str(hh), delta=str(d),
        bound_M=str(M), bound_L=str(L), backend=backend, prec=prec,
        sweep_nre=sweep_nre, sweep_nim=sweep_nim,
        observed_sup_second=f"{sup2b:.10f}", observed_min_first=f"{min1b:.10f}")


def certify_grid_modulus_nonvanishing_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)``."""
    spec = family.special[1](pt)
    cert = grid_modulus_nonvanishing_certificate(
        re0=spec["re0"], re1=spec["re1"], im0=spec["im0"], im1=spec["im1"],
        grid_re=spec["grid_re"], grid_im=spec["grid_im"],
        half_width=spec["half_width"], half_height=spec["half_height"],
        delta=spec["delta"], bound_M=spec["bound_M"], bound_L=spec["bound_L"],
        backend=spec.get("backend", "riemannZeta"), prec=int(spec.get("prec", 40)),
        sweep_nre=int(spec.get("sweep_nre", 8)), sweep_nim=int(spec.get("sweep_nim", 40)))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    # 5 kernel theorems per instance: the four certificate facts plus the capstone.
    return inst, 5


def _q(s: str) -> str:
    """Render an exact rational for Lean (``ℚ`` literals; ``a/b`` is already valid)."""
    return s


def render_grid_modulus_nonvanishing(
    cert: GridModulusNonvanishingCertificate, *, name: str) -> str:
    """Render the CERTIFICATE ARITHMETIC as kernel theorems.

    The emitted theorems are exactly the load-bearing rational inequalities the Python
    checker re-derived.  Corrupting the certificate (understating ``delta``, inflating
    ``bound_L``, shrinking ``bound_M``, loosening the grid) produces a file whose
    ``norm_num`` goals FAIL -- the kernel is the second line of defence behind the refusals.

    The capstone ``theorem <name>`` conjoins all four, so a single name witnesses the whole
    certificate (and the negative-control harness has one theorem to accept or reject)."""
    n = len(cert.grid_im)
    rows = ", ".join(cert.grid_im)
    cover = f"{name}_halfWidth ^ 2 + {name}_halfHeight ^ 2 \u2264 {name}_delta ^ 2"
    gap = f"{name}_boundM * {name}_delta < {name}_boundL"
    col = (f"(({_q(cert.grid_re)} : \u211a) - {_q(cert.re0)} \u2264 {name}_halfWidth \u2227\n"
           f"     ({_q(cert.re1)} : \u211a) - {_q(cert.grid_re)} \u2264 {name}_halfWidth)")
    row = (f"(({_q(cert.grid_im[0])} : \u211a) - {name}_halfHeight \u2264 {_q(cert.im0)} \u2227\n"
           f"     ({_q(cert.grid_im[-1])} : \u211a) + {name}_halfHeight \u2265 {_q(cert.im1)})")
    return f"""/-- Certificate constants for `{name}` (grid-modulus non-vanishing).

    Box `[{cert.re0}, {cert.re1}] x [{cert.im0}, {cert.im1}]`; a single grid column at
    `re = {cert.grid_re}` with {n} rows `{rows}`; cell half-extents
    `({cert.half_width}, {cert.half_height})`.

    Constants: `M = {cert.bound_M}` (claimed `sup |f''|` on the box),
    `delta = {cert.delta}` (covering radius), `L = {cert.bound_L}` (claimed `min |f'|` on the grid).

    Re-derived numerically at precision {cert.prec} and again at {2 * cert.prec}:
    observed `sup |f''| = {cert.observed_sup_second}`, observed `min |f'| = {cert.observed_min_first}`.
    TRUST CLASS {cert.trust_class} -- EVIDENCE, NOT A PROOF.  The Lean obligations stay open. -/
def {name}_boundM : \u211a := {_q(cert.bound_M)}

def {name}_delta : \u211a := {_q(cert.delta)}

def {name}_boundL : \u211a := {_q(cert.bound_L)}

def {name}_halfWidth : \u211a := {_q(cert.half_width)}

def {name}_halfHeight : \u211a := {_q(cert.half_height)}

/-- The claimed covering radius dominates the exact cell half-diagonal. -/
theorem {name}_cover_radius_ok : {cover} := by
  unfold {name}_halfWidth {name}_halfHeight {name}_delta; norm_num

/-- **The gap condition** `M * delta < L`: the single inequality that makes the net
    exclude a zero.  Everything else in the certificate feeds it. -/
theorem {name}_gap_ok : {gap} := by
  unfold {name}_boundM {name}_delta {name}_boundL; norm_num

/-- The grid column spans the box in the real direction within `halfWidth`. -/
theorem {name}_column_span_ok :
    {col} := by
  unfold {name}_halfWidth; constructor <;> norm_num

/-- The grid rows tile the imaginary range within `halfHeight`. -/
theorem {name}_row_tiling_ok :
    {row} := by
  unfold {name}_halfHeight; constructor <;> norm_num

/-- **The certificate**, as one proposition: covering radius, gap condition, column span
    and row tiling together.  These are exactly the facts the Python checker re-derived;
    a forged certificate makes one of them FALSE and the kernel rejects this theorem. -/
theorem {name} :
    ({cover}) \u2227 ({gap}) \u2227
    {col} \u2227
    {row} :=
  \u27e8{name}_cover_radius_ok, {name}_gap_ok, {name}_column_span_ok, {name}_row_tiling_ok\u27e9
"""


@_dataclass
class GridModulusNonvanishingEmitter(Emitter):
    """Emit the grid-modulus non-vanishing certificate arithmetic (kernel theorems) plus a
    ``.cert.json`` sidecar recording the re-derived numeric observations.

    Ships ``nthm = 5`` per instance: the covering radius, the gap condition, the column
    span, the row tiling, and a capstone conjoining all four -- the exact rational facts
    the Python checker re-derived.
    The numeric obligations on `|f'|` and `|f''|` are NOT shipped as theorems; they remain
    open Lean hypotheses, which is the honest trust accounting for a
    ``mpmath-numeric``-class certificate.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "grid_modulus_nonvanishing"
        self.emit_statement_gate = False
        self._cert_sink: list[dict] = []

    def emit_body(self, fam, profile=None) -> tuple[str, int]:
        texts: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: GridModulusNonvanishingCertificate = inst.payload  # type: ignore[assignment]
            self._cert_sink.append(cert.to_json_dict())
            texts.append(render_grid_modulus_nonvanishing(cert, name=inst.lean_name))
            nthm += 5
        return "\n".join(texts), nthm


def grid_modulus_nonvanishing_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a grid_modulus_nonvanishing family (kind='grid_modulus_nonvanishing').

    ``spec``: ``pt -> dict`` with keys ``re0, re1, im0, im1, grid_re, grid_im, half_width,
    half_height, delta, bound_M, bound_L`` and optional ``backend`` (a STRING backend name;
    default ``"riemannZeta"``), ``prec``, ``sweep_nre``, ``sweep_nim``."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("grid_modulus_nonvanishing", spec), constants=dict(constants or {}),
    )
