"""Winding-count numeric core + KERNEL emitter (Stage 2A).

Computes the integer winding number of an ordered cycle of complex enclosure boxes
about 0, produces a certificate with per-step half-plane witnesses (numeric core),
and emits a KERNEL-VERIFIED Lean theorem stating that the four-segment boundary
integral of the log-derivative equals ``2*pi*i*N`` (the ``WindingCountEmitter``).

The cycle format matches the output of Task 2's ``enclose_lambda_boundary``:
  list of (param, ((lo_re, hi_re), (lo_im, hi_im))) -- Fraction-valued, closed
  (last sample has the same box as the first).

TWO EMITTED SHAPES (selected by the family spec's ``mode`` key):

  * ``mode="toy_z2"`` -- the from-scratch de-risking instance.  For ``f z = z^2``
    the log-derivative ``f'/f = 2z/z^2`` reduces pointwise to ``2*z^{-1}`` (path
    value nonzero on the boundary), so the four-segment boundary integral of the
    log-derivative equals ``2*(2*pi*i) = 2*pi*i*2``.  Proof: reduce the integrand
    via ``intervalIntegral.integral_congr`` + the pointwise identity, pull the
    constant out, and close with the winding-ONE primitive ``box_inv_winding``
    (the RectWinding segment/``Complex.log`` branch-split proof with pole ``0``).
    NO winding hypothesis -- the winding is proven from scratch.  N = 2.

  * ``mode="lambda"`` -- the completedRiemannZeta instance.  For the box
    ``[2/5,3/5] x [10,35]`` (5 on-line zeros in [10,35]), the boundary integral of
    ``Lambda'/Lambda`` equals ``2*pi*i*5``.  The zeros' LOCATIONS enter as
    hypotheses (the documented Arb-certified enclosure boxes bracketing each zero
    -- ``hin`` gives strict rational interior bounds per pole), together with the
    argument-principle residue decomposition of ``Lambda'/Lambda`` on the boundary
    (``hdb/hdt/hdr/hdl``) and per-side integrability.  The per-pole winding
    ``Bd((z-rho)^{-1}) = 2*pi*i`` is DISCHARGED from the from-scratch interior-pole
    primitive ``rect_winding_lambda`` (no Mathlib gap left open); Finset linearity
    telescopes the four sides to ``2*pi*i*5``.

NON-KERNEL INPUT.  The enclosure boxes (Arb ball arithmetic, Task 1/2) are the
documented non-kernel input.  In ``toy_z2`` they self-certify a winding of 2 (no
Lean hypothesis needed -- ``z^2`` is exact).  In ``lambda`` they enter the emitted
theorem as HYPOTHESES (the strict interior brackets ``hin`` locating each zero,
plus the residue decomposition); a forged enclosure falsifies a hypothesis, leaving
the argument-principle implication kernel-valid.

conjecture1_proved = False (NOT a proof of RH).
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter

# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

# A single sample point from the boundary cycle (output of Task 2).
# param: Fraction in [0,1]
# box: ((lo_re, hi_re), (lo_im, hi_im))  -- all Fraction
_Box = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
_Sample = tuple[Fraction, _Box]


# ---------------------------------------------------------------------------
# Fixed rational test directions for the half-plane witness search.
# Each entry is (d_re, d_im) representing the direction d = d_re + i*d_im.
# The inner product of a complex number w with direction d is Re(conj(d)*w)
# = d_re * w_re + d_im * w_im.
# ---------------------------------------------------------------------------
_DIRECTIONS: tuple[tuple[Fraction, Fraction], ...] = (
    (Fraction(1), Fraction(0)),    # 1
    (Fraction(-1), Fraction(0)),   # -1
    (Fraction(0), Fraction(1)),    # i
    (Fraction(0), Fraction(-1)),   # -i
    (Fraction(1), Fraction(1)),    # 1+i
    (Fraction(1), Fraction(-1)),   # 1-i
    (Fraction(-1), Fraction(1)),   # -1+i
    (Fraction(-1), Fraction(-1)),  # -1-i
)


def _box_corners(box: _Box) -> tuple[
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
]:
    """Return the four corners of a box as (re, im) pairs."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return (
        (lo_re, lo_im),
        (lo_re, hi_im),
        (hi_re, lo_im),
        (hi_re, hi_im),
    )


def _inner_product(d_re: Fraction, d_im: Fraction, w_re: Fraction, w_im: Fraction) -> Fraction:
    """Compute Re(conj(d) * w) = d_re * w_re + d_im * w_im."""
    return d_re * w_re + d_im * w_im


def _half_plane_witness(box_a: _Box, box_b: _Box) -> tuple[Fraction, Fraction] | None:
    """Find a rational direction proving box_a and box_b share an open half-plane.

    Tests the eight fixed rational directions {1, -1, i, -i, 1+i, 1-i, -1+i, -1-i}.
    For each direction d, checks that ALL FOUR corners of BOTH boxes have
    strictly positive real inner product with d (exact Fraction arithmetic).
    Returns the first such direction (d_re, d_im), or None if no direction works.

    A returned witness certifies that ALL points in box_a AND box_b lie in a common
    OPEN half-plane through 0 (an arc of length pi), so the argument of any complex
    number in either box stays within a half-plane and the argument increment
    between the two boxes is strictly less than pi (the winding step is unambiguous).
    """
    corners_a = _box_corners(box_a)
    corners_b = _box_corners(box_b)
    all_corners = corners_a + corners_b

    for d_re, d_im in _DIRECTIONS:
        if all(
            _inner_product(d_re, d_im, w_re, w_im) > Fraction(0)
            for w_re, w_im in all_corners
        ):
            return (d_re, d_im)

    return None


def _box_contains_zero(box: _Box) -> bool:
    """Return True if the box contains 0, i.e. both real and imaginary parts straddle 0."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return lo_re <= Fraction(0) <= hi_re and lo_im <= Fraction(0) <= hi_im


def _box_center(box: _Box) -> tuple[float, float]:
    """Return the float centre of a box as (re, im)."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return (float(lo_re + hi_re) / 2.0, float(lo_im + hi_im) / 2.0)


# ---------------------------------------------------------------------------
# Public numeric API
# ---------------------------------------------------------------------------

def winding_number(samples: Sequence[_Sample]) -> int:
    """Compute the integer winding number of the boundary cycle about 0.

    Algorithm: accumulate the signed argument increment between consecutive
    box CENTRES using atan2 on rational-centre floats.  Divide the total by
    2*pi and round to nearest integer.

    The float accumulation is sufficient for the integer result; exact
    arithmetic lives in the per-step half-plane witnesses.

    ``samples`` must be a closed cycle (last box == first box in content).
    """
    if len(samples) < 2:
        return 0

    total_angle = 0.0
    prev_re, prev_im = _box_center(samples[0][1])

    for _, box in samples[1:]:
        curr_re, curr_im = _box_center(box)
        # Argument increment: arg(curr) - arg(prev) normalised to (-pi, pi]
        # Use atan2(Im(curr * conj(prev)), Re(curr * conj(prev)))
        # = atan2(curr_im*prev_re - curr_re*prev_im, curr_re*prev_re + curr_im*prev_im)
        cross = curr_im * prev_re - curr_re * prev_im
        dot = curr_re * prev_re + curr_im * prev_im
        delta = math.atan2(cross, dot)
        total_angle += delta
        prev_re, prev_im = curr_re, curr_im

    return round(total_angle / (2.0 * math.pi))


@dataclass(frozen=True)
class WindingCountCertificate:
    """A verified winding-count certificate.

    Attributes:
        box: The query box as (lo_re, hi_re, lo_im, hi_im) -- 4 Fractions.
        n: The integer winding number of the boundary cycle about 0.
        step_witnesses: A tuple of length (len(samples)-1) holding the
            half-plane witness for each consecutive pair of boxes, as
            (d_re, d_im) Fraction pairs.
    """

    box: tuple[Fraction, Fraction, Fraction, Fraction]
    n: int
    step_witnesses: tuple[tuple[Fraction, Fraction], ...]


def winding_count_certificate(
    box: tuple,
    samples: Sequence[_Sample],
) -> WindingCountCertificate:
    """Build and self-check a WindingCountCertificate.

    Raises ValueError if:
    - Any sample box contains 0 (Lambda may vanish on the boundary).
    - Any consecutive pair of sample boxes lacks a half-plane witness
      (winding number would be ambiguous for that step).

    Args:
        box: The query box (lo_re, hi_re, lo_im, hi_im) -- used as metadata.
        samples: Closed boundary cycle from Task 2's ``enclose_lambda_boundary``.

    Returns:
        WindingCountCertificate with self-checked witnesses and integer n.
    """
    # Normalise box to 4-tuple of Fraction
    lo_re, hi_re, lo_im, hi_im = (Fraction(v) for v in box)
    cert_box = (lo_re, hi_re, lo_im, hi_im)

    # Check each sample box for 0-containment
    for i, (param, sample_box) in enumerate(samples):
        if _box_contains_zero(sample_box):
            (slo_re, shi_re), (slo_im, shi_im) = sample_box
            raise ValueError(
                f"Sample {i} (param={param}) contains 0: box "
                f"re=[{slo_re}, {shi_re}] im=[{slo_im}, {shi_im}] "
                f"straddles the origin -- winding_count_certificate refuses."
            )

    # Build step witnesses for each consecutive pair
    witnesses: list[tuple[Fraction, Fraction]] = []
    for i in range(len(samples) - 1):
        _, box_a = samples[i]
        _, box_b = samples[i + 1]
        w = _half_plane_witness(box_a, box_b)
        if w is None:
            raise ValueError(
                f"No half-plane witness for step {i}->{i+1}: "
                f"boxes straddle a half-plane through 0; winding is ambiguous."
            )
        witnesses.append(w)

    n = winding_number(samples)
    return WindingCountCertificate(
        box=cert_box,
        n=n,
        step_witnesses=tuple(witnesses),
    )


@dataclass(frozen=True)
class SegmentWindingCertificate:
    """A verified segment-winding certificate.

    Produced by segment_winding_certificate.  Each entry in step_witnesses
    corresponds to a consecutive pair of segment-boxes from the input segments
    list (length == len(segments) - 1).

    Attributes:
        box: The query box as (lo_re, hi_re, lo_im, hi_im) -- 4 Fractions.
        n: The integer winding number of the boundary cycle about 0.
        step_witnesses: Half-plane witness (d_re, d_im) for each consecutive
            pair of segment-boxes.  Certifies the argument increment between
            each pair is unambiguous (stays within a half-plane).

    conjecture1_proved = False.  This is a non-kernel certificate.
    """

    box: tuple[Fraction, Fraction, Fraction, Fraction]
    n: int
    step_witnesses: tuple[tuple[Fraction, Fraction], ...]


def segment_winding_certificate(
    box: tuple,
    segments: "Sequence[_Sample]",
) -> SegmentWindingCertificate:
    """Build and self-check a SegmentWindingCertificate from segment enclosures.

    Reuses the Task-3 winding_number (on segment-box centers) for the candidate
    n, and the Task-3 refusal logic (box-contains-0, per-step half-plane witness)
    applied to the segment boxes.

    Raises ValueError if:
    - Any segment-box contains 0 (both real and imaginary parts straddle 0),
      indicating Lambda may vanish on the boundary segment.
    - Any consecutive pair of segment-boxes lacks a _half_plane_witness,
      meaning the winding step is ambiguous (the argument increment could
      exceed pi).

    Args:
        box: The query rectangle as (lo_re, hi_re, lo_im, hi_im) -- metadata.
        segments: Closed segment cycle from enclose_lambda_segments.  Each
            entry is (param, ((lo_re, hi_re), (lo_im, hi_im))) with Fraction
            values.  The last entry must repeat the first segment-box content.

    Returns:
        SegmentWindingCertificate with self-checked witnesses and integer n.

    Notes:
        conjecture1_proved = False.  The segment boxes are a non-kernel input.
    """
    lo_re, hi_re, lo_im, hi_im = (Fraction(v) for v in box)
    cert_box = (lo_re, hi_re, lo_im, hi_im)

    # Check each segment box for 0-containment.
    for i, (param, seg_box) in enumerate(segments):
        if _box_contains_zero(seg_box):
            (slo_re, shi_re), (slo_im, shi_im) = seg_box
            raise ValueError(
                f"Segment {i} (param={param}) contains 0: box "
                f"re=[{slo_re}, {shi_re}] im=[{slo_im}, {shi_im}] "
                f"straddles the origin -- segment_winding_certificate refuses. "
                f"Use a finer n_per_side."
            )

    # Build step witnesses for each consecutive pair.
    witnesses: list[tuple[Fraction, Fraction]] = []
    for i in range(len(segments) - 1):
        _, box_a = segments[i]
        _, box_b = segments[i + 1]
        w = _half_plane_witness(box_a, box_b)
        if w is None:
            raise ValueError(
                f"No half-plane witness for segment step {i}->{i+1}: "
                f"boxes straddle a half-plane through 0; winding is ambiguous. "
                f"Use a finer n_per_side."
            )
        witnesses.append(w)

    n = winding_number(segments)
    return SegmentWindingCertificate(
        box=cert_box,
        n=n,
        step_witnesses=tuple(witnesses),
    )


# ---------------------------------------------------------------------------
# z^2 boundary samples (toy positive control) -- exact Fraction boxes.
# ---------------------------------------------------------------------------

def _z2_samples(n_per_side: int = 4) -> list[_Sample]:
    """Closed CCW cycle of EXACT enclosure boxes for f(z)=z^2 around [-1,1]^2.

    Each boundary point z has an exact value z^2 (a single point, so a degenerate
    box lo==hi).  Used by the toy certificate to confirm winding = 2 about 0.
    """
    corners_seq: list[tuple[Fraction, Fraction]] = []
    lo, hi = Fraction(-1), Fraction(1)
    n = n_per_side
    # bottom: (-1..1, -1); right: (1, -1..1); top: (1..-1, 1); left: (-1, 1..-1)
    for k in range(n):
        corners_seq.append((lo + (hi - lo) * Fraction(k, n), lo))
    for k in range(n):
        corners_seq.append((hi, lo + (hi - lo) * Fraction(k, n)))
    for k in range(n):
        corners_seq.append((hi + (lo - hi) * Fraction(k, n), hi))
    for k in range(n):
        corners_seq.append((lo, hi + (lo - hi) * Fraction(k, n)))
    corners_seq.append(corners_seq[0])  # close the cycle
    samples: list[_Sample] = []
    total = 4 * n
    for k, (re, im) in enumerate(corners_seq):
        w_re = re * re - im * im       # Re(z^2)
        w_im = 2 * re * im             # Im(z^2)
        param = Fraction(k, total) if k < total else Fraction(0)
        samples.append((param, ((w_re, w_re), (w_im, w_im))))
    return samples


# ---------------------------------------------------------------------------
# Certification entry point
# ---------------------------------------------------------------------------

def certify_winding_count_point(family, pt, name):
    """Certify one winding-count instance from a family evaluated at point ``pt``.

    Expects ``family.special[1](pt)`` to return a dict with keys:
    - ``"box"``: 4-tuple (lo_re, hi_re, lo_im, hi_im)
    - ``"samples"``: closed boundary cycle (list of _Sample)
    - ``"mode"``: "toy_z2" or "lambda" (selects the emitted proof shape)

    Returns (CertifiedInstance, 1).
    """
    spec = family.special[1](pt)
    cert = winding_count_certificate(spec["box"], spec["samples"])
    mode = spec.get("mode", "lambda")
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(cert, mode),
    )
    return inst, 1


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

# Shared prelude: the two monodromy jump helpers (`log(-x) - log x = +-pi*i`),
# emitted once per module.  Referenced by both the toy and Lambda winding-one
# primitives via `linear_combination`.
WINDING_COUNT_PRELUDE = r"""/-!
# Kernel-verified boundary winding count (Stage 2A)

Each theorem below states that the four-segment boundary integral of a
log-derivative around a rectangle equals `2*pi*i*N`.

`winding_z2` is the from-scratch de-risking instance: for `f z = z^2` the
log-derivative `2z/z^2` reduces to `2*z^{-1}`, and the winding-ONE primitive
`box_inv_winding` (segment/`Complex.log` branch-split, pole 0) gives `N = 2`.

`winding_lambda_five` is the completedRiemannZeta instance on `[2/5,3/5]x[10,35]`:
GIVEN the 5 on-line zeros' enclosure brackets (`hin`, the documented Arb non-kernel
input as hypotheses) and the argument-principle residue decomposition of
`Lambda'/Lambda` on the boundary, the boundary integral equals `2*pi*i*5`.  The
per-pole winding is DISCHARGED from the interior-pole primitive `rect_winding_lambda`
(no Mathlib gap); Finset linearity telescopes the four sides.

conjecture1_proved = False.  This localizes a winding count from certified
enclosures; it does NOT prove RH.
-/

-- Monodromy jump: `log(-x) - log x = pi*i` when `Im x < 0` (principal branch).
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

-- Monodromy jump: `log(-x) - log x = -(pi*i)` when `Im x > 0` (principal branch).
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]
"""


@dataclass
class WindingCountEmitter(Emitter):
    """Emit one kernel-verified boundary winding-count theorem per instance.

    The theorem states that the four-segment boundary integral of a log-derivative
    equals ``2*pi*i*N``.  Two shapes (selected by the instance ``mode``):

    * ``toy_z2``: ``Bd(2z/z^2) = 2*pi*i*2`` -- proven from scratch via the winding-ONE
      primitive ``box_inv_winding`` (segment/``Complex.log`` branch-split, pole 0) plus
      a pointwise integrand reduction ``2z/z^2 = 2*z^{-1}`` and constant pull-out.
    * ``lambda``: ``Bd(Lambda'/Lambda) = 2*pi*i*N`` -- GIVEN the N zeros' enclosure
      brackets (``hin``, hypotheses) and the residue decomposition (``hd*``), with the
      per-pole winding discharged from the interior-pole primitive ``rect_winding_lambda``
      and Finset linearity telescoping the four sides.

    A statement-match gate is appended per theorem, single-sourced with the theorem's
    type string.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "winding_count"
        self.requires_prelude = ("log_neg_sub_im_neg", "log_neg_sub_im_pos")

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert, mode = inst.payload  # type: ignore[misc]
            if mode == "toy_z2":
                body, k = self._emit_toy(inst.lean_name, cert)
            else:
                body, k = self._emit_lambda(inst.lean_name, cert)
            lines.append(body)
            nthm += k
        return "".join(lines), nthm

    # -- helpers ---------------------------------------------------------------

    @staticmethod
    def _corners(cert: WindingCountCertificate):
        lo_re, hi_re, lo_im, hi_im = cert.box
        return (
            rat_lean(sp.Rational(lo_re)),
            rat_lean(sp.Rational(hi_re)),
            rat_lean(sp.Rational(lo_im)),
            rat_lean(sp.Rational(hi_im)),
        )

    # -- toy z^2 (from-scratch winding, N=2) -----------------------------------

    def _emit_toy(self, name: str, cert: WindingCountCertificate) -> tuple[str, int]:
        x0, x1, y0, y1 = self._corners(cert)
        N = cert.n  # expected 2
        primitive = f"{name}_box_inv_winding"
        ld = f"{name}_logderiv_sq_eq"
        # winding-ONE primitive Bd((z)^{-1}) = 2*pi*i (pole 0), segment/log split.
        prim = self._winding_one_pole0(primitive, x0, x1, y0, y1)
        # pointwise log-derivative reduction 2w/w^2 = 2*w^{-1}
        ldthm = (
            f"/-- Pointwise: for `w != 0`, the log-derivative of `w^2`, `2*w/w^2`, is `2*w^{{-1}}`. -/\n"
            f"theorem {ld} (w : ℂ) (hw : w ≠ 0) : 2 * w / w ^ 2 = 2 * w⁻¹ := by\n"
            f"  field_simp\n\n"
        )
        # the toy theorem type (log-derivative boundary integral = 2*pi*i*N)
        thm_type = (
            f"(∫ x in ({x0} : ℝ)..{x1}, 2 * (↑x + (({y0} : ℝ) : ℂ) * I) / (↑x + (({y0} : ℝ) : ℂ) * I) ^ 2)\n"
            f"        - (∫ x in ({x0} : ℝ)..{x1}, 2 * (↑x + (({y1} : ℝ) : ℂ) * I) / (↑x + (({y1} : ℝ) : ℂ) * I) ^ 2)\n"
            f"        + I • (∫ y in ({y0} : ℝ)..{y1}, 2 * ((({x1} : ℝ) : ℂ) + ↑y * I) / ((({x1} : ℝ) : ℂ) + ↑y * I) ^ 2)\n"
            f"        - I • (∫ y in ({y0} : ℝ)..{y1}, 2 * ((({x0} : ℝ) : ℂ) + ↑y * I) / ((({x0} : ℝ) : ℂ) + ↑y * I) ^ 2)\n"
            f"      = 2 * ↑π * I * {N}"
        )
        thm = (
            f"/-- TOY winding-count theorem (`f z = z^2`, `N = {N}` on `[{x0},{x1}]x[{y0},{y1}]`).\n"
            f"    The four-segment boundary integral of the log-derivative `f'/f = 2z/z^2`\n"
            f"    equals `2*pi*i*{N}`.  The integrand reduces pointwise to `2*z^{{-1}}` (path value\n"
            f"    nonzero on the boundary); the winding-ONE primitive + linearity closes it. -/\n"
            f"theorem {name} :\n    {thm_type} := by\n"
            f"  have hbot_ne : ∀ x : ℝ, (↑x + (({y0} : ℝ) : ℂ) * I) ≠ 0 := by\n"
            f"    intro x h\n"
            f"    have : ((↑x + (({y0} : ℝ) : ℂ) * I)).im = (0 : ℂ).im := by rw [h]\n"
            f"    simp at this\n"
            f"  have htop_ne : ∀ x : ℝ, (↑x + (({y1} : ℝ) : ℂ) * I) ≠ 0 := by\n"
            f"    intro x h\n"
            f"    have : ((↑x + (({y1} : ℝ) : ℂ) * I)).im = (0 : ℂ).im := by rw [h]\n"
            f"    simp at this\n"
            f"  have hright_ne : ∀ y : ℝ, ((({x1} : ℝ) : ℂ) + ↑y * I) ≠ 0 := by\n"
            f"    intro y h\n"
            f"    have : (((({x1} : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]\n"
            f"    simp at this\n"
            f"  have hleft_ne : ∀ y : ℝ, ((({x0} : ℝ) : ℂ) + ↑y * I) ≠ 0 := by\n"
            f"    intro y h\n"
            f"    have : (((({x0} : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]\n"
            f"    simp at this\n"
            f"  have ebot : (∫ x in ({x0} : ℝ)..{x1}, 2 * (↑x + (({y0} : ℝ) : ℂ) * I) / (↑x + (({y0} : ℝ) : ℂ) * I) ^ 2)\n"
            f"      = ∫ x in ({x0} : ℝ)..{x1}, 2 * ((↑x + (({y0} : ℝ) : ℂ) * I) - 0)⁻¹ := by\n"
            f"    apply intervalIntegral.integral_congr\n"
            f"    intro x _; simp only [sub_zero]; exact {ld} _ (hbot_ne x)\n"
            f"  have etop : (∫ x in ({x0} : ℝ)..{x1}, 2 * (↑x + (({y1} : ℝ) : ℂ) * I) / (↑x + (({y1} : ℝ) : ℂ) * I) ^ 2)\n"
            f"      = ∫ x in ({x0} : ℝ)..{x1}, 2 * ((↑x + (({y1} : ℝ) : ℂ) * I) - 0)⁻¹ := by\n"
            f"    apply intervalIntegral.integral_congr\n"
            f"    intro x _; simp only [sub_zero]; exact {ld} _ (htop_ne x)\n"
            f"  have eright : (∫ y in ({y0} : ℝ)..{y1}, 2 * ((({x1} : ℝ) : ℂ) + ↑y * I) / ((({x1} : ℝ) : ℂ) + ↑y * I) ^ 2)\n"
            f"      = ∫ y in ({y0} : ℝ)..{y1}, 2 * (((({x1} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by\n"
            f"    apply intervalIntegral.integral_congr\n"
            f"    intro y _; simp only [sub_zero]; exact {ld} _ (hright_ne y)\n"
            f"  have eleft : (∫ y in ({y0} : ℝ)..{y1}, 2 * ((({x0} : ℝ) : ℂ) + ↑y * I) / ((({x0} : ℝ) : ℂ) + ↑y * I) ^ 2)\n"
            f"      = ∫ y in ({y0} : ℝ)..{y1}, 2 * (((({x0} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by\n"
            f"    apply intervalIntegral.integral_congr\n"
            f"    intro y _; simp only [sub_zero]; exact {ld} _ (hleft_ne y)\n"
            f"  rw [ebot, etop, eright, eleft]\n"
            f"  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,\n"
            f"    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,\n"
            f"    smul_eq_mul, smul_eq_mul]\n"
            f"  have key := {primitive}\n"
            f"  rw [smul_eq_mul, smul_eq_mul] at key\n"
            f"  linear_combination ({N} : ℂ) * key\n"
        )
        gate = self.emit_gate(name, thm_type)
        out = prim + "\n" + ldthm + thm
        if gate:
            out += gate
        out += "\n"
        # 3 theorems: primitive, log-deriv reduction, main.
        return out, 3

    def _winding_one_pole0(self, name, x0, x1, y0, y1) -> str:
        """Winding-ONE primitive `Bd((z-0)^{-1}) = 2*pi*i` on [x0,x1]x[y0,y1]."""
        return (
            f"/-- Winding number ONE about 0: `Bd((z)^{{-1}}) = 2*pi*i` on `[{x0},{x1}]x[{y0},{y1}]`.\n"
            f"    Segment/`Complex.log` branch-split proof (RectWinding with pole 0). -/\n"
            f"theorem {name} :\n"
            f"    (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y0} : ℝ) : ℂ) * I) - 0)⁻¹)\n"
            f"        - (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y1} : ℝ) : ℂ) * I) - 0)⁻¹)\n"
            f"        + I • (∫ y in ({y0} : ℝ)..{y1}, (((({x1} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)\n"
            f"        - I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)\n"
            f"      = 2 * ↑π * I := by\n"
            f"  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - 0).im ≠ 0) →\n"
            f"      (∫ x in ({x0} : ℝ)..{x1}, ((↑x + c) - 0)⁻¹)\n"
            f"        = Complex.log ((↑({x1} : ℝ) + c) - 0) - Complex.log ((↑({x0} : ℝ) + c) - 0) := by\n"
            f"    intro c hc\n"
            f"    have hderiv : ∀ x ∈ Set.uIcc ({x0} : ℝ) {x1},\n"
            f"        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - 0)) (((↑x + c) - 0)⁻¹) x := by\n"
            f"      intro x _\n"
            f"      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - 0) 1 x := by\n"
            f"        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp\n"
            f"        exact (h1.add_const c).sub_const 0\n"
            f"      have hslit : ((↑x + c) - 0) ∈ Complex.slitPlane := by\n"
            f"        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)\n"
            f"      have hd := hpath.clog_real hslit\n"
            f"      rwa [one_div] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)\n"
            f"    rw [sub_ne_zero]; intro h\n"
            f"    exact hc x (by rw [h]; simp)\n"
            f"  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - 0) ∈ Complex.slitPlane) →\n"
            f"      I • (∫ y in ({y0} : ℝ)..{y1}, ((c + ↑y * I) - 0)⁻¹)\n"
            f"        = Complex.log ((c + ↑({y1} : ℝ) * I) - 0) - Complex.log ((c + ↑({y0} : ℝ) * I) - 0) := by\n"
            f"    intro c hslit\n"
            f"    rw [← intervalIntegral.integral_smul]\n"
            f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
            f"        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - 0)) (I • ((c + ↑y * I) - 0)⁻¹) y := by\n"
            f"      intro y _\n"
            f"      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - 0) I y := by\n"
            f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
            f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
            f"        exact (h2.const_add c).sub_const 0\n"
            f"      have hd := hpath.clog_real (hslit y)\n"
            f"      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
            f"    have := hslit y\n"
            f"    rw [Complex.mem_slitPlane_iff] at this\n"
            f"    intro h; rw [h] at this; simp at this\n"
            f"  have hbot := horiz ((({y0} : ℝ) : ℂ) * I) (by\n"
            f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num)\n"
            f"  have htop := horiz ((({y1} : ℝ) : ℂ) * I) (by\n"
            f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num)\n"
            f"  have hright := vert (({x1} : ℝ) : ℂ) (by\n"
            f"    intro y; rw [Complex.mem_slitPlane_iff]; left\n"
            f"    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_im]; norm_num)\n"
            f"  have hleftJ : I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹)\n"
            f"      = Complex.log (0 - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I))"
            f" - Complex.log (0 - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)) := by\n"
            f"    rw [← intervalIntegral.integral_smul]\n"
            f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
            f"        HasDerivAt (fun y : ℝ => Complex.log (0 - ((({x0} : ℝ) : ℂ) + ↑y * I)))\n"
            f"          (I • (((({x0} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹) y := by\n"
            f"      intro y _\n"
            f"      have hpath : HasDerivAt (fun y : ℝ => 0 - ((({x0} : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by\n"
            f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
            f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
            f"        exact (h2.const_add (((({x0} : ℝ) : ℂ)))).const_sub 0\n"
            f"      have hslit : (0 - ((({x0} : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by\n"
            f"        rw [Complex.mem_slitPlane_iff]; left\n"
            f"        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"          Complex.I_re, Complex.I_im, Complex.ofReal_im]; norm_num\n"
            f"      have hd := hpath.clog_real hslit\n"
            f"      have hval : (-I) / (0 - ((({x0} : ℝ) : ℂ) + ↑y * I))"
            f" = I • (((({x0} : ℝ) : ℂ) + ↑y * I) - 0)⁻¹ := by\n"
            f"        rw [smul_eq_mul, div_eq_mul_inv,\n"
            f"          show (0 : ℂ) - ((({x0} : ℝ) : ℂ) + ↑y * I)"
            f" = -(((({x0} : ℝ) : ℂ) + ↑y * I) - 0) from by ring, inv_neg]\n"
            f"        ring\n"
            f"      rwa [hval] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
            f"    rw [sub_ne_zero]; intro h\n"
            f"    have : (((({x0} : ℝ) : ℂ) + ↑y * I)).re = (0 : ℂ).re := by rw [h]\n"
            f"    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this\n"
            f"  rw [hbot, htop, hright, hleftJ,\n"
            f"    show (0 : ℂ) - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I)"
            f" = -((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - 0) from by ring,\n"
            f"    show (0 : ℂ) - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)"
            f" = -((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - 0) from by ring]\n"
            f"  have hAim : ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - 0).im < 0 := by\n"
            f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num\n"
            f"  have hDim : 0 < ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - 0).im := by\n"
            f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; norm_num\n"
            f"  linear_combination log_neg_sub_im_neg ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - 0) hAim\n"
            f"    - log_neg_sub_im_pos ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - 0) hDim\n"
        )

    # -- Lambda (argument-principle, N poles) ----------------------------------

    def _emit_lambda(self, name: str, cert: WindingCountCertificate) -> tuple[str, int]:
        x0, x1, y0, y1 = self._corners(cert)
        N = cert.n  # expected 5
        primitive = f"{name}_rect_winding"
        prim = self._winding_one_interior(primitive, x0, x1, y0, y1)
        # theorem type (Lambda'/Lambda boundary integral = 2*pi*i*N)
        thm_type = (
            f"(∫ x in ({x0} : ℝ)..{x1}, Ld (↑x + (({y0} : ℝ) : ℂ) * I))\n"
            f"        - (∫ x in ({x0} : ℝ)..{x1}, Ld (↑x + (({y1} : ℝ) : ℂ) * I))\n"
            f"        + I • (∫ y in ({y0} : ℝ)..{y1}, Ld ((({x1} : ℝ) : ℂ) + ↑y * I))\n"
            f"        - I • (∫ y in ({y0} : ℝ)..{y1}, Ld ((({x0} : ℝ) : ℂ) + ↑y * I))\n"
            f"      = 2 * ↑π * I * {N}"
        )
        # Value binders (named; the conclusion and hypotheses reference them) and the
        # propositional hypothesis (name, type) pairs.  The theorem SIGNATURE renders
        # each hyp as a named binder `(hname : htype)`; the statement-match GATE renders
        # the value binders named + the hyp TYPES as anonymous `→` arrows (so no
        # unusedVariables warning on the gate's hyp binder names -- the same pattern
        # as XiLineZerosEmitter).
        value_binders = "(Ld : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℤ)"
        hyps: list[tuple[str, str]] = [
            ("hcard", f"s.card = {N}"),
            ("hm", "∀ ρ ∈ s, m ρ = 1"),
            ("hin", f"∀ ρ ∈ s, ({x0} : ℝ) < ρ.re ∧ ρ.re < {x1} ∧ ({y0} : ℝ) < ρ.im ∧ ρ.im < {y1}"),
            ("hb", f"∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹) volume ({x0}) ({x1})"),
            ("ht", f"∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹) volume ({x0}) ({x1})"),
            ("hr", f"∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ({y0}) ({y1})"),
            ("hl", f"∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ({y0}) ({y1})"),
            ("hdb", f"∀ x : ℝ, Ld (↑x + (({y0} : ℝ) : ℂ) * I) ="
                    f" ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹"),
            ("hdt", f"∀ x : ℝ, Ld (↑x + (({y1} : ℝ) : ℂ) * I) ="
                    f" ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹"),
            ("hdr", f"∀ y : ℝ, Ld ((({x1} : ℝ) : ℂ) + ↑y * I) ="
                    f" ∑ ρ ∈ s, (m ρ : ℂ) * (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹"),
            ("hdl", f"∀ y : ℝ, Ld ((({x0} : ℝ) : ℂ) + ↑y * I) ="
                    f" ∑ ρ ∈ s, (m ρ : ℂ) * (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹"),
        ]
        sig = "    " + value_binders + "\n" + "\n".join(
            f"    ({hn} : {ht})" for hn, ht in hyps
        )
        thm = (
            f"/-- Λ boundary log-derivative winding count on `[{x0},{x1}]x[{y0},{y1}]`, `N = {N}`.\n"
            f"    GIVEN the {N} zeros' enclosure brackets (`hin`, the documented Arb non-kernel\n"
            f"    input as hypotheses) and the argument-principle residue decomposition of\n"
            f"    `Lambda'/Lambda` on the boundary (`hd*`), the boundary integral equals\n"
            f"    `2*pi*i*{N}`.  The per-pole winding `Bd((z-ρ)^{{-1}}) = 2*pi*i` is DISCHARGED\n"
            f"    from the interior-pole primitive `{primitive}`; Finset linearity telescopes\n"
            f"    the four sides.  conjecture1_proved = False. -/\n"
            f"theorem {name}\n{sig} :\n    {thm_type} := by\n"
            f"  have eb : (∫ x in ({x0} : ℝ)..{x1}, Ld (↑x + (({y0} : ℝ) : ℂ) * I))\n"
            f"      = ∫ x in ({x0} : ℝ)..{x1}, ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹ :=\n"
            f"    intervalIntegral.integral_congr (fun x _ => hdb x)\n"
            f"  have et : (∫ x in ({x0} : ℝ)..{x1}, Ld (↑x + (({y1} : ℝ) : ℂ) * I))\n"
            f"      = ∫ x in ({x0} : ℝ)..{x1}, ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹ :=\n"
            f"    intervalIntegral.integral_congr (fun x _ => hdt x)\n"
            f"  have er : (∫ y in ({y0} : ℝ)..{y1}, Ld ((({x1} : ℝ) : ℂ) + ↑y * I))\n"
            f"      = ∫ y in ({y0} : ℝ)..{y1}, ∑ ρ ∈ s, (m ρ : ℂ) * (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ :=\n"
            f"    intervalIntegral.integral_congr (fun y _ => hdr y)\n"
            f"  have el : (∫ y in ({y0} : ℝ)..{y1}, Ld ((({x0} : ℝ) : ℂ) + ↑y * I))\n"
            f"      = ∫ y in ({y0} : ℝ)..{y1}, ∑ ρ ∈ s, (m ρ : ℂ) * (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ :=\n"
            f"    intervalIntegral.integral_congr (fun y _ => hdl y)\n"
            f"  rw [eb, et, er, el]\n"
            f"  rw [intervalIntegral.integral_finsetSum (μ := volume) (a := ({x0}:ℝ)) (b := ({x1}:ℝ)) (s := s)\n"
            f"        (f := fun (ρ : ℂ) (x : ℝ) => (m ρ : ℂ) * ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),\n"
            f"      intervalIntegral.integral_finsetSum (μ := volume) (a := ({x0}:ℝ)) (b := ({x1}:ℝ)) (s := s)\n"
            f"        (f := fun (ρ : ℂ) (x : ℝ) => (m ρ : ℂ) * ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),\n"
            f"      intervalIntegral.integral_finsetSum (μ := volume) (a := ({y0}:ℝ)) (b := ({y1}:ℝ)) (s := s)\n"
            f"        (f := fun (ρ : ℂ) (y : ℝ) => (m ρ : ℂ) * (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
            f"        (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),\n"
            f"      intervalIntegral.integral_finsetSum (μ := volume) (a := ({y0}:ℝ)) (b := ({y1}:ℝ)) (s := s)\n"
            f"        (f := fun (ρ : ℂ) (y : ℝ) => (m ρ : ℂ) * (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
            f"        (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]\n"
            f"  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]\n"
            f"  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]\n"
            f"  have hsum : (∑ ρ ∈ s,\n"
            f"      ((m ρ : ℂ) * (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        - (m ρ : ℂ) * (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        + I * ((m ρ : ℂ) * (∫ y in ({y0} : ℝ)..{y1}, (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹))\n"
            f"        - I * ((m ρ : ℂ) * (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹))))\n"
            f"      = ∑ _ρ ∈ s, (2 * ↑π * I : ℂ) := by\n"
            f"    apply Finset.sum_congr rfl\n"
            f"    intro ρ hρ\n"
            f"    obtain ⟨hre0, hre1, him0, him1⟩ := hin ρ hρ\n"
            f"    have hw := {primitive} ρ hre0 hre1 him0 him1\n"
            f"    rw [smul_eq_mul, smul_eq_mul] at hw\n"
            f"    rw [hm ρ hρ, Int.cast_one]\n"
            f"    linear_combination hw\n"
            f"  rw [hsum, Finset.sum_const, hcard]\n"
            f"  simp only [nsmul_eq_mul]\n"
            f"  push_cast\n"
            f"  ring\n"
        )
        # The statement-match gate ascribes the FULL dependent theorem type: the value
        # binders (Ld, s, m) are NAMED (the conclusion references them), the propositional
        # hypotheses are ANONYMOUS `→` arrows (their binder names are unused, so no
        # unusedVariables warning).  Single-sourced from the SAME value_binders / hyps /
        # thm_type used in the signature, so it stays a genuine drift net.
        # Parenthesise each hypothesis type: a bare `∀ ρ ∈ s, P` followed by `→ Q`
        # would otherwise parse as `∀ ρ ∈ s, (P → Q)` (binder captures the arrow).
        arrow_hyps = "".join(f"({ht}) → " for _hn, ht in hyps)
        gate_type = f"∀ {value_binders}, {arrow_hyps}{thm_type}"
        gate = self.emit_gate(name, gate_type)
        out = prim + "\n" + thm
        if gate:
            out += gate
        out += "\n"
        # 2 theorems: interior-pole primitive, main.
        return out, 2

    def _winding_one_interior(self, name, x0, x1, y0, y1) -> str:
        """Winding-ONE primitive `Bd((z-ρ)^{-1}) = 2*pi*i` for interior ρ on the box."""
        return (
            f"/-- Winding number ONE about an interior pole ρ of `[{x0},{x1}]x[{y0},{y1}]`:\n"
            f"    `Bd((z-ρ)^{{-1}}) = 2*pi*i`.  Segment/`Complex.log` branch-split proof. -/\n"
            f"theorem {name} (ρ : ℂ)\n"
            f"    (hre0 : ({x0} : ℝ) < ρ.re) (hre1 : ρ.re < {x1})\n"
            f"    (him0 : ({y0} : ℝ) < ρ.im) (him1 : ρ.im < {y1}) :\n"
            f"    (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        - (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
            f"        + I • (∫ y in ({y0} : ℝ)..{y1}, (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
            f"        - I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
            f"      = 2 * ↑π * I := by\n"
            f"  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →\n"
            f"      (∫ x in ({x0} : ℝ)..{x1}, ((↑x + c) - ρ)⁻¹)\n"
            f"        = Complex.log ((↑({x1} : ℝ) + c) - ρ) - Complex.log ((↑({x0} : ℝ) + c) - ρ) := by\n"
            f"    intro c hc\n"
            f"    have hderiv : ∀ x ∈ Set.uIcc ({x0} : ℝ) {x1},\n"
            f"        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - ρ)) (((↑x + c) - ρ)⁻¹) x := by\n"
            f"      intro x _\n"
            f"      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - ρ) 1 x := by\n"
            f"        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp\n"
            f"        exact (h1.add_const c).sub_const ρ\n"
            f"      have hslit : ((↑x + c) - ρ) ∈ Complex.slitPlane := by\n"
            f"        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)\n"
            f"      have hd := hpath.clog_real hslit\n"
            f"      rwa [one_div] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)\n"
            f"    rw [sub_ne_zero]; intro h\n"
            f"    exact hc x (by rw [h]; simp)\n"
            f"  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - ρ) ∈ Complex.slitPlane) →\n"
            f"      I • (∫ y in ({y0} : ℝ)..{y1}, ((c + ↑y * I) - ρ)⁻¹)\n"
            f"        = Complex.log ((c + ↑({y1} : ℝ) * I) - ρ) - Complex.log ((c + ↑({y0} : ℝ) * I) - ρ) := by\n"
            f"    intro c hslit\n"
            f"    rw [← intervalIntegral.integral_smul]\n"
            f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
            f"        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - ρ)) (I • ((c + ↑y * I) - ρ)⁻¹) y := by\n"
            f"      intro y _\n"
            f"      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - ρ) I y := by\n"
            f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
            f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
            f"        exact (h2.const_add c).sub_const ρ\n"
            f"      have hd := hpath.clog_real (hslit y)\n"
            f"      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
            f"    have := hslit y\n"
            f"    rw [Complex.mem_slitPlane_iff] at this\n"
            f"    intro h; rw [h] at this; simp at this\n"
            f"  have hbot := horiz ((({y0} : ℝ) : ℂ) * I) (by\n"
            f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)\n"
            f"  have htop := horiz ((({y1} : ℝ) : ℂ) * I) (by\n"
            f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)\n"
            f"  have hright := vert (({x1} : ℝ) : ℂ) (by\n"
            f"    intro y; rw [Complex.mem_slitPlane_iff]; left\n"
            f"    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)\n"
            f"  have hleftJ : I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
            f"      = Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I))"
            f" - Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)) := by\n"
            f"    rw [← intervalIntegral.integral_smul]\n"
            f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
            f"        HasDerivAt (fun y : ℝ => Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)))\n"
            f"          (I • (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) y := by\n"
            f"      intro y _\n"
            f"      have hpath : HasDerivAt (fun y : ℝ => ρ - ((({x0} : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by\n"
            f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
            f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
            f"        exact (h2.const_add ((({x0} : ℝ) : ℂ))).const_sub ρ\n"
            f"      have hslit : (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by\n"
            f"        rw [Complex.mem_slitPlane_iff]; left\n"
            f"        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith\n"
            f"      have hd := hpath.clog_real hslit\n"
            f"      have hval : (-I) / (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I))"
            f" = I • (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ := by\n"
            f"        rw [smul_eq_mul, div_eq_mul_inv,\n"
            f"          show ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)"
            f" = -(((({x0} : ℝ) : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]\n"
            f"        ring\n"
            f"      rwa [hval] at hd\n"
            f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
            f"    apply Continuous.intervalIntegrable\n"
            f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
            f"    rw [sub_ne_zero]; intro h\n"
            f"    have : (((({x0} : ℝ) : ℂ) + ↑y * I)).re = ρ.re := by rw [h]\n"
            f"    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith\n"
            f"  rw [hbot, htop, hright, hleftJ,\n"
            f"    show ρ - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I)"
            f" = -((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ) from by ring,\n"
            f"    show ρ - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)"
            f" = -((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ) from by ring]\n"
            f"  have hAim : ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ).im < 0 := by\n"
            f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith\n"
            f"  have hDim : 0 < ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ).im := by\n"
            f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
            f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith\n"
            f"  linear_combination log_neg_sub_im_neg ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ) hAim\n"
            f"    - log_neg_sub_im_pos ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ) hDim\n"
        )


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def winding_count_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a winding-count family (kind='winding_count').

    ``spec``: a callable ``pt -> {"box", "samples", "mode"}`` where ``box`` is the
    4-tuple ``(lo_re, hi_re, lo_im, hi_im)``, ``samples`` is the closed boundary
    cycle (Task 2 format), and ``mode`` is ``"toy_z2"`` or ``"lambda"``.
    ``certify_winding_count_point`` refuses (ValueError) a 0-containing sample box
    or a step lacking a half-plane witness (the winding would be ambiguous)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("winding_count", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== toy z^2 winding certificate (expect n=2) ===")
    toy = winding_count_certificate((-1, 1, -1, 1), _z2_samples())
    print(f"n = {toy.n}, steps = {len(toy.step_witnesses)}")
