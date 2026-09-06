"""xi_line_zeros emitter (Stage 1 core): on-line zero count via sign changes + IVT.

Given certified real enclosures of the completed Riemann zeta function
`Lambda = completedRiemannZeta` at sample points `t_0 < t_1 < ... < t_m` on the
critical line `Re s = 1/2`, with ALTERNATING signs, this emitter certifies and
emits a Lean theorem asserting

    Lambda has >= N zeros on the critical line in [a, b],

encoded as: there exist N strictly increasing reals `x_1 < ... < x_N` in `[a, b]`
with `completedRiemannZeta (1/2 + x_k * I) = 0` for every `k`.  N is the number of
sign changes of the sample boxes.

MECHANISM.  On the line, `Lambda(1/2 + t*I)` is REAL (Task-2 kernel prelude
`ZetaZeroLocalization.completedZeta_im_eq_zero`), so it equals its real part
`g t := (completedRiemannZeta (1/2 + t*I)).re` promoted to `ℂ`.  `g` is continuous
(completedRiemannZeta is differentiable away from {0, 1}, and `1/2 + t*I` -- having
real part 1/2 -- is never 0 nor 1).  For each sign-change subinterval `[t_i, t_k]`
with `g t_i < 0 < g t_k` (or the reverse), the intermediate value theorem
(`intermediate_value_Icc` / `intermediate_value_Icc'`) yields a `t*` in `[t_i, t_k]`
with `g t* = 0`, hence `completedRiemannZeta (1/2 + t*·I) = 0`.  Because the box at
each sign-DEFINITE endpoint is strictly nonzero (lo > 0 or hi < 0), the root is
strictly interior (`t_i < t* < t_k`); consecutive sign-change subintervals are
ordered and non-overlapping (adjacent or separated by straddling samples), so
the roots are strictly increasing, hence distinct.

CERTIFICATE (`certify_xi_line_zeros_point`).  Builds the samples via the family
spec, computes `sign_change_count`, and REFUSES (ValueError -> CertificationError)
when it is 0 (nothing to prove -- the negative control).  A box is "positive" if
`lo > 0`, "negative" if `hi < 0`, else STRADDLING (ignored for sign purposes).
Sign changes are counted between consecutive SIGN-DEFINITE boxes.  All arithmetic
is EXACT (fractions.Fraction); Lean literals render via `rat_lean`.

NON-KERNEL INPUT.  The enclosure hypotheses `g t_i in [lo_i, hi_i]` are theorem
HYPOTHESES -- the documented Arb-certified (Task-1 `enclose_lambda`) box membership
of a transcendental value, which Lean does not re-derive.  The emitted proof is the
kernel-honest IVT argument that, GIVEN those enclosures, the zeros exist.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Sign-change counting (exact Fraction boxes)
# ---------------------------------------------------------------------------

def _box_sign(box: tuple[Fraction, Fraction]) -> int:
    """Sign of a real enclosure box: +1 if lo > 0, -1 if hi < 0, else 0 (straddle)."""
    lo, hi = box
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    return 0


def sign_change_count(samples: Sequence[tuple[Fraction, tuple[Fraction, Fraction]]]) -> int:
    """Count sign alternations between consecutive SIGN-DEFINITE boxes.

    ``samples`` is a list ``[(t_i, (lo_i, hi_i)), ...]`` of sample points with their
    real enclosure boxes for ``Lambda(1/2 + t_i*I)``.  A box is "positive" if
    ``lo > 0``, "negative" if ``hi < 0``, else STRADDLING (ignored).  Counts the
    number of positive<->negative transitions between consecutive sign-definite
    boxes (straddling boxes are skipped)."""
    changes = 0
    prev_sign = 0
    for _t, box in samples:
        s = _box_sign(box)
        if s == 0:
            continue
        if prev_sign != 0 and s != prev_sign:
            changes += 1
        prev_sign = s
    return changes


def _sign_change_intervals(
    samples: Sequence[tuple[Fraction, tuple[Fraction, Fraction]]]
) -> list[tuple[int, int]]:
    """Return the list of ``(i, k)`` index pairs (into ``samples``) of each
    sign-change subinterval: ``i`` is a sign-definite sample and ``k`` the NEXT
    sign-definite sample whose sign is opposite.  Consecutive returned intervals
    are ordered and non-overlapping (``k_m <= i_next``); an adjacent pair may
    share the boundary index (back-to-back) or be separated by straddling
    samples, so the resulting roots are strictly increasing either way."""
    intervals: list[tuple[int, int]] = []
    prev_idx = None
    prev_sign = 0
    for idx, (_t, box) in enumerate(samples):
        s = _box_sign(box)
        if s == 0:
            continue
        if prev_sign != 0 and s != prev_sign:
            intervals.append((prev_idx, idx))
        prev_idx = idx
        prev_sign = s
    return intervals


# ---------------------------------------------------------------------------
# Payload + certification
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class XiLineZerosPayload:
    """Certificate payload for one on-line zero-count claim.

    ``a``, ``b`` bound the sweep interval (exact Fractions, ``a <= b``).  ``samples``
    is the ordered list of ``(t_i, (lo_i, hi_i))`` sample points with real enclosure
    boxes.  ``intervals`` is the list of ``(i, k)`` sign-change subinterval index
    pairs (into ``samples``); its length ``n_zeros`` is the certified number of
    distinct on-line zeros.  ``signs`` records ``+1``/``-1`` for each sample (0 for
    straddling), for the emitter's IVT-direction choice."""

    a: Fraction
    b: Fraction
    samples: tuple[tuple[Fraction, tuple[Fraction, Fraction]], ...]
    intervals: tuple[tuple[int, int], ...]
    signs: tuple[int, ...]

    @property
    def n_zeros(self) -> int:
        return len(self.intervals)


def certify_xi_line_zeros_point(family, pt, name):
    """Certify one xi_line_zeros instance from ``family.special[1](pt) ->
    (a, b, samples)``.

    ``samples`` = list of ``(t_i (Fraction), (lo_i, hi_i) (Fraction real box))``.
    Computes ``sign_change_count`` and REFUSES (ValueError -- the negative control)
    when it is 0 (no sign change -> nothing to prove).  Also refuses on a malformed
    box (``lo > hi``), non-increasing sample points, or ``a > b``.  Returns
    ``(CertifiedInstance, n_checks)`` with ``n_checks = 1 + n_zeros`` (the sign-change
    count plus one strict-sign check per certified zero)."""
    a_raw, b_raw, samples_raw = family.special[1](pt)
    a = Fraction(str(sp.Rational(a_raw)))
    b = Fraction(str(sp.Rational(b_raw)))
    if a > b:
        raise ValueError(
            f"xi_line_zeros instance '{name}': interval [a, b] has a={a} > b={b}"
        )
    samples: list[tuple[Fraction, tuple[Fraction, Fraction]]] = []
    prev_t = None
    for t_raw, (lo_raw, hi_raw) in samples_raw:
        t = Fraction(str(sp.Rational(t_raw)))
        lo = Fraction(str(sp.Rational(lo_raw)))
        hi = Fraction(str(sp.Rational(hi_raw)))
        if lo > hi:
            raise ValueError(
                f"xi_line_zeros instance '{name}': box at t={t} has lo={lo} > hi={hi}"
            )
        if prev_t is not None and not (t > prev_t):
            raise ValueError(
                f"xi_line_zeros instance '{name}': sample points must be strictly "
                f"increasing; t={t} follows {prev_t}"
            )
        if not (a <= t <= b):
            raise ValueError(
                f"xi_line_zeros instance '{name}': sample t={t} outside [a, b]=[{a}, {b}]"
            )
        prev_t = t
        samples.append((t, (lo, hi)))

    n = sign_change_count(samples)
    if n == 0:
        raise ValueError(
            f"xi_line_zeros instance '{name}' REFUSED: no sign change among the "
            f"sample boxes; there is nothing to prove (negative control)"
        )
    intervals = _sign_change_intervals(samples)
    signs = tuple(_box_sign(box) for _t, box in samples)
    payload = XiLineZerosPayload(
        a=a,
        b=b,
        samples=tuple(samples),
        intervals=tuple(intervals),
        signs=signs,
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=payload)
    return inst, 1 + len(intervals)


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

# Prelude: the shared `g`/continuity scaffolding, emitted once per file.  `g` is the
# real part of Lambda on the line; `hg_cont` is its continuity; `hLam` rewrites
# `completedRiemannZeta (1/2 + t*I)` back to `(g t : ℂ)` using the Task-2 real-on-line
# prelude.  All three are referenced by every emitted theorem.
XI_LINE_ZEROS_PRELUDE = r"""/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.
noncomputable def gLine (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re

-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).
theorem line_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (0 : ℂ).re := by rw [h]
  simp at hre

theorem line_ne_one (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (1 : ℂ).re := by rw [h]
  simp at hre

-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.
theorem gLine_continuous : Continuous gLine := by
  have hline : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hZeta : Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd : DifferentiableAt ℂ completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
      differentiableAt_completedZeta (line_ne_zero t) (line_ne_one t)
    exact ContinuousAt.comp (g := completedRiemannZeta)
      (f := fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) hd.continuousAt
      (hline.continuousAt (x := t))
  exact Complex.continuous_re.comp hZeta

-- On the line, Lambda equals its real part promoted to ℂ.
theorem lambda_eq_gLine (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = (gLine t : ℂ) := by
  have him : (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).im = 0 :=
    ZetaZeroLocalization.completedZeta_im_eq_zero t
  apply Complex.ext
  · rfl
  · rw [him]; simp [gLine]
"""


@dataclass
class XiLineZerosEmitter(Emitter):
    """Emit one on-line zero-count theorem per instance.

    The theorem states: given the enclosure hypotheses
    ``(completedRiemannZeta (1/2 + t_i*I)).re in [lo_i, hi_i]`` for the sign-definite
    samples and the alternating signs, there exist ``N`` strictly increasing reals in
    ``[a, b]`` at which ``completedRiemannZeta (1/2 + x*I) = 0``.  The proof lifts to
    ``gLine`` (real part of Lambda on the line, real by the Task-2 prelude), uses its
    continuity, and applies the intermediate value theorem on each sign-change
    subinterval.  A statement-match gate is appended, single-sourced with the theorem
    type string."""

    def __post_init__(self):
        self.kind = "xi_line_zeros"
        self.requires_prelude = (
            "gLine", "gLine_continuous", "lambda_eq_gLine",
            "ZetaZeroLocalization.completedZeta_im_eq_zero",
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            payload: XiLineZerosPayload = inst.payload  # type: ignore[assignment]
            body = self._emit_one(inst.lean_name, payload)
            lines.append(body)
            nthm += 1
        return "".join(lines), nthm

    # -- per-instance rendering -------------------------------------------------

    def _emit_one(self, name: str, payload: XiLineZerosPayload) -> str:
        samples = payload.samples
        intervals = payload.intervals
        N = len(intervals)

        # Indices of the sign-definite samples that anchor a sign-change interval.
        anchor_idx = sorted({i for iv in intervals for i in iv})

        def tlit(i: int) -> str:
            return rat_lean(sp.Rational(samples[i][0]))

        def lolit(i: int) -> str:
            return rat_lean(sp.Rational(samples[i][1][0]))

        def hilit(i: int) -> str:
            return rat_lean(sp.Rational(samples[i][1][1]))

        a_s = rat_lean(sp.Rational(payload.a))
        b_s = rat_lean(sp.Rational(payload.b))

        # Enclosure hypotheses (the documented non-kernel Arb input): exactly ONE
        # load-bearing one-sided bound per anchor sample -- the side that pins the
        # sign.  A NEGATIVE anchor (hi < 0) contributes `henc{i} : gLine t_i <= hi_i`
        # (used to derive gLine t_i < 0); a POSITIVE anchor (lo > 0) contributes
        # `henc{i} : lo_i <= gLine t_i` (used to derive 0 < gLine t_i).  The opposite
        # side is never needed, so it is NOT emitted: every hypothesis is genuinely
        # load-bearing (removing any one breaks the proof), and the caller's
        # obligation is exactly the sign-pinning Arb bound, no more.  `hyp_type[i]`
        # is the H_i proposition; anchors are emitted as SIGNATURE binders (not a
        # `forall` + `intro`) and referenced in TERM position in the proof, so the
        # `unusedVariables` linter sees each as used (no suppression needed).
        anchor_sign = {i: payload.signs[i] for i in anchor_idx}
        hyp_type: dict[int, str] = {}
        for i in anchor_idx:
            if anchor_sign[i] < 0:
                hyp_type[i] = f"gLine {tlit(i)} ≤ {hilit(i)}"
            else:
                hyp_type[i] = f"{lolit(i)} ≤ gLine {tlit(i)}"
        sig_binders = " ".join(f"(henc{i} : {hyp_type[i]})" for i in anchor_idx)

        # Conclusion: exists x_1 ... x_N, ordering chain in [a, b] AND each a zero.
        xs = [f"x{m + 1}" for m in range(N)]
        # ordering: a ≤ x1 ∧ x1 < x2 ∧ ... ∧ x_{N-1} < x_N ∧ x_N ≤ b
        order_parts = [f"{a_s} ≤ {xs[0]}"]
        for m in range(N - 1):
            order_parts.append(f"{xs[m]} < {xs[m + 1]}")
        order_parts.append(f"{xs[-1]} ≤ {b_s}")
        order = " ∧ ".join(order_parts)
        zero_parts = [
            f"completedRiemannZeta (1 / 2 + ({x} : ℂ) * Complex.I) = 0" for x in xs
        ]
        zeros = " ∧ ".join(zero_parts)
        exists_binder = " ".join(xs)
        concl = f"∃ {exists_binder} : ℝ, ({order}) ∧ ({zeros})"

        # The statement-match gate ascribes the theorem's type in ARROW form
        # `H0 → H1 → … → concl` (anonymous, so no binder-name warning).  Since
        # `concl` does not mention the henc binders, this is definitionally the
        # theorem's `(henc0 : H0) … : concl` type -- single-sourced with the same
        # `hyp_type` / `concl` used in the signature, so it is a genuine drift net.
        arrow_prefix = "".join(f"{hyp_type[i]} → " for i in anchor_idx)
        gate_type = f"{arrow_prefix}{concl}"

        # ---- proof body ----
        proof: list[str] = []
        root_names = [f"r{m + 1}" for m in range(N)]
        for m, (i, k) in enumerate(intervals):
            rn = root_names[m]
            si = payload.signs[i]
            # si < 0 (neg -> pos): gLine t_i < 0 < gLine t_k, IVT via
            # intermediate_value_Icc.  si > 0 (pos -> neg): gLine t_k < 0 < gLine t_i,
            # IVT via intermediate_value_Icc'.  The strict sign bounds come from the
            # enclosure hyps (hi_i < 0 for a negative box, lo_i > 0 for a positive one).
            proof.append(
                f"  -- sign-change subinterval [{tlit(i)}, {tlit(k)}]: root {rn}\n"
            )
            proof.append(
                f"  have hle{m} : ({tlit(i)} : ℝ) ≤ {tlit(k)} := by norm_num\n"
            )
            proof.append(
                f"  have hcont{m} : ContinuousOn gLine (Set.Icc ({tlit(i)} : ℝ) {tlit(k)}) :=\n"
                f"    gLine_continuous.continuousOn\n"
            )
            if si < 0:
                lo_end, hi_end = i, k  # gLine at lo_end < 0 < gLine at hi_end
                ivt = "intermediate_value_Icc"
            else:
                lo_end, hi_end = k, i  # gLine at lo_end (=t_k) < 0 < gLine at hi_end (=t_i)
                ivt = "intermediate_value_Icc'"
            # strict sign facts (named hneg{m}: gLine t_neg < 0, hpos{m}: 0 < gLine
            # t_pos).  Each derives from the SINGLE load-bearing enclosure hyp of its
            # anchor, re-bound in TERM position (`:= henc{i}`) so the unusedVariables
            # linter counts the signature binder as referenced: the negative anchor's
            # `henc{lo_end}` (gLine <= hi < 0), the positive anchor's `henc{hi_end}`
            # (0 < lo <= gLine).  A given anchor's sign is fixed, so the same hyp is
            # reused if the sample also anchors the adjacent interval.
            proof.append(
                f"  have he_neg{m} : {hyp_type[lo_end]} := henc{lo_end}\n"
                f"  have hneg{m} : gLine {tlit(lo_end)} < 0 := by linarith [he_neg{m}]\n"
            )
            proof.append(
                f"  have he_pos{m} : {hyp_type[hi_end]} := henc{hi_end}\n"
                f"  have hpos{m} : (0 : ℝ) < gLine {tlit(hi_end)} := by linarith [he_pos{m}]\n"
            )
            proof.append(
                f"  have hmem{m} : (0 : ℝ) ∈ gLine '' Set.Icc ({tlit(i)} : ℝ) {tlit(k)} :=\n"
                f"    {ivt} hle{m} hcont{m} ⟨le_of_lt hneg{m}, le_of_lt hpos{m}⟩\n"
            )
            proof.append(f"  obtain ⟨{rn}, hIcc{m}, hz{m}⟩ := hmem{m}\n")
            # Strict interior: root ≠ either endpoint because gLine there is nonzero.
            # hIcc.1 : t_i ≤ r, hIcc.2 : r ≤ t_k.  If r = t_lo_end then gLine r =
            # gLine t_lo_end < 0, contradicting gLine r = 0 (hz).  Similarly hi_end.
            proof.append(
                f"  have hri_lo{m} : ({tlit(i)} : ℝ) < {rn} := by\n"
                f"    rcases lt_or_eq_of_le hIcc{m}.1 with h | h\n"
                f"    · exact h\n"
                f"    · exfalso\n"
                + (
                    f"      rw [← h] at hz{m}; rw [hz{m}] at hneg{m}; exact lt_irrefl 0 hneg{m}\n"
                    if si < 0 else
                    f"      rw [← h] at hz{m}; rw [hz{m}] at hpos{m}; exact lt_irrefl 0 hpos{m}\n"
                )
            )
            proof.append(
                f"  have hri_hi{m} : {rn} < ({tlit(k)} : ℝ) := by\n"
                f"    rcases lt_or_eq_of_le hIcc{m}.2 with h | h\n"
                f"    · exact h\n"
                f"    · exfalso\n"
                + (
                    f"      rw [h] at hz{m}; rw [hz{m}] at hpos{m}; exact lt_irrefl 0 hpos{m}\n"
                    if si < 0 else
                    f"      rw [h] at hz{m}; rw [hz{m}] at hneg{m}; exact lt_irrefl 0 hneg{m}\n"
                )
            )
            # The zero of Lambda at the root.
            proof.append(
                f"  have hLam{m} : completedRiemannZeta (1 / 2 + ({rn} : ℂ) * Complex.I) = 0 := by\n"
                f"    rw [lambda_eq_gLine, hz{m}]; simp\n"
            )

        # Assemble the existential witness: roots, ordering chain, zeros.
        # For each inter-root gap we need r_{m+1} < r_{m+2}.  Whether the
        # bounding intervals are back-to-back (k_m == i_next) or separated
        # (k_m < i_next), the chain is:
        #   r_{m+1} < t_{k_m} <= t_{i_next} < r_{m+2}
        # The middle inequality t_{k_m} <= t_{i_next} is a rational literal
        # comparison discharged by norm_num (trivially when k_m == i_next it
        # is t_k <= t_k, i.e. le_refl, which norm_num also handles).  We emit
        # an intermediate have only when k_m != i_next to keep output concise
        # for the common back-to-back case.
        gap_haves: list[str] = []
        order_terms: list[str] = []
        # a ≤ r1: a ≤ t_{first_i} < r1
        order_terms.append(f"by linarith [hri_lo0]")
        for m in range(N - 1):
            k_m = intervals[m][1]
            i_next = intervals[m + 1][0]
            if k_m == i_next:
                # Back-to-back: r_{m+1} < t_{k_m} = t_{i_next} < r_{m+2}
                order_terms.append(f"by linarith [hri_hi{m}, hri_lo{m + 1}]")
            else:
                # Separated: r_{m+1} < t_{k_m} <= t_{i_next} < r_{m+2}.
                # Emit a numeric gap lemma and use it in linarith.
                gap_haves.append(
                    f"  have hgap{m} : ({tlit(k_m)} : ℝ) ≤ {tlit(i_next)} := by norm_num\n"
                )
                order_terms.append(
                    f"by linarith [hri_hi{m}, hgap{m}, hri_lo{m + 1}]"
                )
        # r_N ≤ b: r_N < t_{last_k} ≤ b
        order_terms.append(f"by linarith [hri_hi{N - 1}]")
        # Insert the gap haves before the final exact (after all IVT haves).
        if gap_haves:
            proof.extend(gap_haves)
        order_anon = "⟨" + ", ".join(order_terms) + "⟩"
        # The zeros component is `hLam0 ∧ ... ∧ hLam{N-1}`; for N == 1 it is a single
        # Prop (no `∧`), so it must NOT be wrapped in an anonymous constructor.
        if N == 1:
            zeros_anon = "hLam0"
        else:
            zeros_anon = "⟨" + ", ".join(f"hLam{m}" for m in range(N)) + "⟩"
        # a ≤ x1 (from a ≤ t_first < r1) and rN ≤ b (from rN < t_last ≤ b): the
        # numeric endpoint facts `a ≤ t_first` / `t_last ≤ b` are rational-literal
        # comparisons that `linarith` discharges itself, so no reflexivity `have`s
        # are needed.
        proof.append(
            f"  exact ⟨{', '.join(root_names)}, {order_anon}, {zeros_anon}⟩\n"
        )

        # Signature-binder form (no `forall` + `intro`): with the term-position
        # references above, every `henc{i}` is a used binder -> warning-free.
        sig = f" {sig_binders}" if sig_binders else ""
        thm = f"theorem {name}{sig} : {concl} := by\n"
        thm += "".join(proof)

        gate = self.emit_gate(name, gate_type)
        out = thm
        if gate:
            out += gate
        out += "\n"
        return out


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def xi_line_zeros_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an xi_line_zeros family (kind='xi_line_zeros').

    ``spec``: a callable ``pt -> (a, b, samples)`` where ``a, b`` are the rational
    sweep-interval bounds and ``samples`` is a list of ``(t_i (Fraction), (lo_i, hi_i)
    (Fraction real box for Lambda(1/2 + i*t_i)))`` in strictly increasing ``t_i``,
    each ``t_i in [a, b]``.  ``certify_xi_line_zeros_point`` counts sign changes and
    REFUSES (ValueError) any point with none (nothing to prove)."""
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("xi_line_zeros", spec),
        constants=dict(constants or {}),
    )
