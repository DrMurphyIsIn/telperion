"""Window-form-floor emitter -- Zhu's one-stroke window reduction as a certificate shape.

Xuefeng Zhu, arXiv:2608.24827 (v2, 2026-09-02), "Weil positivity in compact windows: a finite
reduction, certified two-sided bounds, and a Landau-Widom decay law", Theorem 1.1, proves: for
`L > 0` and `T#` with

    beta* := log(T# / 2pi) - 1/T# - A_L  >  0,       A_L = sum_{log n < 2L} 2 Lambda(n)/sqrt n,

if the leading `N x N` block of the reduced form `R` in the Legendre basis of `L^2[-L, L]`, cut
after `N` even modes with first discarded order `2N >~ e L T# / 2`, has `lambda_min >= lam0 > 0`,
then for every real even `f` with `supp f subset [-L, L]`

    Q(f)  >=  ( min(lam0, beta* - epsD) - epsB ) ||f||_2^2,

with `epsD` (tail-block deviation) and `epsB` (leading-tail coupling norm) explicit and
super-exponentially small.  Executed at `L = 0.8` (Theorem 1.2) this gives
`Q(f) >= 8.9e-18 ||f||_2^2`, i.e. unconditional Weil positivity on autocorrelation support `1.6`,
`2.3x` the classical `(log 2)/2` range of Yoshida and Connes-Consani.

THE SHAPE THAT HAD NO CERTIFICATE TYPE
--------------------------------------
Nothing in the registry lifts a FINITE certified block floor to a floor on an INFINITE-dimensional
form while carrying the lift's tail constants and the reduction's threshold constant explicitly:

  * ``weil_form_enclosure`` -- an Arb enclosure of `Re weilForm` for ONE explicit test function
    (or a `2 x 2` cross-correlation Gram block via Sylvester).  No uniform floor over a window,
    no `beta*`, no `A_L`, no tail constants.  Zhu's claim quantifies over EVERY `f` in `[-L, L]`.
  * ``interval_gram_inertia`` -- the exact signature `(p, q)` shared by every Hermitian matrix in a
    rational interval box.  Certifies INERTIA, not a quantitative floor, and explicitly REFUSES the
    definite case (`p == 0` or `q == 0`).  Zhu's block is definite and the datum is `lam0`.
  * ``psd_form`` -- exact rational PSD of one explicit matrix; no interval, no floor, no lift.
  * ``rayleigh_gram`` -- one Rayleigh direction, not an infimum.
  * ``tight_cap_enclosure`` / ``bragg_floor`` -- unrelated shapes.

This emitter is that type.  Its certified datum is the bundle
`(L, T#, A_L, beta*, lam0, epsD, epsB, N)` closing on `min(lam0, beta* - epsD) - epsB > 0`.

THE DISCIPLINE (identical to ``emit_weil_form_enclosure``'s ``henc`` seam and the Li ladder)
--------------------------------------------------------------------------------------------
`lam0`, `epsD` and `epsB` are multiprecision / interval-arithmetic outputs (Zhu uses mpmath with
the gmpy2 backend at 50 digits; this program's equivalent is Arb via python-flint).  The EMITTED
LEAN never asserts them.  The kernel proves only the finite rational inequality

    0 < min(lam0, beta* - epsD) - epsB

by `norm_num`, and the passage to a window floor runs through FOUR NAMED, UNDISCHARGED analytic
hypotheses, which are exactly the analytic content of Theorem 1.1 that this program does not have:

  * ``hQrep`` -- Zhu eq. (2), the frequency-side symbol representation
    `Q(f) = 2 F(i/2)^2 + (1/2pi) int |F|^2 Psi_L`.  A rearrangement of the PROVED node
    `RH_limit_explicit_formula`, but that rearrangement is not proved on main.
  * ``henv``  -- Zhu Lemma 3.1, the digamma envelope
    `Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t` for `t >= 15/4`, by Binet's second formula.
    Mathlib's digamma support does not reach it.
  * ``hloc``  -- Zhu eqs. (6) and (12), the Legendre / spherical-Bessel localization
    `|j_n(x)| <= x^n/(2n+1)!!` and the super-exponential decay it gives the `C`-matrix entries.
    Spherical Bessel functions are not in Mathlib.
  * ``hhead`` -- the Arb/mpmath TRUST SEAM: the leading block's least eigenvalue is at least `lam0`.

The two moves of Theorem 1.1 that ARE provable in Lean today -- the two-block bound (eq. 13,
`lambda_min(M_R) >= min(lambda_min(A), lambda_min(D)) - ||B||`) and the Cholesky residual bound
(Lemma 5.2, `lambda_min(M') >= -(r+s)` from `L~ L~^T >= 0` and Weyl) -- are recorded in the prelude
as the discharge targets.  They are not proved here; this emitter emits certificates, not analysis.

THE ANTI-PHANTOM FACE, AND WHY IT IS UNUSUALLY STRONG
------------------------------------------------------
``window_form_floor_certificate`` RE-DERIVES the two finite constants rather than trusting them:
`A_L` by exact von Mangoldt summation over `log n < 2L` (strict), and `beta*` from `(T#, A_L)`.
It refuses any instance whose declared values disagree beyond `const_tol`.

That is the guard that catches the paper's OWN RETRACTED CLAIM.  An earlier draft of Zhu's work
substituted the per-prime constant `A_eff = -sum_p min_theta sum_k c_{p,k} cos(k theta)` for `A_L`
in the envelope: at `L = 1.19`, `A_eff = 4.6948` against `A_L = 7.0750`.  `A_eff` bounds the comb
from BELOW, hence the symbol from ABOVE, and the envelope needs an UPPER bound for the comb; by
Lemma 3.2 (`sup_t P_L(t) = A_L` exactly, via Weyl equidistribution on `{log p}`) no pointwise upper
bound below `A_L` exists.  The resulting support-`2.38` claim is retracted (Remark 3.3, Section 15
item 4).  Every downstream number in that forgery is internally consistent -- with `A_eff` the
apparent threshold is `2 pi e^{A_eff} = 687.2` rather than the true `T_1 = 7427`, so a `T# = 1000`
run shows `beta* = 0.374 > 0` and a perfectly healthy-looking certificate.  ONLY re-derivation of
the constant from its definition catches it.  The negative-control twin is that forgery.

Full refusal list:
  * `L <= 0`, `T# <= 0`;
  * declared `A_L` disagrees with the recomputed comb mass -- THE RETRACTION GUARD;
  * declared `beta*` disagrees with `log(T#/2pi) - 1/T# - A_L`;
  * `beta* <= 0` -- Theorem 1.1's hypothesis fails; equivalently `T#` is below `T_1 = 2 pi e^{A_L}`
    (Theorem 1.4's barrier threshold, which Lemma 3.2 shows cannot be lowered);
  * `lam0 <= 0`, or negative `epsD` / `epsB`;
  * `2N < e L T# / 2` -- the Legendre localization does not apply at that cut, so the tail constants
    are not the ones bounded in the proof;
  * `min(lam0, beta* - epsD) - epsB <= 0` -- no positive floor is implied, so nothing is emitted.

WHAT THIS CERTIFIES, AND WHAT IT DOES NOT (read before citing it)
-----------------------------------------------------------------
Certified: a finite, kernel-checkable rational inequality, plus the bookkeeping that the constants
in it are the ones their definitions produce.  Category-(b): finite, consistent with RH, PROVING
NOTHING about RH.  Positivity of the Weil form on a bounded window is what RH predicts; observing it
on one window confirms nothing, since Weil positivity over EVERY support is RH-equivalent.

And the route is CLOSED, provably, by the same paper.  Theorem 1.4: any application of Theorem 1.1
needs `T# > T_1(L) = 2 pi e^{A_L}` with `A_L = (4 + o(1)) e^L` by PNT, so `T_1 = 2 pi exp(4 e^L)` and
the matrix size `N ~ L T_1` grows DOUBLY EXPONENTIALLY in the support; by Lemma 3.2 the threshold
cannot be lowered within pointwise-envelope certificates.  Certifying past support `~ 3.2`
(`T_1 ~ 1e7`) is, in the paper's word, computationally void.  Meanwhile the margin to be resolved
collapses at the Landau-Widom rate `-ln lambda*(L) ~ 2 pi^2 N(T*)/ln N(T*)`, `T* = 2 pi e^{2L}` --
though that law is MEASURED and its constant FITTED (Remark 1.5, Remark 12.2), not proved, and must
never be cited as a theorem.

Theorem 1.4 is scoped to certificates that bound the prime comb POINTWISE.  It is not a barrier for
positivity arguments in general, and escalating it to one misquotes the paper.

Design memo: telperion/docs/ZHU_WINDOW_POSITIVITY_IMPORT_2026-09-19.md.
No RH progress.  PRE-WALL.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

#: Default agreement tolerance between a DECLARED constant and its exact re-derivation.  The
#: declared values are rational truncations of transcendental quantities, so exact equality is not
#: available; `1e-6` is far tighter than any real error (Zhu's own retraction was off by 2.38) and
#: far looser than the truncation of a printed 7-digit constant.
CONST_TOL = sp.Rational(1, 10 ** 6)


def _rat(x):
    """Exact rational coercion that never loses a tiny magnitude.

    ``sp.nsimplify`` collapses values like ``1e-100`` to ``0`` at its default tolerance, which would
    silently turn a super-exponentially small tail constant into an exact zero -- a certificate bug
    that flatters the instance.  Sympy numbers, ints, strings and Fractions pass straight to
    ``sp.Rational``; only genuine floats go through ``nsimplify(rational=True)``.
    """
    if isinstance(x, sp.Expr) and x.is_Rational:
        return sp.Rational(x)
    if isinstance(x, (int, str)):
        return sp.Rational(x)
    from fractions import Fraction
    if isinstance(x, Fraction):
        return sp.Rational(x.numerator, x.denominator)
    return sp.nsimplify(x, rational=True)


def _von_mangoldt(n: int) -> "sp.Expr | None":
    """`Lambda(n) = log p` when `n = p^k`, else None (the emitter sums only prime powers)."""
    if n < 2:
        return None
    factors = sp.factorint(n)
    if len(factors) != 1:
        return None
    (p,) = factors
    return sp.log(p)


def comb_mass(L, terms: bool = False, n_max: int = 10 ** 6):
    """The comb mass `A_L = sum_{log n < 2L} 2 Lambda(n)/sqrt n`, recomputed EXACTLY.

    This is the retraction guard's engine.  The inequality is STRICT (`log n < 2L`), matching Zhu
    eq. (3); at `2L = log 4` exactly, `n = 4` is excluded.  The sum is finite: `n < e^{2L}`.

    With ``terms=True`` returns the list of `(n, 2 Lambda(n)/sqrt n)` pairs instead of the sum, so
    a caller can see which prime powers are live (three of them, `n = 2, 3, 4`, at `L = 0.8`).
    """
    L = _rat(L)
    if L <= 0:
        raise ValueError(f"window_form_floor REFUSED: need half-width L > 0, got {L}")
    bound = sp.exp(2 * L)
    limit = int(sp.floor(bound)) + 2
    if limit > n_max:
        raise ValueError(
            f"window_form_floor REFUSED: comb cutoff e^(2L) = {float(bound):.3g} exceeds n_max="
            f"{n_max}; A_L is finite but this L is past the doubly exponential barrier "
            f"(Zhu Thm 1.4) and no certificate of this shape is computable there")
    out = []
    total = sp.Integer(0)
    for n in range(2, limit + 1):
        lam = _von_mangoldt(n)
        if lam is None:
            continue
        gap = sp.simplify(sp.log(n) - 2 * L)
        neg = gap.is_negative
        if neg is None:                       # undecidable symbolically: settle it numerically
            neg = bool(sp.N(gap, 60) < 0)
        if neg:
            t = 2 * lam / sp.sqrt(n)
            out.append((n, t))
            total += t
    return out if terms else total


@dataclass(frozen=True)
class WindowFormFloorData:
    """Raw input to the certificate layer.

    `comb_mass` and `beta_star` are DECLARED values, re-derived and checked rather than trusted;
    `lam0`, `eps_d`, `eps_b` are the Arb/mpmath enclosures (the documented non-kernel trust seam);
    `n_modes` is `N`, the number of retained even Legendre modes (first discarded order `2N`).
    """

    L: object
    t_sharp: object
    comb_mass: object
    beta_star: object
    lam0: object
    eps_d: object
    eps_b: object
    n_modes: int
    published_floor: object = None
    label: str = ""
    const_tol: object = CONST_TOL


@dataclass(frozen=True)
class WindowFormFloorCert:
    """One certified window-floor instance.  The claim is the finite rational inequality
    `0 < min(lam0, beta_star - eps_d) - eps_b`, together with the recorded fact that `comb_mass`
    and `beta_star` are the values their definitions produce at `(L, t_sharp)`."""

    L: sp.Rational
    t_sharp: sp.Rational
    comb_mass: sp.Rational
    beta_star: sp.Rational
    lam0: sp.Rational
    eps_d: sp.Rational
    eps_b: sp.Rational
    n_modes: int
    published_floor: sp.Rational
    label: str

    @property
    def floor(self) -> sp.Rational:
        """The certified window floor `min(lam0, beta* - epsD) - epsB` (Zhu Thm 1.1)."""
        return sp.Rational(min(self.lam0, self.beta_star - self.eps_d) - self.eps_b)

    @property
    def t_one(self):
        """The barrier threshold `T_1 = 2 pi e^{A_L}` (Zhu Thm 1.4); `T#` must exceed it."""
        return 2 * sp.pi * sp.exp(self.comb_mass)

    @property
    def cut_order_bound(self):
        """The localization bound `e L T# / 2`; the first discarded order `2N` must reach it."""
        return sp.E * self.L * self.t_sharp / 2


def window_form_floor_certificate(data: WindowFormFloorData) -> WindowFormFloorCert:
    """Build (and exactly re-check) a window-form-floor certificate.

    Every refusal is listed in the module docstring.  The load-bearing one is the RETRACTION GUARD:
    the declared comb mass is re-derived from `L` by exact von Mangoldt summation, because that is
    the only check that catches an `A_eff`-for-`A_L` substitution (Zhu Remark 3.3).
    """
    L = _rat(data.L)
    t_sharp = _rat(data.t_sharp)
    tol = _rat(data.const_tol)

    if L <= 0:
        raise ValueError(f"window_form_floor REFUSED: need half-width L > 0, got {L}")
    if t_sharp <= 0:
        raise ValueError(f"window_form_floor REFUSED: need cut frequency T# > 0, got {t_sharp}")

    declared_A = _rat(data.comb_mass)
    exact_A = comb_mass(L)
    if abs(sp.N(declared_A - exact_A)) > tol:
        raise ValueError(
            f"window_form_floor REFUSED: declared comb mass A_L = {float(declared_A):.6g} "
            f"disagrees with the exact sum_(log n < 2L) 2*Lambda(n)/sqrt(n) = "
            f"{float(exact_A):.6g} at L = {float(L):.6g} (tolerance {float(tol):.3g}).  "
            f"THE RETRACTION GUARD: Zhu's withdrawn support-2.38 claim substituted the per-prime "
            f"constant A_eff for A_L, which bounds the comb from BELOW where the envelope needs an "
            f"UPPER bound; by Lemma 3.2 sup_t P_L(t) = A_L exactly, so no smaller pointwise "
            f"constant exists")

    declared_beta = _rat(data.beta_star)
    exact_beta = sp.log(t_sharp / (2 * sp.pi)) - 1 / t_sharp - exact_A
    if abs(sp.N(declared_beta - exact_beta)) > tol:
        raise ValueError(
            f"window_form_floor REFUSED: declared beta* = {float(declared_beta):.8g} disagrees "
            f"with log(T#/2pi) - 1/T# - A_L = {float(exact_beta):.8g} at T# = {float(t_sharp):.6g} "
            f"(tolerance {float(tol):.3g}); the threshold constant is re-derived, never trusted")

    if declared_beta <= 0:
        raise ValueError(
            f"window_form_floor REFUSED: beta* = {float(declared_beta):.8g} <= 0, so Zhu Thm 1.1's "
            f"hypothesis fails.  Equivalently T# = {float(t_sharp):.6g} does not exceed the barrier "
            f"threshold T_1 = 2*pi*e^(A_L) = {float(2 * sp.pi * sp.exp(exact_A)):.6g} (Thm 1.4); "
            f"by Lemma 3.2 that threshold cannot be lowered within pointwise-envelope certificates")

    lam0 = _rat(data.lam0)
    eps_d = _rat(data.eps_d)
    eps_b = _rat(data.eps_b)
    if lam0 <= 0:
        raise ValueError(
            f"window_form_floor REFUSED: need a strictly positive block floor lam0, got {lam0}")
    if eps_d < 0 or eps_b < 0:
        raise ValueError(
            f"window_form_floor REFUSED: tail constants must be non-negative bounds, got "
            f"eps_d = {eps_d}, eps_b = {eps_b}")

    n_modes = int(data.n_modes)
    if n_modes < 1:
        raise ValueError(f"window_form_floor REFUSED: need n_modes >= 1, got {n_modes}")
    cut_bound = sp.E * L * t_sharp / 2
    if sp.N(2 * n_modes - cut_bound) < 0:
        raise ValueError(
            f"window_form_floor REFUSED: cut order 2N = {2 * n_modes} is below the localization "
            f"bound e*L*T#/2 = {float(cut_bound):.6g}, so Zhu Thm 1.1's Legendre localization does "
            f"not apply at this cut and eps_d / eps_b are not the constants bounded in its proof")

    raw_floor = sp.Rational(min(lam0, declared_beta - eps_d) - eps_b)
    published = raw_floor if data.published_floor is None else _rat(data.published_floor)
    if published <= 0:
        raise ValueError(
            f"window_form_floor REFUSED: published floor {float(published):.6g} <= 0 -- a window "
            f"floor claim must be strictly positive to say anything")
    if published > raw_floor:
        raise ValueError(
            f"window_form_floor REFUSED: published floor {float(published):.6g} EXCEEDS the "
            f"certified floor min(lam0, beta* - eps_d) - eps_b = {float(raw_floor):.6g}; rounding "
            f"must go DOWN (Zhu Thm 1.2 publishes 8.9e-18 for a raw 9e-18 - 4e-43 - 1e-100), and "
            f"rounding up would claim more than the certificate supports")

    cert = WindowFormFloorCert(
        L=L, t_sharp=t_sharp, comb_mass=declared_A, beta_star=declared_beta,
        lam0=lam0, eps_d=eps_d, eps_b=eps_b,
        n_modes=n_modes, published_floor=published, label=str(data.label),
    )
    if cert.floor <= 0:
        raise ValueError(
            f"window_form_floor REFUSED: floor min(lam0, beta* - eps_d) - eps_b = "
            f"{float(cert.floor):.6g} <= 0 -- no positive window floor is implied, so nothing is "
            f"emitted (raise the certified block floor lam0 or tighten the tail constants)")
    return cert


def certify_window_form_floor_point(family, pt, name):
    """Certify one window-floor instance: ``(CertifiedInstance, 1)``."""
    data = family.special[1](pt)
    cert = window_form_floor_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def window_form_floor_prelude_lean() -> str:
    """The window-floor vocabulary and the one abstract lemma the instances route through.

    Emitted ONCE per generated file, and SORRY-FREE.  Two pieces:

      * ``WindowFloor L lam`` -- Zhu's window predicate written in the registry's own vocabulary:
        the Weil pairing `Re weilForm (autocorr f)` of every smooth compactly supported test
        function supported in `[-L, L]` is at least `lam * ||f||_2^2`.  `WindowFloor L lam` with
        `lam > 0` at a fixed `L` is a finite fragment of RH; `forall L, WindowFloor L 0` is the
        RH-equivalent clause and is NOT touched here.
      * ``windowFloor_of_le`` -- monotonicity in the floor, PROVED: a window floor at `lam`
        implies one at any `mu <= lam`, because `int ||f||^2 >= 0`.

    That lemma is what each instance uses, and it is the reason the emitted theorems are honest.
    Zhu's Theorem 1.2 does exactly this rounding in its last line: the raw certified constant is
    `lam0 - (r+s) - epsB = 9e-18 - 4e-43 - 1e-100`, and the published floor is the rounded-down
    `8.9e-18`.  The kernel here proves that the rounding is SOUND; it proves nothing about the raw
    constant, which arrives as the hypothesis `hred` (the Arb/mpmath trust seam together with the
    four undischarged analytic inputs of Theorem 1.1).

    Requires `WeilFormDefs` (the `WeilExplicit` / `WeilForm` vocabulary mirrored from the proved
    node `RH_limit_explicit_formula`).  conjecture1_proved = False.
    """
    return (
        "/-! ## Zhu's window-floor vocabulary (arXiv:2608.24827) and the rounding lemma.\n\n"
        "`WindowFloor L lam` says the Weil pairing of every smooth compactly supported test function\n"
        "supported in `[-L, L]` is at least `lam * ||f||_2^2`.  At a FIXED `L` with `lam > 0` this is\n"
        "a finite fragment of RH (Weil 1952; Yoshida and Connes-Consani for `2L <= log 2`); the\n"
        "RH-equivalent clause is `WindowFloor L 0` for EVERY L, and nothing here approaches it.\n"
        "conjecture1_proved = False. -/\n"
        "\n"
        "open MeasureTheory in\n"
        "/-- The window floor predicate (Zhu eq. 1, written with the registry's E8 vocabulary). -/\n"
        "def WindowFloor (L lam : \u211d) : Prop :=\n"
        "  \u2200 f : \u211d \u2192 \u2102, WeilExplicit.IsWeilTest f \u2192\n"
        "    tsupport f \u2286 Set.Icc (-L) L \u2192\n"
        "    lam * (\u222b x : \u211d, \u2016f x\u2016 ^ 2) \u2264\n"
        "      (WeilForm.weilForm (WeilForm.autocorr f)).re\n"
        "\n"
        "open MeasureTheory in\n"
        "/-- Monotonicity of the floor: a window floor at `lam` gives one at any `mu \u2264 lam`,\n"
        "    since the L2 mass is non-negative.  This is exactly the rounding step in the last line\n"
        "    of Zhu Thm 1.2 (raw `9e-18 - 4e-43 - 1e-100`, published `8.9e-18`). -/\n"
        "theorem windowFloor_of_le {L lam mu : \u211d} (h : WindowFloor L lam) (hmu : mu \u2264 lam) :\n"
        "    WindowFloor L mu := by\n"
        "  intro f hf hsupp\n"
        "  refine le_trans ?_ (h f hf hsupp)\n"
        "  have hnn : (0 : \u211d) \u2264 \u222b x : \u211d, \u2016f x\u2016 ^ 2 :=\n"
        "    integral_nonneg fun x => by positivity\n"
        "  exact mul_le_mul_of_nonneg_right hmu hnn\n"
    )


@dataclass
class WindowFormFloorEmitter(Emitter):
    """Emit Zhu's window-floor certificate: the finite rational inequality
    `0 < min(lam0, beta* - epsD) - epsB` discharged by `norm_num`, with the four analytic inputs of
    Theorem 1.1 and the Arb block floor carried as NAMED, UNDISCHARGED hypotheses."""

    def __post_init__(self):
        self.kind = "window_form_floor"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: WindowFormFloorCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            L = rat_lean(cert.L)
            lam0 = rat_lean(cert.lam0)
            epsd = rat_lean(cert.eps_d)
            epsb = rat_lean(cert.eps_b)
            beta = rat_lean(cert.beta_star)
            pub = rat_lean(cert.published_floor)
            lines.append(
                f"-- {nm}: Zhu arXiv:2608.24827 Thm 1.1 instantiated at L = {cert.L} "
                f"(autocorrelation support {2 * cert.L}), T# = {cert.t_sharp}, N = {cert.n_modes} "
                f"even Legendre modes.\n"
                f"-- FINITE constants, RE-DERIVED by the emitter and never trusted: comb mass "
                f"A_L = {float(cert.comb_mass):.10g} = sum_(log n < 2L) 2*Lambda(n)/sqrt(n) (a "
                f"finite von Mangoldt sum); and\n"
                f"-- beta* = log(T#/2pi) - 1/T# - A_L = {float(cert.beta_star):.10g} > 0, which is "
                f"exactly the condition T# > T_1 = 2*pi*e^(A_L) = {float(cert.t_one):.6g}, the "
                f"Thm 1.4 barrier threshold\n"
                f"-- (unimprovable within pointwise-envelope certificates by Lemma 3.2, "
                f"sup_t P_L(t) = A_L exactly via Weyl equidistribution on (log p)).\n"
                f"-- TRUST SEAM, NON-KERNEL: lam0 = {float(cert.lam0):.6g} is an Arb / mpmath "
                f"certified least-eigenvalue floor for the leading Legendre block; eps_d = "
                f"{float(cert.eps_d):.6g} (tail-block deviation) and\n"
                f"-- eps_b = {float(cert.eps_b):.6g} (leading-tail coupling norm) are the "
                f"super-exponentially small constants bounded in the proof.  The kernel asserts "
                f"NONE of them.\n"
                f"-- They enter through hred, together with the four UNDISCHARGED analytic inputs "
                f"of Thm 1.1: eq. (2) the frequency-side symbol representation, Lemma 3.1 the "
                f"digamma envelope,\n"
                f"-- eqs. (6) and (12) the Legendre / spherical-Bessel localization, and the block "
                f"floor itself.  What the kernel DOES prove is that the published rounding is "
                f"sound.\n"
                f"-- Category-(b): finite, consistent with RH, PROVES NOTHING about RH.  The route "
                f"is closed by Thm 1.4 at doubly exponential cost.  conjecture1_proved = False.\n"
                f"theorem {nm}\n"
                f"    (hred : WindowFloor ({L}) "
                f"(min ({lam0}) (({beta}) - ({epsd})) - ({epsb}))) :\n"
                f"    WindowFloor ({L}) ({pub}) :=\n"
                f"  windowFloor_of_le hred (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def window_form_floor_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a window-form-floor family (kind ``window_form_floor``).
    ``spec: pt -> WindowFormFloorData``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("window_form_floor", spec),
        constants=dict(constants or {}),
    )
