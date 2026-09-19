"""Self-inversive rigidity emitter — equal-modulus real-rootedness (MIRRORMERE R3, n=2).

The reverse-Dyson base-case rigidity theorem distilled from the quasicrystal island's
`TwoFreqRigidity.lean` (`twoFreq_realRooted_iff`): for a two-frequency exponential sum

    F(x) = c₁·e^{i λ₁ x} + c₂·e^{i λ₂ x},    c₁,c₂ ∈ ℂ*,   λ₁ ≠ λ₂ ∈ ℝ,

`F` is REAL-ROOTED (every zero has zero imaginary part) IF AND ONLY IF `|c₁| = |c₂|` — the reality of
the SUPPORT forced by an equal-modulus condition on the COEFFICIENTS (spectrum side).

The emitter takes Gaussian-rational coefficients `c₁ = (re₁, im₁)`, `c₂ = (re₂, im₂)` and rational
frequencies `λ₁ ≠ λ₂`.  When `|c₁|² = |c₂|²` EXACTLY (rational arithmetic: `re₁²+im₁² = re₂²+im₂²`)
it emits Lean that proves `‖c₁‖ = ‖c₂‖` (via `Complex.norm_def` + the exact rational normSq equality)
and applies `Quasicrystal.twoFreq_realRooted_iff` to conclude real-rootedness of the concrete sum.

Self-check (EXACT rational): `re₁²+im₁² = re₂²+im₂²`, both coefficients nonzero (`|cᵢ|² > 0`), and
`λ₁ ≠ λ₂`.

NEGATIVE CONTROL: `|c₁|² ≠ |c₂|²` is REFUSED to certify real-rootedness — equal modulus is exactly
the forcing condition, and unequal modulus puts every zero off the real line (on the single line
`Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Also refused: a zero coefficient, or `λ₁ = λ₂`.

OFFLINE MODE (``spec["mode"] == "offline"``, 2026-09-18, MIRRORMERE torus-section ladder T2):
the REFUTATION-shaped mirror.  Real coefficients of the form `r·√q` (r, q rational, q > 0, so
`|c|² = r²·q` is EXACT rational arithmetic) and frequencies that are rational or `r·log q`
(q integer ≥ 2).  When `|c₁|² ≠ |c₂|²` EXACTLY the emitter proves
`¬ (∀ x, twoFreq c₁ c₂ λ₁ λ₂ x = 0 → x.im = 0)` — the `.mp` direction of the iff would force
`‖c₁‖ = ‖c₂‖`, and the kernel checks `‖c₁‖² = r₁²q₁ ≠ r₂²q₂ = ‖c₂‖²` by `norm_num`.  The p-th
Euler-factor section `1 − p^{−s}` on `s = 1/2 + ix` is `twoFreq(1, −(1/√p); 0, −log p)`, whose zeros
sit uniformly at `Im x = 1/2`; for that exact shape the emitter ALSO ships the explicit witness
`x = i/2`.  NEGATIVE CONTROL of the offline mode: EQUAL modulus is REFUSED (mirror of the default
mode's refusal), as is any frequency pair whose distinctness the kernel cannot certify without
transcendence (`λ₁ ∈ ℚ∖{0}` against `r·log q` needs Lindemann — refused, not faked).
conjecture1_proved = False — an unconditional finite rigidity fact, NOT a proof of RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

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


@dataclass(frozen=True)
class SelfInversiveRigidityCertificate:
    """A verified equal-modulus rigidity certificate: Gaussian-rational coefficients with
    `|c₁|² = |c₂|²` EXACTLY, distinct rational frequencies, both coefficients nonzero."""

    re1: sp.Rational
    im1: sp.Rational
    re2: sp.Rational
    im2: sp.Rational
    lam1: sp.Rational
    lam2: sp.Rational
    normsq: sp.Rational       # the common |c₁|² = |c₂|²


def selfinversive_rigidity_certificate(c1, c2, lam1, lam2) -> SelfInversiveRigidityCertificate:
    """Build and EXACTLY self-check a self-inversive rigidity certificate.

    `c1`, `c2`: `(re, im)` rational pairs (Gaussian rationals).  `lam1`, `lam2`: rational frequencies.

    REFUSES (``ValueError``):
      * non-rational input;
      * a zero coefficient (`|cᵢ|² = 0`);
      * `lam1 = lam2` (degenerate — no two-frequency structure);
      * `|c₁|² ≠ |c₂|²` (the negative control: unequal modulus does NOT force real-rootedness).
    """
    re1, im1 = sp.nsimplify(c1[0]), sp.nsimplify(c1[1])
    re2, im2 = sp.nsimplify(c2[0]), sp.nsimplify(c2[1])
    l1, l2 = sp.nsimplify(lam1), sp.nsimplify(lam2)
    for nm, v in (("re1", re1), ("im1", im1), ("re2", re2), ("im2", im2),
                  ("lam1", l1), ("lam2", l2)):
        if not v.is_rational:
            raise ValueError(f"selfinversive_rigidity: {nm} must be rational; got {v!r}")
    ns1 = re1 ** 2 + im1 ** 2
    ns2 = re2 ** 2 + im2 ** 2
    if ns1 == 0 or ns2 == 0:
        raise ValueError("selfinversive_rigidity: coefficients must be nonzero (|cᵢ|² > 0)")
    if l1 == l2:
        raise ValueError(f"selfinversive_rigidity: frequencies must differ; got λ₁=λ₂={l1}")
    # THE equal-modulus self-check (and the negative control).
    if ns1 != ns2:
        raise ValueError(
            f"selfinversive_rigidity: |c₁|²={ns1} ≠ |c₂|²={ns2} — unequal modulus does NOT force "
            f"real-rootedness (every zero sits off the real line); refused")
    return SelfInversiveRigidityCertificate(
        re1=re1, im1=im1, re2=re2, im2=im2, lam1=l1, lam2=l2, normsq=sp.nsimplify(ns1))



# --------------------------------------------------------------------------------------------
# OFFLINE MODE — refutation-shaped negative control (unequal modulus ⟹ NOT real-rooted).
# --------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class RadicalCoeff:
    """A real coefficient `r·√q` with r, q rational, r ≠ 0, q > 0.  `normsq = r²·q` exactly."""

    r: sp.Rational
    q: sp.Rational

    @property
    def normsq(self) -> sp.Rational:
        return sp.nsimplify(self.r ** 2 * self.q)


@dataclass(frozen=True)
class LogFreq:
    """A real frequency: rational `rat` (when ``logq`` is None) or `rat·log(logq)` with
    ``logq`` an integer ≥ 2 (so `log logq > 0` is a `norm_num`-discharged fact)."""

    rat: sp.Rational
    logq: sp.Integer | None = None

    @property
    def is_rational(self) -> bool:
        return self.logq is None


@dataclass(frozen=True)
class SelfInversiveOfflineCertificate:
    """A verified UNEQUAL-modulus refutation certificate: radical real coefficients with
    `|c₁|² ≠ |c₂|²` EXACTLY, frequencies certifiably distinct, both coefficients nonzero.
    ``euler_p`` is set when the instance is exactly the p-th Euler-factor section
    `twoFreq(1, −(1/√p); 0, −log p)`, for which the explicit witness `x = i/2` is emitted."""

    c1: RadicalCoeff
    c2: RadicalCoeff
    lam1: LogFreq
    lam2: LogFreq
    normsq1: sp.Rational
    normsq2: sp.Rational
    euler_p: int | None


def _radical_coeff(nm, spec) -> RadicalCoeff:
    if isinstance(spec, dict):
        r, q = spec.get("rat", 0), spec.get("sqrt", 1)
    else:  # a bare rational
        r, q = spec, 1
    r, q = sp.nsimplify(r), sp.nsimplify(q)
    if not (r.is_rational and q.is_rational):
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} must be r·√q with r, q rational")
    if r == 0:
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} must be nonzero (|c|² > 0)")
    if q <= 0:
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} radicand must be > 0; got {q}")
    return RadicalCoeff(r=r, q=q)


def _log_freq(nm, spec) -> LogFreq:
    if isinstance(spec, dict):
        rat, logq = spec.get("rat", 1), spec.get("log")
    else:
        rat, logq = spec, None
    rat = sp.nsimplify(rat)
    if not rat.is_rational:
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} coefficient must be rational")
    if logq is None:
        return LogFreq(rat=rat)
    logq = sp.nsimplify(logq)
    if not (logq.is_integer and logq >= 2):
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} log base must be an integer ≥ 2")
    if rat == 0:
        raise ValueError(f"selfinversive_rigidity[offline]: {nm} = 0·log q is degenerate; write 0")
    return LogFreq(rat=rat, logq=sp.Integer(logq))


def _freqs_certifiably_distinct(l1: LogFreq, l2: LogFreq) -> bool:
    """The kernel-certifiable distinctness cases (each discharged by `intro h; linarith` given
    `0 < log q`): both rational and different; `0` against `r·log q`; `r₁·log q` against
    `r₂·log q` with the SAME base.  Everything else (a nonzero rational against a log, or two
    logs with different bases) would need transcendence/independence of logarithms — REFUSED."""
    if l1.is_rational and l2.is_rational:
        return l1.rat != l2.rat
    if l1.is_rational or l2.is_rational:
        rat = l1 if l1.is_rational else l2
        return rat.rat == 0
    return l1.logq == l2.logq and l1.rat != l2.rat


def selfinversive_offline_certificate(c1, c2, lam1, lam2) -> SelfInversiveOfflineCertificate:
    """Build and EXACTLY self-check an OFFLINE (refutation) certificate.

    ``c1``, ``c2``: rational, or ``{"rat": r, "sqrt": q}`` meaning `r·√q`.
    ``lam1``, ``lam2``: rational, or ``{"rat": r, "log": q}`` meaning `r·log q` (q integer ≥ 2).

    REFUSES (``ValueError``):
      * a zero coefficient, a non-positive radicand, a non-rational input;
      * frequencies whose distinctness is not kernel-certifiable (see
        ``_freqs_certifiably_distinct``) — including `λ₁ = λ₂`;
      * `|c₁|² = |c₂|²` (THE negative control of this mode: equal modulus forces
        real-rootedness, so there is no off-line zero to certify).
    """
    a, b = _radical_coeff("c1", c1), _radical_coeff("c2", c2)
    l1, l2 = _log_freq("lam1", lam1), _log_freq("lam2", lam2)
    if not _freqs_certifiably_distinct(l1, l2):
        raise ValueError(
            f"selfinversive_rigidity[offline]: frequencies λ₁={lam1!r}, λ₂={lam2!r} are not "
            f"kernel-certifiably distinct (equal, or would need transcendence of log); refused")
    ns1, ns2 = a.normsq, b.normsq
    if ns1 == ns2:
        raise ValueError(
            f"selfinversive_rigidity[offline]: |c₁|²=|c₂|²={ns1} — EQUAL modulus forces "
            f"real-rootedness (twoFreq_realRooted_iff .mpr), there is no off-line zero; refused")
    euler_p = None
    if (a.r == 1 and a.q == 1 and l1.is_rational and l1.rat == 0
            and not l2.is_rational and l2.rat == -1
            and b.q == l2.logq and b.r == -1 / b.q):
        euler_p = int(l2.logq)
    return SelfInversiveOfflineCertificate(
        c1=a, c2=b, lam1=l1, lam2=l2, normsq1=ns1, normsq2=ns2, euler_p=euler_p)


def _freq_lean(f: LogFreq) -> str:
    if f.is_rational:
        return f"({rat_lean(f.rat)})"
    if f.rat == 1:
        return f"(Real.log {f.logq})"
    if f.rat == -1:
        return f"(-(Real.log {f.logq}))"
    return f"({rat_lean(f.rat)} * Real.log {f.logq})"


def _emit_offline_instance(base: str, cert: SelfInversiveOfflineCertificate) -> str:
    r1, q1 = rat_lean(cert.c1.r), rat_lean(cert.c1.q)
    r2, q2 = rat_lean(cert.c2.r), rat_lean(cert.c2.q)
    l1, l2 = _freq_lean(cert.lam1), _freq_lean(cert.lam2)
    log_facts = ""
    for f in (cert.lam1, cert.lam2):
        if not f.is_rational:
            log_facts += (f"    have hlog{f.logq} := Real.log_pos "
                          f"(by norm_num : (1 : ℝ) < {f.logq})\n")
            break  # same base by construction when both are logs
    # The nonvanishing + iff-application prelude, shared by the refutation and the witness.
    prelude = (
        f"  have hq1 : (0 : ℝ) < {q1} := by norm_num\n"
        f"  have hq2 : (0 : ℝ) < {q2} := by norm_num\n"
        f"  have hc1 : {base}_c1 ≠ 0 := Complex.ofReal_ne_zero.mpr\n"
        f"    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq1))\n"
        f"  have hc2 : {base}_c2 ≠ 0 := Complex.ofReal_ne_zero.mpr\n"
        f"    (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hq2))\n"
    )
    text = (
        f"/-- Concrete two-frequency sum `F(x) = c₁·e^{{iλ₁x}} + c₂·e^{{iλ₂x}}` with REAL radical\n"
        f"    coefficients `c₁ = {r1}·√{q1}`, `c₂ = {r2}·√{q2}` (so `|c₁|² = {cert.normsq1}`,\n"
        f"    `|c₂|² = {cert.normsq2}`, EXACT) and frequencies `λ₁ = {l1}`, `λ₂ = {l2}`. -/\n"
        f"noncomputable def {base}_c1 : ℂ := (({r1} * Real.sqrt {q1} : ℝ) : ℂ)\n"
        f"noncomputable def {base}_c2 : ℂ := (({r2} * Real.sqrt {q2} : ℝ) : ℂ)\n\n"
        f"/-- **Off-line refutation** ({base}): since `|c₁|² = {cert.normsq1} ≠ {cert.normsq2} = |c₂|²`\n"
        f"    EXACTLY, `‖c₁‖ ≠ ‖c₂‖`, so by the `.mp` direction of `Quasicrystal.twoFreq_realRooted_iff`\n"
        f"    the two-frequency sum is NOT real-rooted — some zero has nonzero imaginary part (in\n"
        f"    fact every zero sits on the single line `Im x = −(1/w)·log|c₁/c₂| ≠ 0`).  Reverse-Dyson\n"
        f"    R3(n=2) negative control: unequal modulus is exactly the off-line signature.\n"
        f"    conjecture1_proved = False. -/\n"
        f"theorem {base} :\n"
        f"    ¬ (∀ x : ℂ, Quasicrystal.twoFreq {base}_c1 {base}_c2 {l1} {l2} x = 0 → x.im = 0) := by\n"
        f"  intro hall\n"
        f"{prelude}"
        f"  have hlam : ({l1} : ℝ) ≠ {l2} := by\n"
        f"{log_facts}"
        f"    intro h\n"
        f"    linarith\n"
        f"  have hn := (Quasicrystal.twoFreq_realRooted_iff {base}_c1 {base}_c2 {l1} {l2}\n"
        f"    hc1 hc2 hlam).mp hall\n"
        f"  -- the kernel checks the EXACT normSq inequality {cert.normsq1} ≠ {cert.normsq2}\n"
        f"  have hsq : ‖{base}_c1‖ ^ 2 ≠ ‖{base}_c2‖ ^ 2 := by\n"
        f"    unfold {base}_c1 {base}_c2\n"
        f"    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,\n"
        f"      sq_abs, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hq1.le, Real.sq_sqrt hq2.le]\n"
        f"    norm_num\n"
        f"  exact hsq (by rw [hn])\n\n"
    )
    if cert.euler_p is not None:
        p = cert.euler_p
        text += (
            f"/-- **Explicit off-line witness** ({base}_witness): `x = i/2` is a zero of the p = {p}\n"
            f"    Euler-factor section `1 − (1/√{p})·e^{{−i (log {p}) x}}`, since\n"
            f"    `e^{{−i (log {p}) (i/2)}} = e^{{(log {p})/2}} = √{p}`.  `Im (i/2) = 1/2`: the uniform\n"
            f"    off-line displacement (the zeros are `s = 2πik/log {p}`, i.e. `Re s = 0`).\n"
            f"    conjecture1_proved = False. -/\n"
            f"theorem {base}_witness :\n"
            f"    Quasicrystal.twoFreq {base}_c1 {base}_c2 {l1} {l2} (Complex.I / 2) = 0 := by\n"
            f"{prelude}"
            f"  rw [Quasicrystal.twoFreq_eq_zero_iff _ _ _ _ _ hc1 hc2]\n"
            f"  have harg : (((-(Real.log {p})) - 0 : ℝ) : ℂ) * (Complex.I / 2) * Complex.I\n"
            f"      = ((Real.log {p} / 2 : ℝ) : ℂ) := by\n"
            f"    push_cast\n"
            f"    ring_nf\n"
            f"    rw [Complex.I_sq]\n"
            f"    ring\n"
            f"  rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hq2]\n"
            f"  unfold {base}_c1 {base}_c2\n"
            f"  rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_inj, Real.sqrt_one]\n"
            f"  have hs : Real.sqrt {p} ≠ 0 := Real.sqrt_ne_zero'.mpr hq2\n"
            f"  have hsq : Real.sqrt {p} * Real.sqrt {p} = {p} := Real.mul_self_sqrt hq2.le\n"
            f"  field_simp\n"
            f"  linarith [hsq]\n\n"
            f"/-- The witness is off the real line: `Im (i/2) = 1/2 ≠ 0`, so `{base}` also follows\n"
            f"    directly from `{base}_witness` (second, independent route). -/\n"
            f"theorem {base}_of_witness :\n"
            f"    ¬ (∀ x : ℂ, Quasicrystal.twoFreq {base}_c1 {base}_c2 {l1} {l2} x = 0 → x.im = 0) := by\n"
            f"  intro hall\n"
            f"  have h := hall (Complex.I / 2) {base}_witness\n"
            f"  simp [Complex.div_ofNat_im] at h\n\n"
            # The SAME refutation restated in the registry's own spelling of the coefficients
            # (1 and -(1/sqrt p)), so the emitted Lean carries the node statement verbatim.
            f"/-- The p = {p} Euler-factor coefficients in the registry's spelling:\n"
            f"    `{r1}·√{q1} = 1` and `{r2}·√{p} = -(1/√{p})` (since `√{p}·√{p} = {p}`). -/\n"
            f"theorem {base}_c1_eq : {base}_c1 = 1 := by\n"
            f"  unfold {base}_c1\n"
            f"  rw [Real.sqrt_one]\n"
            f"  norm_num\n\n"
            f"theorem {base}_c2_eq : {base}_c2 = ((-(1 / Real.sqrt {p}) : ℝ) : ℂ) := by\n"
            f"  unfold {base}_c2\n"
            f"  have hq : (0 : ℝ) < {p} := by norm_num\n"
            f"  have hs : Real.sqrt {p} ≠ 0 := Real.sqrt_ne_zero'.mpr hq\n"
            f"  have hsq : Real.sqrt {p} * Real.sqrt {p} = {p} := Real.mul_self_sqrt hq.le\n"
            f"  rw [Complex.ofReal_inj]\n"
            f"  field_simp\n"
            f"  linarith [hsq]\n\n"
            f"/-- **The registry-verbatim form** ({base}_node): the p = {p} Euler-factor section\n"
            f"    `twoFreq 1 (-(1/√{p})) 0 (-log {p})` is NOT real-rooted.  Identical content to\n"
            f"    `{base}`, restated with the coefficients in the mission-registry spelling.\n"
            f"    conjecture1_proved = False. -/\n"
            f"theorem {base}_node :\n"
            f"    ¬ (∀ x : ℂ,\n"
            f"        Quasicrystal.twoFreq 1 ((-(1 / Real.sqrt {p}) : ℝ) : ℂ) 0 (-(Real.log {p})) x = 0\n"
            f"          → x.im = 0) := by\n"
            f"  rw [← {base}_c1_eq, ← {base}_c2_eq]\n"
            f"  exact {base}\n\n"
        )
    return text


def certify_selfinversive_rigidity_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` — a dict with keys ``c1``, ``c2``
    ((re,im) pairs) and ``lam1``, ``lam2`` (rational frequencies); with ``mode="offline"`` the
    coefficients are radicals ``{"rat": r, "sqrt": q}`` and frequencies may be ``{"rat": r,
    "log": q}`` (see ``selfinversive_offline_certificate``)."""
    spec = family.special[1](pt)
    mode = spec.get("mode", "rigidity")
    if mode == "offline":
        cert = selfinversive_offline_certificate(spec["c1"], spec["c2"], spec["lam1"], spec["lam2"])
    elif mode == "rigidity":
        cert = selfinversive_rigidity_certificate(spec["c1"], spec["c2"], spec["lam1"], spec["lam2"])
    else:
        raise ValueError(f"selfinversive_rigidity: unknown mode {mode!r} (rigidity | offline)")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class SelfInversiveRigidityEmitter(Emitter):
    """Emit equal-modulus real-rootedness — `‖c₁‖ = ‖c₂‖` (from the exact rational normSq equality)
    fed into `Quasicrystal.twoFreq_realRooted_iff`.  One theorem per instance.  The emitted file
    imports the in-island `TwoFreqRigidity`, so it must be built inside the quasicrystal island.

    OFFLINE-mode instances (payload ``SelfInversiveOfflineCertificate``) emit the refutation
    `¬ real-rooted` from the exact normSq INEQUALITY via the `.mp` direction, plus — for the exact
    Euler-factor shape `twoFreq(1, −(1/√p); 0, −log p)` — the explicit witness `x = i/2`, the
    witness-route refutation, and the MISSION-REGISTRY-VERBATIM restatement `…_node` whose
    coefficients are spelled `1` and `−(1/√p)` (six theorems)."""

    def __post_init__(self):
        self.kind = "selfinversive_rigidity"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            if isinstance(inst.payload, SelfInversiveOfflineCertificate):
                lines.append(_emit_offline_instance(inst.lean_name, inst.payload))
                nthm += 1 + (5 if inst.payload.euler_p is not None else 0)
                continue
            cert: SelfInversiveRigidityCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            re1, im1 = rat_lean(cert.re1), rat_lean(cert.im1)
            re2, im2 = rat_lean(cert.re2), rat_lean(cert.im2)
            l1, l2 = rat_lean(cert.lam1), rat_lean(cert.lam2)

            lines.append(
                f"/-- Concrete two-frequency sum `F(x) = c₁·e^{{iλ₁x}} + c₂·e^{{iλ₂x}}` with Gaussian-\n"
                f"    rational coefficients `c₁ = {re1} + {im1}i`, `c₂ = {re2} + {im2}i` and frequencies\n"
                f"    `λ₁ = {l1}`, `λ₂ = {l2}`. -/\n"
                f"noncomputable def {base}_c1 : ℂ := ⟨({re1}), ({im1})⟩\n"
                f"noncomputable def {base}_c2 : ℂ := ⟨({re2}), ({im2})⟩\n\n"
                f"/-- **Equal-modulus rigidity** ({base}): since `|c₁|² = |c₂|²` exactly, `‖c₁‖ = ‖c₂‖`,\n"
                f"    so by `Quasicrystal.twoFreq_realRooted_iff` the two-frequency sum is REAL-ROOTED —\n"
                f"    every zero has zero imaginary part.  Reverse-Dyson R3(n=2): reality of the support\n"
                f"    is forced by an equal-modulus condition on the coefficients alone.\n"
                f"    conjecture1_proved = False. -/\n"
                f"theorem {base} :\n"
                f"    ∀ x : ℂ, Quasicrystal.twoFreq {base}_c1 {base}_c2 ({l1}) ({l2}) x = 0 → x.im = 0 := by\n"
                f"  have hc1 : {base}_c1 ≠ 0 := by\n"
                f"    have h : Complex.normSq {base}_c1 ≠ 0 := by\n"
                f"      unfold {base}_c1; simp only [Complex.normSq_mk]; norm_num\n"
                f"    exact fun hz => h (by rw [hz]; simp)\n"
                f"  have hc2 : {base}_c2 ≠ 0 := by\n"
                f"    have h : Complex.normSq {base}_c2 ≠ 0 := by\n"
                f"      unfold {base}_c2; simp only [Complex.normSq_mk]; norm_num\n"
                f"    exact fun hz => h (by rw [hz]; simp)\n"
                f"  have hlam : ({l1} : ℝ) ≠ ({l2}) := by norm_num\n"
                f"  have hmod : ‖{base}_c1‖ = ‖{base}_c2‖ := by\n"
                f"    have hns : Complex.normSq {base}_c1 = Complex.normSq {base}_c2 := by\n"
                f"      unfold {base}_c1 {base}_c2; simp only [Complex.normSq_mk]; norm_num\n"
                f"    rw [Complex.norm_def, Complex.norm_def, hns]\n"
                f"  exact (Quasicrystal.twoFreq_realRooted_iff {base}_c1 {base}_c2 ({l1}) ({l2}) hc1 hc2 hlam).mpr hmod\n\n"
            )
            nthm += 1
        return "".join(lines), nthm


def selfinversive_rigidity_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a selfinversive_rigidity family (kind='selfinversive_rigidity').  ``spec``: ``pt -> dict``
    with keys ``c1``, ``c2`` ((re,im) rational pairs), ``lam1``, ``lam2``.  Refuses unequal modulus
    (the negative control), a zero coefficient, or equal frequencies.  A spec with
    ``"mode": "offline"`` instead certifies the REFUTATION (unequal modulus ⟹ NOT real-rooted)
    and refuses EQUAL modulus."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("selfinversive_rigidity", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert (c1=(3/5,4/5), c2=(1,0), |c|²=1) ===")
    c = selfinversive_rigidity_certificate(("3/5", "4/5"), ("1", "0"), "1", "2")
    print(f"cert OK: |c₁|²=|c₂|²={c.normsq}")
    print("\n=== NEGATIVE CONTROL: unequal modulus (must raise) ===")
    try:
        selfinversive_rigidity_certificate(("3/5", "4/5"), ("2", "0"), "1", "2")
        raise SystemExit("FAIL: unequal modulus not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    fam = selfinversive_rigidity_family(
        "T", GridSpec([("case", [0])]), lambda pt: "rigidity_demo",
        spec=lambda pt: {"c1": ("3/5", "4/5"), "c2": ("1", "0"), "lam1": "1", "lam2": "2"})
    inst, _ = certify_selfinversive_rigidity_point(fam, {"case": 0}, "rigidity_demo")

    class _V:
        instances = [inst]

    body, nthm = SelfInversiveRigidityEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")

    print("\n=== OFFLINE mode: p=2 Euler-factor section (must certify, ships witness) ===")
    euler2 = {"mode": "offline", "c1": "1", "c2": {"rat": "-1/2", "sqrt": 2},
              "lam1": "0", "lam2": {"rat": "-1", "log": 2}}
    oc = selfinversive_offline_certificate(euler2["c1"], euler2["c2"], euler2["lam1"], euler2["lam2"])
    print(f"cert OK: |c₁|²={oc.normsq1} ≠ |c₂|²={oc.normsq2}, euler_p={oc.euler_p}")
    print("\n=== OFFLINE NEGATIVE CONTROL: equal modulus (must raise) ===")
    try:
        selfinversive_offline_certificate({"rat": "1/2", "sqrt": 2}, {"rat": "-1/2", "sqrt": 2},
                                          "0", {"rat": "-1", "log": 2})
        raise SystemExit("FAIL: equal modulus not refused in offline mode")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam2 = selfinversive_rigidity_family(
        "T2", GridSpec([("case", [0])]), lambda pt: "euler_factor_p2", spec=lambda pt: euler2)
    inst2, _ = certify_selfinversive_rigidity_point(fam2, {"case": 0}, "euler_factor_p2")

    class _V2:
        instances = [inst2]

    body2, nthm2 = SelfInversiveRigidityEmitter().emit_body(_V2(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm2} theorems --\n{body2}")
