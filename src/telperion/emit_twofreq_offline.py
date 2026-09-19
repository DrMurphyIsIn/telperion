"""twofreq_offline emitter -- certified OFF-line displacement of a two-frequency section.

MIRRORMERE torus-section ladder, rung T2 (QC_TORUS_SECTION_LADDER memo sections 4b/5).
The EXACT COMPLEMENT of `emit_selfinversive_rigidity`.  For a two-frequency exponential sum

    F(x) = c1 * e^{i lam1 x} + c2 * e^{i lam2 x},   c1,c2 in C*,  lam1 != lam2 in R,

the island lemma `Quasicrystal.twoFreq_realRooted_iff` (TwoFreqRigidity.lean:92) says

    (every zero of F is real)  <->  ||c1|| = ||c2||.

`selfinversive_rigidity` emits the POSITIVE direction from |c1|^2 = |c2|^2 EXACTLY.
This emitter certifies the NEGATIVE direction: when |c1|^2 != |c2|^2 EXACTLY, F is NOT
real-rooted -- some zero sits strictly off the real line.  Together the two emitters
PARTITION the coefficient space: each REFUSES precisely the regime the other certifies,
so neither can emit a false theorem.

THE FAMILY.  The motivating instance is the Euler factor at a prime p, read on the
critical line s = 1/2 + i x:

    1 - p^{-s} = 1 - p^{-1/2} e^{-i (log p) x} = twoFreq 1 (-(1/sqrt p)) 0 (-(log p)) (x),

whose moduli are 1 and 1/sqrt p -- never equal.  So NO single Euler-factor section is
real-rooted, at any prime, at any rung of the ladder.  In `mode='displacement'` the
emitter additionally certifies WHERE the zeros go: uniformly at `Im x = 1/2`, i.e. on
`Re s = 0`, the memo's "uniform off-line displacement 1/2, at every rung, for every p".
This is the ladder's certified NEGATIVE CONTROL: it shows no per-rung line-membership
claim can survive finite truncation, so critical-line membership is an infinite-N
continuation phenomenon and never a finite-section fact.

COEFFICIENT LITERALS.  `selfinversive_rigidity` takes Gaussian rationals only; the Euler
factor needs the IRRATIONAL coefficient -1/sqrt p, so this emitter carries three literal
shapes with EXACT rational moduli:

    gauss(re, im)        -> `re + im * Complex.I`        |c|^2 = re^2 + im^2
    inv_sqrt(s, sign)    -> `((+-(1 / Real.sqrt s) : R) : C)`  |c|^2 = 1/s
    real_sqrt(q, s)      -> `((q * Real.sqrt s : R) : C)`      |c|^2 = q^2 * s

and two frequency shapes: `rat(r)` and `neglog(p)` (the literal `-(Real.log p)`).

SELF-CHECK / REFUSALS (ValueError, all EXACT rational arithmetic -- no floats):
  * |c1|^2 == |c2|^2                 -- equal modulus: the sum IS real-rooted and the
                                        emitted negation would be FALSE.  THE anti-
                                        phantom guard, and the exact complement of
                                        selfinversive_rigidity's refusal.
  * a zero coefficient (|c|^2 == 0);
  * lam1 == lam2, including the disguised forms (neglog 1 IS rat 0, since log 1 = 0);
  * a negative rational frequency opposite a -log p frequency (the emitted separation
    argument is 0 <= r and -log p < 0; anything else is refused, not guessed);
  * a radicand s that is not an integer >= 2 (the emitted sqrt arithmetic is exact only
    there), or non-rational input;
  * mode='displacement' outside the p-family shape, or p < 2 -- honest scope: the
    certified displacement 1/2 is a fact about 1 - p^{-1/2} e^{-i log p x} ONLY.

conjecture1_proved = False.  A finite fact about ONE Euler factor (or one two-frequency
sum); it says nothing about zeta, about the full Euler product, or about RH.
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


# ---------------------------------------------------------------------------
# Literal constructors (CoefLit / LamLit are plain tuples so a negative-control
# adapter can hand-forge one, bypassing the Layer-1 self-check below).
# ---------------------------------------------------------------------------

def gauss(re, im) -> tuple:
    """Gaussian-rational coefficient `re + im*I`."""
    return ("gauss", sp.nsimplify(re), sp.nsimplify(im))


def inv_sqrt(s, sign: int = -1) -> tuple:
    """Coefficient `sign * (1 / sqrt s)` -- the Euler-factor shape (sign = -1)."""
    return ("inv_sqrt", int(sign), sp.nsimplify(s))


def real_sqrt(q, s) -> tuple:
    """Coefficient `q * sqrt s` with rational `q`."""
    return ("real_sqrt", sp.nsimplify(q), sp.nsimplify(s))


def rat(r) -> tuple:
    """Rational frequency."""
    return ("rat", sp.nsimplify(r))


def neglog(p) -> tuple:
    """Frequency `-(Real.log p)` -- the Euler-factor shape."""
    return ("neglog", int(p))


@dataclass(frozen=True)
class TwoFreqOfflineCert:
    """A verified off-line displacement certificate: two coefficient literals whose EXACT
    rational moduli DIFFER, and two distinct frequency literals."""

    c1: tuple                       # CoefLit
    c2: tuple                       # CoefLit
    lam1: tuple                     # LamLit
    lam2: tuple                     # LamLit
    normsq1: sp.Rational            # EXACT |c1|^2
    normsq2: sp.Rational            # EXACT |c2|^2
    p: int | None = None            # Euler-factor parameter, when the instance is one
    displacement: sp.Rational | None = None   # certified Im x, 1/2 for the p-family
    mode: str = "offline"           # 'offline' | 'displacement'


# ---------------------------------------------------------------------------
# Exact arithmetic on the literals
# ---------------------------------------------------------------------------

def _coef_normsq(c: tuple, which: str) -> sp.Rational:
    """EXACT |c|^2 of a coefficient literal.  Raises on a malformed / out-of-scope one."""
    tag = c[0]
    if tag == "gauss":
        re, im = c[1], c[2]
        for nm, v in (("re", re), ("im", im)):
            if not sp.nsimplify(v).is_rational:
                raise ValueError(f"twofreq_offline: {which}.{nm} must be rational; got {v!r}")
        return sp.nsimplify(re) ** 2 + sp.nsimplify(im) ** 2
    if tag == "inv_sqrt":
        sign, s = c[1], sp.nsimplify(c[2])
        if sign not in (1, -1):
            raise ValueError(f"twofreq_offline: {which} sign must be +-1; got {sign!r}")
        _check_radicand(s, which)
        return sp.Rational(1, 1) / s
    if tag == "real_sqrt":
        q, s = sp.nsimplify(c[1]), sp.nsimplify(c[2])
        if not q.is_rational:
            raise ValueError(f"twofreq_offline: {which} coefficient must be rational; got {q!r}")
        _check_radicand(s, which)
        return q ** 2 * s
    raise ValueError(f"twofreq_offline: unknown coefficient literal {tag!r}")


def _check_radicand(s, which: str) -> None:
    if not sp.nsimplify(s).is_rational:
        raise ValueError(f"twofreq_offline: {which} radicand must be rational; got {s!r}")
    if s <= 0:
        raise ValueError(f"twofreq_offline: {which} radicand must be positive; got {s}")
    if not (s.is_Integer and s >= 2):
        raise ValueError(
            f"twofreq_offline: {which} radicand must be an integer >= 2 (the emitted sqrt "
            f"arithmetic is exact only there); got {s}")


def _lam_value(lam: tuple, which: str):
    """The frequency as a sympy expression (`-log p` stays symbolic)."""
    tag = lam[0]
    if tag == "rat":
        r = sp.nsimplify(lam[1])
        if not r.is_rational:
            raise ValueError(f"twofreq_offline: {which} must be rational; got {r!r}")
        return r
    if tag == "neglog":
        p = int(lam[1])
        if p < 1:
            raise ValueError(f"twofreq_offline: {which} = -log p needs p >= 1; got {p}")
        return -sp.log(sp.Integer(p))
    raise ValueError(f"twofreq_offline: unknown frequency literal {tag!r}")


# ---------------------------------------------------------------------------
# Layer 1: build + EXACTLY self-check a certificate
# ---------------------------------------------------------------------------

def twofreq_offline_certificate(c1, c2, lam1, lam2, *, p=None, mode: str = "offline",
                                ) -> TwoFreqOfflineCert:
    """Build and EXACTLY self-check an off-line displacement certificate.

    `c1`, `c2`: coefficient literals from :func:`gauss` / :func:`inv_sqrt` /
    :func:`real_sqrt`.  `lam1`, `lam2`: frequency literals from :func:`rat` /
    :func:`neglog`.  `mode='displacement'` additionally certifies `Im x = 1/2` and is
    accepted ONLY for the Euler-factor shape `twoFreq 1 (-(1/sqrt p)) 0 (-(log p))`.

    Every refusal is listed in the module docstring.  conjecture1_proved = False.
    """
    ns1 = _coef_normsq(c1, "c1")
    ns2 = _coef_normsq(c2, "c2")
    if ns1 == 0 or ns2 == 0:
        raise ValueError("twofreq_offline: coefficients must be nonzero (|c|^2 > 0)")

    v1, v2 = _lam_value(lam1, "lam1"), _lam_value(lam2, "lam2")
    if sp.simplify(v1 - v2) == 0:
        raise ValueError(
            f"twofreq_offline: frequencies must differ; lam1 = lam2 = {v1} (note log 1 = 0, "
            f"so neglog(1) IS rat(0))")
    # The emitted separation for a rational-vs-(-log p) pair is `-log p < 0 <= r`.
    for a, b in ((lam1, lam2), (lam2, lam1)):
        if a[0] == "rat" and b[0] == "neglog" and sp.nsimplify(a[1]) < 0:
            raise ValueError(
                "twofreq_offline: a rational frequency opposite a -log p frequency must be "
                f"nonnegative (the emitted separation is -log p < 0 <= r); got {a[1]}")

    # THE anti-phantom self-check (and the exact complement of selfinversive_rigidity).
    if ns1 == ns2:
        raise ValueError(
            f"twofreq_offline: |c1|^2 = |c2|^2 = {ns1} -- equal modulus means the sum IS "
            f"real-rooted (twoFreq_realRooted_iff), so the emitted negation would be FALSE; "
            f"refused.  Use the selfinversive_rigidity emitter for that regime.")

    if mode not in ("offline", "displacement"):
        raise ValueError(f"twofreq_offline: unknown mode {mode!r}")

    is_p_family = (
        c1 == ("gauss", sp.Integer(1), sp.Integer(0))
        and c2[0] == "inv_sqrt" and c2[1] == -1
        and lam1 == ("rat", sp.Integer(0))
        and lam2[0] == "neglog" and int(lam2[1]) == int(c2[2])
    )
    p_val = int(c2[2]) if is_p_family else (int(p) if p is not None else None)
    if p is not None and is_p_family and int(p) != int(c2[2]):
        raise ValueError(
            f"twofreq_offline: declared p = {p} disagrees with the Euler-factor literals "
            f"(p = {int(c2[2])})")
    if is_p_family and p_val < 2:
        raise ValueError(f"twofreq_offline: the Euler-factor parameter needs p >= 2; got {p_val}")
    if mode == "displacement":
        if not is_p_family:
            raise ValueError(
                "twofreq_offline: mode='displacement' certifies Im x = 1/2 for the Euler-factor "
                "shape twoFreq 1 (-(1/sqrt p)) 0 (-(log p)) ONLY; this instance is not that "
                "shape, and the displacement of a general pair is -(log(|c1|/|c2|))/(lam2-lam1), "
                "not 1/2.  Refused rather than guessed.")
        if p_val < 2:
            raise ValueError(f"twofreq_offline: the Euler-factor parameter needs p >= 2; got {p_val}")

    return TwoFreqOfflineCert(
        c1=tuple(c1), c2=tuple(c2), lam1=tuple(lam1), lam2=tuple(lam2),
        normsq1=sp.nsimplify(ns1), normsq2=sp.nsimplify(ns2),
        p=p_val if is_p_family else None,
        displacement=sp.Rational(1, 2) if (is_p_family and mode == "displacement") else None,
        mode=mode,
    )


def certify_twofreq_offline_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` -- a dict with keys ``c1``,
    ``c2``, ``lam1``, ``lam2`` and optional ``p`` / ``mode``."""
    spec = dict(family.special[1](pt))
    cert = twofreq_offline_certificate(
        spec["c1"], spec["c2"], spec["lam1"], spec["lam2"],
        p=spec.get("p"), mode=spec.get("mode", "offline"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

def _coef_lean(c: tuple) -> str:
    tag = c[0]
    if tag == "gauss":
        re, im = sp.nsimplify(c[1]), sp.nsimplify(c[2])
        if im == 0:
            return rat_lean(re)
        return f"({rat_lean(re)} + {rat_lean(im)} * Complex.I : ℂ)"
    if tag == "inv_sqrt":
        sign, s = int(c[1]), sp.nsimplify(c[2])
        inner = f"1 / Real.sqrt {rat_lean(s)}"
        body = f"-({inner})" if sign < 0 else f"({inner})"
        return f"(({body} : ℝ) : ℂ)"
    if tag == "real_sqrt":
        q, s = sp.nsimplify(c[1]), sp.nsimplify(c[2])
        return f"(({rat_lean(q)} * Real.sqrt {rat_lean(s)} : ℝ) : ℂ)"
    raise ValueError(f"twofreq_offline: unknown coefficient literal {tag!r}")


def _lam_lean(lam: tuple) -> str:
    if lam[0] == "rat":
        return rat_lean(sp.nsimplify(lam[1]))
    return f"(-(Real.log {int(lam[1])}))"


def _coef_ne_tac(c: tuple, ind: str) -> str:
    """Tactic block proving the coefficient literal is nonzero."""
    tag = c[0]
    if tag == "gauss":
        return f"{ind}norm_num [Complex.ext_iff]"
    if tag == "inv_sqrt":
        s = rat_lean(sp.nsimplify(c[2]))
        sign = int(c[1])
        pos = f"1 / Real.sqrt {s}"
        return (
            f"{ind}have hs : (0 : ℝ) < Real.sqrt {s} := Real.sqrt_pos.mpr (by norm_num)\n"
            f"{ind}intro hzero\n"
            f"{ind}have hre := Complex.ofReal_eq_zero.mp hzero\n"
            f"{ind}have hp : (0 : ℝ) < {pos} := by positivity\n"
            f"{ind}linarith" if sign < 0 else
            f"{ind}have hs : (0 : ℝ) < Real.sqrt {s} := Real.sqrt_pos.mpr (by norm_num)\n"
            f"{ind}intro hzero\n"
            f"{ind}have hre := Complex.ofReal_eq_zero.mp hzero\n"
            f"{ind}have hp : (0 : ℝ) < {pos} := by positivity\n"
            f"{ind}linarith")
    if tag == "real_sqrt":
        q, s = rat_lean(sp.nsimplify(c[1])), rat_lean(sp.nsimplify(c[2]))
        return (
            f"{ind}have hs : (0 : ℝ) < Real.sqrt {s} := Real.sqrt_pos.mpr (by norm_num)\n"
            f"{ind}intro hzero\n"
            f"{ind}have hre := Complex.ofReal_eq_zero.mp hzero\n"
            f"{ind}exact absurd hre (mul_ne_zero (by norm_num) hs.ne')")
    raise ValueError(f"twofreq_offline: unknown coefficient literal {tag!r}")


def _lam_ne_tac(lam1: tuple, lam2: tuple, ind: str) -> str:
    """Tactic block proving the two frequency literals differ."""
    t1, t2 = lam1[0], lam2[0]
    if t1 == "rat" and t2 == "rat":
        return f"{ind}norm_num"
    if t1 == "neglog" and t2 == "neglog":
        a, b = int(lam1[1]), int(lam2[1])
        lo, hi = (a, b) if a < b else (b, a)
        return (
            f"{ind}intro hlog\n"
            f"{ind}have hlt := Real.log_lt_log (show (0 : ℝ) < {lo} by norm_num) "
            f"(show ({lo} : ℝ) < {hi} by norm_num)\n"
            f"{ind}linarith")
    # one rational (necessarily >= 0, enforced at certify time) against one -log p (< 0)
    p = int(lam1[1]) if t1 == "neglog" else int(lam2[1])
    return (
        f"{ind}have hlp := Real.log_pos (show (1 : ℝ) < {p} by norm_num)\n"
        f"{ind}intro hlog\n"
        f"{ind}linarith")


def _normsq_tac(c: tuple, ns: sp.Rational, ind: str) -> str:
    """Tactic block evaluating `Complex.normSq c` to its EXACT rational value."""
    tag = c[0]
    if tag == "gauss":
        return f"{ind}norm_num [Complex.normSq_apply]"
    if tag == "inv_sqrt":
        sign, s = int(c[1]), sp.nsimplify(c[2])
        neg = "neg_mul_neg, " if sign < 0 else ""
        return (
            f"{ind}rw [Complex.normSq_ofReal, {neg}div_mul_div_comm, one_mul,\n"
            f"{ind}  Real.mul_self_sqrt (show (0 : ℝ) ≤ {rat_lean(s)} by norm_num)]")
    if tag == "real_sqrt":
        q, s = sp.nsimplify(c[1]), sp.nsimplify(c[2])
        return (
            f"{ind}rw [Complex.normSq_ofReal]\n"
            f"{ind}have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ {rat_lean(s)} by norm_num)\n"
            f"{ind}linear_combination ({rat_lean(q)} ^ 2 : ℝ) * hss")
    raise ValueError(f"twofreq_offline: unknown coefficient literal {tag!r}")


_BRIDGE_HYP = (
    "    (hiff : ∀ (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ), c₁ ≠ 0 → c₂ ≠ 0 → lam₁ ≠ lam₂ →\n"
    "      ((∀ x : ℂ, twoFreq c₁ c₂ lam₁ lam₂ x = 0 → x.im = 0) ↔ ‖c₁‖ = ‖c₂‖))\n"
)

#: The island definition, copied VERBATIM from TwoFreqRigidity.lean:40-42 -- the prelude a
#: plain-Mathlib (negative-control) elaboration needs.
TWOFREQ_PRELUDE = """noncomputable section
namespace Quasicrystal

-- ===== TwoFreqRigidity.lean:40-42 (v4.32 quasicrystal island), VERBATIM =====
def twoFreq (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) : ℂ :=
  c₁ * Complex.exp ((lam₁ : ℂ) * x * Complex.I)
    + c₂ * Complex.exp ((lam₂ : ℂ) * x * Complex.I)

end Quasicrystal
end

open Quasicrystal
"""


@dataclass
class TwoFreqOfflineEmitter(Emitter):
    """Emit the NOT-real-rooted direction of `Quasicrystal.twoFreq_realRooted_iff` from the
    EXACT rational inequality `|c1|^2 != |c2|^2`, plus the existence corollary and (for the
    Euler-factor family) the certified displacement `Im x = 1/2`.  One instance per point.

    The emitted file imports the in-island `TwoFreqRigidity`, so it builds inside the
    quasicrystal island.  `bridge=True` on :meth:`emit_theorem` renders the same arithmetic
    against plain Mathlib with the island iff as an explicit hypothesis -- the form the
    negative-control harness elaborates."""

    def __post_init__(self):
        self.kind = "twofreq_offline"

    # ---- per-instance renderer (also the negative-control adapter's entry point) ----
    def emit_theorem(self, cert: TwoFreqOfflineCert, name: str, *, bridge: bool = False) -> str:
        c1, c2 = _coef_lean(cert.c1), _coef_lean(cert.c2)
        l1, l2 = _lam_lean(cert.lam1), _lam_lean(cert.lam2)
        ns1, ns2 = rat_lean(cert.normsq1), rat_lean(cert.normsq2)
        iff_call = "hiff _ _ _ _ hc1 hc2 hlam" if bridge else \
            "twoFreq_realRooted_iff _ _ _ _ hc1 hc2 hlam"
        p_txt = f"p = {cert.p}" if cert.p is not None else "a two-frequency section"

        head = (
            f"/-- **Off-line displacement** ({name}): the two-frequency sum\n"
            f"    `F(x) = c₁·e^{{iλ₁x}} + c₂·e^{{iλ₂x}}` with `|c₁|² = {cert.normsq1}` and\n"
            f"    `|c₂|² = {cert.normsq2}` is NOT real-rooted -- some zero lies strictly off the\n"
            f"    real line.  By `Quasicrystal.twoFreq_realRooted_iff` real-rootedness is\n"
            f"    EQUIVALENT to `‖c₁‖ = ‖c₂‖`, and the two moduli differ EXACTLY, so the\n"
            f"    universal statement is refuted.  Ladder rung T2 ({p_txt}).\n"
            f"    A finite section fact; nothing about ζ or RH.  conjecture1_proved = False. -/\n"
        )
        # In bridge mode the island iff rides in as an explicit hypothesis, so the
        # signature opens with the binder instead of a bare `:`.
        sig = (f"theorem {name}\n{_BRIDGE_HYP}    :\n    " if bridge
               else f"theorem {name} :\n    ")
        out = [head, sig]
        out.append(
            f"\u00ac (\u2200 x : \u2102, twoFreq {c1} {c2} {l1} {l2} x = 0 \u2192 x.im = 0) := by\n"
            f"  have hc1 : ({c1} : \u2102) \u2260 0 := by\n{_coef_ne_tac(cert.c1, '    ')}\n"
            f"  have hc2 : ({c2} : \u2102) \u2260 0 := by\n{_coef_ne_tac(cert.c2, '    ')}\n"
            f"  have hlam : ({l1} : \u211d) \u2260 ({l2}) := by\n{_lam_ne_tac(cert.lam1, cert.lam2, '    ')}\n"
            f"  rw [{iff_call}]\n"
            f"  intro h\n"
            f"  have h2 : Complex.normSq ({c1}) = Complex.normSq ({c2}) := by\n"
            f"    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]\n"
            f"  have hns1 : Complex.normSq ({c1}) = ({ns1} : \u211d) := by\n"
            f"{_normsq_tac(cert.c1, cert.normsq1, '    ')}\n"
            f"  have hns2 : Complex.normSq ({c2}) = ({ns2} : \u211d) := by\n"
            f"{_normsq_tac(cert.c2, cert.normsq2, '    ')}\n"
            f"  rw [hns1, hns2] at h2\n"
            f"  norm_num at h2\n\n"
        )
        if bridge:
            return "".join(out)

        # Existence corollary: the negation, unpacked, so the off-line zero is visible.
        out.append(
            f"/-- Existence form of `{name}`: an explicit zero off the real line.\n"
            f"    conjecture1_proved = False. -/\n"
            f"theorem {name}_offline_zero :\n"
            f"    ∃ x : ℂ, twoFreq {c1} {c2} {l1} {l2} x = 0 ∧ x.im ≠ 0 := by\n"
            f"  obtain ⟨x, hx⟩ := not_forall.mp {name}\n"
            f"  exact ⟨x, (Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩\n\n"
        )
        if cert.mode == "displacement":
            out.append(self._emit_displacement(cert, name))
        return "".join(out)

    def _emit_displacement(self, cert: TwoFreqOfflineCert, name: str) -> str:
        """The p-family's certified location: EVERY zero sits at `Im x = 1/2`."""
        p = cert.p
        c1, c2 = _coef_lean(cert.c1), _coef_lean(cert.c2)
        l1, l2 = _lam_lean(cert.lam1), _lam_lean(cert.lam2)
        return (
            f"/-- **Certified displacement** ({name}_displacement): for the Euler factor\n"
            f"    `1 - {p}^(-s)` read on `s = 1/2 + i x`, EVERY zero of the section sits at\n"
            f"    `Im x = 1/2` -- i.e. on `Re s = 0`, uniformly.  The ladder's negative control:\n"
            f"    the off-line displacement is 1/2 at this rung, for this prime, with no\n"
            f"    dependence on the truncation.  conjecture1_proved = False. -/\n"
            f"theorem {name}_displacement :\n"
            f"    ∀ x : ℂ, twoFreq {c1} {c2} {l1} {l2} x = 0 → x.im = 1 / 2 := by\n"
            f"  intro x hz\n"
            f"  have hc1 : ({c1} : ℂ) ≠ 0 := by\n{_coef_ne_tac(cert.c1, '    ')}\n"
            f"  have hc2 : ({c2} : ℂ) ≠ 0 := by\n{_coef_ne_tac(cert.c2, '    ')}\n"
            f"  have hn := twoFreq_zero_norm _ _ _ _ x hc1 hc2 hz\n"
            f"  rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,\n"
            f"    abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt {p} by positivity), one_div_one_div] at hn\n"
            f"  have hlog := congrArg Real.log hn\n"
            f"  rw [Real.log_exp, Real.log_sqrt (show (0 : ℝ) ≤ {p} by norm_num)] at hlog\n"
            f"  have hl : (0 : ℝ) < Real.log {p} := Real.log_pos (by norm_num)\n"
            f"  have hkey : Real.log {p} * x.im = Real.log {p} * (1 / 2) := by linarith\n"
            f"  exact mul_left_cancel₀ hl.ne' hkey\n\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: TwoFreqOfflineCert = inst.payload  # type: ignore[assignment]
            lines.append(self.emit_theorem(cert, inst.lean_name))
            nthm += 2 + (1 if cert.mode == "displacement" else 0)
        return "".join(lines), nthm


def twofreq_offline_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a twofreq_offline family (kind='twofreq_offline').  ``spec``: ``pt -> dict`` with
    keys ``c1``, ``c2`` (coefficient literals), ``lam1``, ``lam2`` (frequency literals) and
    optional ``p`` / ``mode``.  Refuses equal modulus (the sum would be real-rooted), a zero
    coefficient, equal frequencies, and 'displacement' outside the Euler-factor shape."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("twofreq_offline", spec), constants=dict(constants or {}),
    )


def euler_factor_spec(p: int, mode: str = "displacement") -> dict:
    """The Euler-factor section at the prime `p`: `1 - p^(-s)` on `s = 1/2 + i x`."""
    return {"c1": gauss(1, 0), "c2": inv_sqrt(p, sign=-1),
            "lam1": rat(0), "lam2": neglog(p), "p": int(p), "mode": mode}


if __name__ == "__main__":
    print("=== positive cert (Euler factor p = 2) ===")
    c = twofreq_offline_certificate(**{k: v for k, v in euler_factor_spec(2).items()
                                       if k != "p" and k != "mode"},
                                    p=2, mode="displacement")
    print(f"cert OK: |c1|^2 = {c.normsq1} != |c2|^2 = {c.normsq2}; displacement {c.displacement}")
    print("\n=== NEGATIVE CONTROL: equal modulus (must raise) ===")
    try:
        twofreq_offline_certificate(gauss("3/5", "4/5"), gauss(1, 0), rat(1), rat(2))
        raise SystemExit("FAIL: equal modulus not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean ===")
    print(TwoFreqOfflineEmitter().emit_theorem(c, "euler_factor_section_offline"))
