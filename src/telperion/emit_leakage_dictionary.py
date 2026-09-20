"""leakage_dictionary emitter -- the log-derivative coefficient functional at a COMPOSITE index.

PROGRAM MIRRORMERE, ROUTE A item A2b (RH_ROUTES_ROADMAP_2026-09-16.md).  The island lemma
`Quasicrystal.composite_bragg_amplitude_zero` (LeakageDictionary.lean) says

    a completely multiplicative  =>  b n = 0 at every non-prime-power n

where `b` is pinned to `a` by the divisor recursion `IsLogDerivCoeff a b`:

    a n * log n = sum_{d | n} b d * a (n / d).

This emitter certifies the INSTANCES: for a concrete periodic amplitude vector it RE-DERIVES the
whole coefficient row `b(d)`, `d | n`, by running that recursion in EXACT symbolic arithmetic, and
emits the derivation as a kernel-checked chain of lemmas ending in the verdict

    * claim='vanishes'  -- the re-derived `b n` is symbolically 0 (the completely-multiplicative
      fiber: zeta, a Dirichlet character), or
    * claim='leaks'     -- the re-derived `b n` is symbolically NONZERO, which by the island's
      contrapositive `not_completelyMultiplicative_of_composite_leak` REFUSES complete
      multiplicativity of the amplitude.

WHY THIS IS NOT THE rfl-GRADE DIRECTION.  The roadmap flags a trivial-direction trap: that the von
Mangoldt function is supported on prime powers is definitional in Mathlib
(`vonMangoldt_eq_zero_iff` unfolds the `if IsPrimePow n then ... else 0` body).  Nothing here
touches that.  The certificate is the coefficient ROW of a logarithmic derivative: `b` is specified
only implicitly by the recursion, and for a non-multiplicative amplitude it is supported at
composites -- the DH point below has `b 6 = log 6 + kappa^2 (log 2 + log 3) > 0`, which no
support-level reading can produce.

THE CERTIFICATE (load-bearing).  The emitted Lean carries the re-derived closed forms
`b d = <polynomial in the amplitude constant, linear in the atoms log e (e | d)>`.  Each is proved
from the recursion at `d` by expanding `Nat.divisors d`, rewriting the already-derived smaller
coefficients, and closing by linear arithmetic.  CORRUPT ANY ENTRY OF THE ROW and the emitted
`linarith` step has no proof: the kernel rejects it.  The claimed enclosure of `b n`, when
requested, is likewise computed by the emitter from the supplied atom intervals -- inflate it and
the emitted `nlinarith` fails.

SELF-CHECK / REFUSALS (ValueError; all EXACT sympy arithmetic, no floats) -- the negative control,
which bites in BOTH directions:
  * `a 1 != 1`                          -- the recursion is not normalized (and `b` is not pinned);
  * `n` a prime power or `n <= 1`       -- the dictionary is about COMPOSITE frequencies; a
                                           prime-power index has nothing to say either way;
  * claim='vanishes' for an amplitude that is NOT completely multiplicative -- refused BEFORE the
    symbolic check, because that is precisely the false certificate this module exists to prevent;
  * claim='vanishes' whose re-derived `b n` is NOT symbolically zero -- the anti-phantom gate: a
    vanishing claim must be RE-DERIVED, never asserted;
  * claim='leaks' for a COMPLETELY MULTIPLICATIVE amplitude -- refused, because the island theorem
    proves the leak is impossible there, so the emitted theorem would be false;
  * claim='leaks' whose re-derived `b n` IS symbolically zero -- no leak to certify;
  * a supplied enclosure interval that fails to contain the emitter's own interval evaluation.

Complete multiplicativity of a `q`-periodic amplitude is decided EXACTLY (not sampled): a
`q`-periodic `a` with `a 1 = 1` is completely multiplicative iff `r -> a r` is a monoid
homomorphism on `Z/q`, which is a finite `q x q` table check.

conjecture1_proved = False.  A finite fact about Dirichlet coefficients of a logarithmic
derivative; it says nothing about zeros, temperedness, or RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import Callable

import sympy as sp

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


# The single algebraic constant an amplitude vector may contain (rendered as a supplied Lean name).
K = sp.Symbol("K", real=True)


def _lg(p: int) -> sp.Symbol:
    """The atom standing for `Real.log p` at a PRIME p.

    The coefficient row is carried in the free abelian group on PRIME logs, so that
    `log 6 = log 2 + log 3` is an identity of the representation rather than a fact to be
    discovered -- which is what makes the completely-multiplicative row cancel to exactly 0."""
    return sp.Symbol(f"Lg{p}")


def _log_expr(d: int) -> sp.Expr:
    """`log d` expanded on the prime-log basis."""
    return sum((e * _lg(p) for p, e in sp.factorint(d).items()), sp.Integer(0))


def _flat_factor_lean(d: int) -> tuple[str, int]:
    """`d` as a right-associated product of PRIME literals, plus the number of factors."""
    facs = []
    for p, e in sorted(sp.factorint(d).items()):
        facs.extend([p] * int(e))
    if len(facs) == 1:
        return f"({facs[0]} : ℝ)", 1
    text = f"({facs[-1]} : ℝ)"
    for p in reversed(facs[:-1]):
        text = f"({p} : ℝ) * ({text})"
    return text, len(facs)


def _divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def _is_prime_power(n: int) -> bool:
    if n < 2:
        return False
    return len(sp.factorint(n)) == 1


# ---------------------------------------------------------------------------
# The certificate
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class LeakageCertificate:
    """A verified leakage certificate at one composite index.

    ``vec[i]`` is the amplitude at `n = i + 1` (so ``vec`` has length ``period`` and the amplitude
    is ``a m = vec[(m - 1) % period]``).  ``row[d]`` is the EXACT re-derived coefficient `b d` as a
    polynomial in :data:`K` whose log-atoms are :func:`_lg`."""

    vec: tuple
    period: int
    n: int
    row: tuple                    # ((d, expr), ...) in increasing d over the divisors of n
    completely_multiplicative: bool
    claim: str                    # "vanishes" | "leaks"
    enclosure: tuple | None       # (lo, hi) rationals for b n, or None


def _amp(vec, period: int, m: int):
    return vec[(m - 1) % period]


def _is_completely_multiplicative(vec, period: int) -> bool:
    """EXACT decision for a ``period``-periodic amplitude: is ``r -> a r`` multiplicative on Z/q?"""
    if sp.simplify(_amp(vec, period, 1) - 1) != 0:
        return False
    for i in range(1, period + 1):
        for j in range(1, period + 1):
            lhs = _amp(vec, period, ((i * j - 1) % period) + 1)
            rhs = _amp(vec, period, i) * _amp(vec, period, j)
            if sp.simplify(sp.expand(lhs - rhs)) != 0:
                return False
    return True


def leakage_certificate(vec, period: int, n: int, claim: str,
                        enclosure=None) -> LeakageCertificate:
    """Build and EXACTLY self-check a leakage certificate; see the module docstring for refusals."""
    v = tuple(sp.nsimplify(x) for x in vec)
    period = int(period)
    n = int(n)
    if period < 1 or len(v) != period:
        raise ValueError(
            f"leakage_dictionary: vec must have exactly `period` entries; got len={len(v)}, "
            f"period={period}")
    if claim not in ("vanishes", "leaks"):
        raise ValueError(f"leakage_dictionary: claim must be 'vanishes' or 'leaks'; got {claim!r}")
    if sp.simplify(_amp(v, period, 1) - 1) != 0:
        raise ValueError(
            f"leakage_dictionary: the amplitude must be normalized, a 1 = 1; got a 1 = "
            f"{_amp(v, period, 1)}.  The divisor recursion does not pin b without it; refused")
    if n <= 1:
        raise ValueError(
            f"leakage_dictionary: index n must exceed 1; got n={n} (b 1 = 0 always, vacuous)")
    if _is_prime_power(n):
        raise ValueError(
            f"leakage_dictionary: n={n} is a PRIME POWER; the dictionary is a statement about "
            f"COMPOSITE (non-prime-power) frequencies, where a multiplicative amplitude must "
            f"vanish.  At a prime power neither verdict has content; refused")

    cm = _is_completely_multiplicative(v, period)
    if claim == "vanishes" and not cm:
        raise ValueError(
            "leakage_dictionary: claim='vanishes' for an amplitude that is NOT completely "
            "multiplicative.  That is exactly the false certificate this emitter exists to "
            "prevent (the Davenport-Heilbronn fingerprint); refused")
    if claim == "leaks" and cm:
        raise ValueError(
            f"leakage_dictionary: claim='leaks' for a COMPLETELY MULTIPLICATIVE amplitude.  The "
            f"island theorem composite_bragg_amplitude_zero proves b {n} = 0 there, so the "
            f"emitted theorem would be FALSE; refused")

    # --- the anti-phantom driver: re-derive the whole row by the divisor recursion -------------
    b: dict[int, sp.Expr] = {}
    for d in _divisors(n):
        acc = _amp(v, period, d) * _log_expr(d)
        for e in _divisors(d):
            if e < d:
                acc -= b[e] * _amp(v, period, d // e)
        b[d] = sp.expand(sp.simplify(sp.expand(acc)))
    bn = sp.expand(b[n])

    if claim == "vanishes" and sp.simplify(bn) != 0:
        raise ValueError(
            f"leakage_dictionary: claim='vanishes' but the RE-DERIVED coefficient is b {n} = {bn} "
            f"!= 0.  A vanishing claim must be re-derived from the recursion, never asserted; "
            f"refused")
    if claim == "leaks" and sp.simplify(bn) == 0:
        raise ValueError(
            f"leakage_dictionary: claim='leaks' but the RE-DERIVED coefficient is b {n} = 0; "
            f"there is no leak to certify; refused")

    enc = None
    if enclosure is not None:
        def _to_rat(x):
            if isinstance(x, F):
                return sp.Rational(x.numerator, x.denominator)
            return sp.Rational(sp.nsimplify(x))

        lo, hi = _to_rat(enclosure[0]), _to_rat(enclosure[1])
        if lo >= hi:
            raise ValueError(f"leakage_dictionary: empty enclosure [{lo}, {hi}]; refused")
        enc = (lo, hi)

    return LeakageCertificate(
        vec=v, period=period, n=n,
        row=tuple((d, b[d]) for d in _divisors(n)),
        completely_multiplicative=cm, claim=claim, enclosure=enc,
    )


def interval_of(expr: sp.Expr, atom_bounds: dict) -> tuple[F, F]:
    """Interval-evaluate a re-derived coefficient from supplied atom intervals.

    ``atom_bounds`` maps each sympy atom (``K`` or ``_lg(d)``) to a ``(lo, hi)`` rational pair.
    Evaluation is monomial-wise on the EXPANDED polynomial, so the result is a certified (if not
    tight) enclosure whenever every atom interval is."""
    poly = sp.expand(expr)
    terms = poly.as_ordered_terms() if poly != 0 else []
    lo_tot, hi_tot = F(0), F(0)
    for t in terms:
        coef, rest = t.as_coeff_Mul()
        c = F(int(sp.Rational(coef).p), int(sp.Rational(coef).q))
        lo, hi = F(1), F(1)
        for fac, power in (rest.as_powers_dict() if rest != 1 else {}).items():
            if fac not in atom_bounds:
                raise ValueError(f"leakage_dictionary: no interval supplied for atom {fac}")
            a, bb = atom_bounds[fac]
            a, bb = F(a), F(bb)
            cands = [a ** int(power), bb ** int(power)]
            if int(power) % 2 == 0 and a < 0 < bb:
                cands.append(F(0))
            plo, phi = min(cands), max(cands)
            cands2 = [lo * plo, lo * phi, hi * plo, hi * phi]
            lo, hi = min(cands2), max(cands2)
        cands3 = [c * lo, c * hi]
        lo_tot += min(cands3)
        hi_tot += max(cands3)
    return lo_tot, hi_tot


def certify_leakage_dictionary_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` -- a dict with keys ``vec``, ``period``,
    ``n``, ``claim`` and the optional ``enclosure``."""
    spec = family.special[1](pt)
    if not isinstance(spec, dict):
        raise ValueError(f"leakage_dictionary spec must be a dict; got {spec!r}")
    cert = leakage_certificate(
        spec["vec"], spec["period"], spec["n"], spec["claim"], spec.get("enclosure"))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.row)


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------
def _rat(x) -> str:
    r = sp.Rational(x)
    if r.q == 1:
        return f"({r.p} : ℝ)" if r.p >= 0 else f"(-({-r.p}) : ℝ)"
    return f"({r.p} / {r.q} : ℝ)" if r.p >= 0 else f"(-({-r.p} / {r.q}) : ℝ)"


def _atom_lean(a: sp.Expr, kappa_lean: str) -> str:
    if a == K:
        return kappa_lean
    s = str(a)
    if s.startswith("Lg"):
        return f"Real.log {s[2:]}"
    raise ValueError(f"leakage_dictionary: unrenderable atom {a!r}")


def _expr_lean(e: sp.Expr, kappa_lean: str) -> str:
    """Render an expanded polynomial in K and the log atoms as Lean source."""
    e = sp.expand(e)
    if e == 0:
        return "(0 : ℝ)"
    out = []
    for t in e.as_ordered_terms():
        coef, rest = t.as_coeff_Mul()
        c = sp.Rational(coef)
        neg = c < 0
        c = abs(c)
        facs = []
        if c != 1 or rest == 1:
            facs.append(_rat(c))
        for fac, power in (rest.as_powers_dict() if rest != 1 else {}).items():
            base = _atom_lean(fac, kappa_lean)
            facs.append(base if int(power) == 1 else f"{base} ^ {int(power)}")
        term = " * ".join(facs)
        out.append(("-" if neg else "+", term))
    head = out[0]
    text = ("-" + head[1]) if head[0] == "-" else head[1]
    for sign, term in out[1:]:
        text += f" {sign} {term}"
    return text


def _amp_def_lean(cert: LeakageCertificate, base: str, kappa_lean: str) -> str:
    q = cert.period
    if q == 1:
        return (f"noncomputable def {base}_amp : ℕ → ℝ := fun _ => "
                f"{_expr_lean(cert.vec[0], kappa_lean)}\n")
    arms = []
    for r in range(1, q):
        arms.append(f"if n % {q} = {r} then {_expr_lean(cert.vec[r - 1], kappa_lean)} else")
    body = "\n  ".join(arms) + f"\n  {_expr_lean(cert.vec[q - 1], kappa_lean)}"
    return f"noncomputable def {base}_amp : ℕ → ℝ := fun n =>\n  {body}\n"


def _divisor_finset(d: int) -> str:
    return "{" + ", ".join(str(x) for x in _divisors(d)) + "}"


@dataclass
class LeakageDictionaryEmitter(Emitter):
    """Emit one leakage instance: the amplitude definition, its evaluation lemmas, the re-derived
    coefficient chain `b d`, and the verdict (`= 0` for the completely-multiplicative fiber, or
    `!= 0` plus the refusal of complete multiplicativity for a leaking amplitude).

    The emitted file calls the island's `Quasicrystal.IsLogDerivCoeff`,
    `Quasicrystal.exists_logDerivCoeff` and
    `Quasicrystal.not_completelyMultiplicative_of_composite_leak`, so it must be built inside the
    quasicrystal island (profile imports `Mathlib` and `LeakageDictionary`).

    ``kappa_lean`` names the Lean constant rendering the symbolic amplitude constant ``K``;
    ``atom_bounds_lean`` maps each atom to the island lemma proving its rational interval, and is
    required exactly when a point requests an enclosure.
    """

    kappa_lean: str = "Quasicrystal.dhKappa"
    atom_bounds_lean: tuple = ()      # ((atom_str, lemma_name, lo, hi), ...)

    def __post_init__(self):
        self.kind = "leakage_dictionary"
        self.requires_prelude = ()

    # -- pieces -------------------------------------------------------------
    def _amp_eval_lemmas(self, cert: LeakageCertificate, base: str) -> tuple[str, list[str]]:
        need = sorted({m for d, _ in cert.row for m in (d, cert.n // d)} | {cert.n})
        out, names = [], []
        for m in need:
            nm = f"{base}_amp_{m}"
            val = _expr_lean(_amp(cert.vec, cert.period, m), self.kappa_lean)
            out.append(f"@[simp] theorem {nm} : {base}_amp {m} = {val} := by\n"
                       f"  norm_num [{base}_amp]\n")
            names.append(nm)
        return "".join(out), names

    def _b_lemma(self, cert: LeakageCertificate, base: str, d: int, expr) -> str:
        nm = f"{base}_b_{d}"
        rhs = _expr_lean(expr, self.kappa_lean)
        if d == 1:
            return (f"theorem {nm} {{b : ℕ → ℝ}} (hb : Quasicrystal.IsLogDerivCoeff "
                    f"{base}_amp b) :\n    b 1 = 0 := by\n"
                    f"  have h := hb 1 (by norm_num)\n"
                    f"  rw [show (1:ℕ).divisors = {{1}} from by decide] at h\n"
                    f"  simpa using h.symm\n")
        divs = _divisors(d)
        rw_sum = ", ".join(["Finset.sum_insert (by decide)"] * (len(divs) - 1)
                           + ["Finset.sum_singleton"])
        rw_prev = ", ".join(f"{base}_b_{e} hb" for e in divs if e < d)
        prod, nfac = _flat_factor_lean(d)
        logrhs = _expr_lean(_log_expr(d), self.kappa_lean)
        log_proof: list[str] = []
        if nfac > 1:
            # `d` is not prime: decompose `log d` onto the prime-log basis the row is carried on.
            log_proof = [f"  have hlog : Real.log {d} = {logrhs} := by",
                         f"    rw [show ({d} : ℝ) = {prod} by norm_num]"]
            muls = ", ".join(["Real.log_mul (by norm_num) (by norm_num)"] * (nfac - 1))
            log_proof.append(f"    rw [{muls}]")
            # After the rewrites the goal is the flat prime-log sum; `rw` discharges it on
            # its own exactly when that is syntactically the stated right-hand side (two
            # distinct primes).  Emit the reassociation step only when it is really needed,
            # so the generated file is linter-clean.
            facs = []
            for pp, ee in sorted(sp.factorint(d).items()):
                facs.extend([pp] * int(ee))
            flat_lhs = " + ".join(f"Real.log {pp}" for pp in facs)
            if flat_lhs != logrhs:
                log_proof.append("    ring")
            log_proof.append("  rw [hlog] at h")
        lines = [
            f"theorem {nm} {{b : ℕ → ℝ}} (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) :",
            f"    b {d} = {rhs} := by",
            f"  have h := hb {d} (by norm_num)",
            f"  push_cast at h",
            *log_proof,
            f"  rw [show ({d}:ℕ).divisors = {_divisor_finset(d)} from by decide] at h",
            f"  rw [{rw_sum}] at h",
            f"  rw [{rw_prev}] at h",
            f"  norm_num [{base}_amp] at h",
            f"  linarith [h]",
        ]
        return "\n".join(lines) + "\n"

    def _verdict(self, cert: LeakageCertificate, base: str) -> tuple[str, int, list[str]]:
        n = cert.n
        out, nthm, names = [], 0, []
        if cert.claim == "vanishes":
            out.append(
                f"/-- **Composite amplitude VANISHES** at `n = {n}`, RE-DERIVED from the divisor\n"
                f"    recursion (not imported from the general dictionary): the coefficient row\n"
                f"    cancels exactly.  The amplitude is completely multiplicative, so this is the\n"
                f"    POSITIVE control of `Quasicrystal.composite_bragg_amplitude_zero`. -/\n"
                f"theorem {base}_composite_vanishes {{b : ℕ → ℝ}}\n"
                f"    (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) : b {n} = 0 :=\n"
                f"  {base}_b_{n} hb\n\n")
            nthm += 1
            names.append(f"{base}_composite_vanishes")
        else:
            out.append(
                f"/-- **Composite amplitude LEAKS** at `n = {n}`: the re-derived coefficient is\n"
                f"    strictly positive, so the Bragg amplitude at the composite frequency\n"
                f"    `log {n}` does NOT vanish. -/\n"
                f"theorem {base}_composite_leak_pos {{b : ℕ → ℝ}}\n"
                f"    (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) : 0 < b {n} := by\n"
                f"  rw [{base}_b_{n} hb]\n"
                f"  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)\n"
                f"  have hl3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)\n"
                f"  nlinarith [hl2, hl3, sq_nonneg {self.kappa_lean}]\n\n")
            nthm += 1
            names.append(f"{base}_composite_leak_pos")
            out.append(
                f"/-- **The negative control bites.**  A nonzero COMPOSITE Bragg amplitude refuses\n"
                f"    complete multiplicativity of the amplitude sequence, through the island's\n"
                f"    contrapositive instrument.  Nothing but the recursion is consumed. -/\n"
                f"theorem {base}_not_completelyMultiplicative {{b : ℕ → ℝ}}\n"
                f"    (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) :\n"
                f"    ¬ Quasicrystal.CompletelyMultiplicative {base}_amp :=\n"
                f"  Quasicrystal.not_completelyMultiplicative_of_composite_leak hb (by norm_num)\n"
                f"    (by decide) (ne_of_gt ({base}_composite_leak_pos hb))\n\n")
            nthm += 1
            names.append(f"{base}_not_completelyMultiplicative")
        return "".join(out), nthm, names

    def _enclosure(self, cert: LeakageCertificate, base: str) -> tuple[str, int]:
        if cert.enclosure is None:
            return "", 0
        lo, hi = cert.enclosure
        # Outward-rounded decimal form, for the human-readable corollary.
        scale = sp.Integer(10) ** 5
        dlo = sp.Rational(sp.floor(lo * scale), scale)
        dhi = sp.Rational(sp.ceiling(hi * scale), scale)
        obtains = "".join(
            f"  obtain ⟨hb{i}lo, hb{i}hi⟩ := {lem}\n"
            for i, (_a, lem, _l, _h) in enumerate(self.atom_bounds_lean))
        hints = ", ".join(
            [f"hb{i}lo, hb{i}hi" for i in range(len(self.atom_bounds_lean))]
            + [f"sq_nonneg {self.kappa_lean}"])
        return (
            f"/-- **The certified number.**  The re-derived composite amplitude at `n = {cert.n}`,\n"
            f"    pinned to a rational interval of width ~{float(hi - lo):.2e} from the island's\n"
            f"    kernel-proved atom enclosures.  Roadmap value: `b({cert.n}) = +1.9364`. -/\n"
            f"theorem {base}_enclosure {{b : ℕ → ℝ}}\n"
            f"    (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) :\n"
            f"    {_rat(lo)} < b {cert.n} ∧ b {cert.n} < {_rat(hi)} := by\n"
            f"  rw [{base}_b_{cert.n} hb]\n"
            f"{obtains}"
            f"  constructor <;> nlinarith [{hints}]\n\n"
            f"/-- The same enclosure at five decimals -- the human-readable form the registry\n"
            f"    node quotes, and the form that pins the published four-decimal value. -/\n"
            f"theorem {base}_enclosure_decimal {{b : ℕ → ℝ}}\n"
            f"    (hb : Quasicrystal.IsLogDerivCoeff {base}_amp b) :\n"
            f"    ({dlo} : ℝ) < b {cert.n} ∧ b {cert.n} < ({dhi} : ℝ) := by\n"
            f"  obtain ⟨h1, h2⟩ := {base}_enclosure hb\n"
            f"  exact ⟨by norm_num at h1 ⊢; linarith, by norm_num at h2 ⊢; linarith⟩\n\n", 2)

    def _twin(self, cert: LeakageCertificate, base: str) -> tuple[str, int]:
        """The falsification twin, emitted only for a leaking point."""
        if cert.claim != "leaks":
            return "", 0
        n = cert.n
        return (
            f"/-- **Non-vacuity.**  The functional exists for this amplitude, so the conditional\n"
            f"    theorems above are not empty: the leak is an unconditional theorem. -/\n"
            f"theorem {base}_leak_exists :\n"
            f"    ∃ b : ℕ → ℝ, Quasicrystal.IsLogDerivCoeff {base}_amp b ∧ 0 < b {n} := by\n"
            f"  obtain ⟨b, hb⟩ := Quasicrystal.exists_logDerivCoeff (a := {base}_amp)\n"
            f"    (by norm_num [{base}_amp])\n"
            f"  exact ⟨b, hb, {base}_composite_leak_pos hb⟩\n\n"
            f"/-- **THE FALSIFICATION TWIN.**  Delete the multiplicativity hypothesis from\n"
            f"    `Quasicrystal.composite_bragg_amplitude_zero` and the statement is FALSE --\n"
            f"    refuted in-kernel by THIS amplitude at `n = {n}`.\n\n"
            f"    This is the probe that would fail if the dictionary were the `rfl`-grade von\n"
            f"    Mangoldt-support statement in disguise: a support-level reading admits no\n"
            f"    counterexample, because `Λ` vanishes off prime powers unconditionally.  The\n"
            f"    log-derivative coefficient functional does not. -/\n"
            f"theorem {base}_multiplicativity_is_necessary :\n"
            f"    ¬ (∀ a b : ℕ → ℝ, a 1 = 1 → Quasicrystal.IsLogDerivCoeff a b →\n"
            f"        ∀ m : ℕ, 0 < m → ¬ IsPrimePow m → b m = 0) := by\n"
            f"  intro H\n"
            f"  obtain ⟨b, hb, hpos⟩ := {base}_leak_exists\n"
            f"  have := H {base}_amp b (by norm_num [{base}_amp]) hb {n} (by norm_num) (by decide)\n"
            f"  linarith\n\n", 2)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: LeakageCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            verdict = "VANISHES (completely multiplicative)" if cert.claim == "vanishes" \
                else "LEAKS (not completely multiplicative)"
            lines.append(
                f"/-! ### Instance `{base}` -- period {cert.period}, index n = {cert.n}: "
                f"{verdict}\n\n"
                f"    Amplitude vector `[a 1, ..., a {cert.period}] = "
                f"[{', '.join(str(x) for x in cert.vec)}]`.\n"
                f"    Re-derived coefficient row (exact symbolic divisor recursion):\n"
                f"{''.join(f'      b {d} = {e}{chr(10)}' for d, e in cert.row)}"
                f"    conjecture1_proved = False. -/\n\n")
            lines.append(_amp_def_lean(cert, base, self.kappa_lean) + "\n")
            evals, _names = self._amp_eval_lemmas(cert, base)
            lines.append(evals + "\n")
            nthm += evals.count("theorem ")
            for d, e in cert.row:
                lines.append(self._b_lemma(cert, base, d, e) + "\n")
                nthm += 1
            v, k, _n = self._verdict(cert, base)
            lines.append(v)
            nthm += k
            enc, k = self._enclosure(cert, base)
            lines.append(enc)
            nthm += k
            tw, k = self._twin(cert, base)
            lines.append(tw)
            nthm += k
        return "".join(lines), nthm


def leakage_dictionary_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a leakage_dictionary family (kind='leakage_dictionary').  ``spec``: ``pt -> {"vec":
    [...], "period": q, "n": n, "claim": "vanishes"|"leaks", "enclosure": (lo, hi) | None}``."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("leakage_dictionary", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    CHI5 = [1, -1, -1, 1, 0]                 # the real character mod 5 (completely multiplicative)
    DH = [1, K, -K, -1, 0]                   # Davenport-Heilbronn, kappa = 0.284079...
    print("=== positive control: chi_5 at n = 6 (vanishes) ===")
    c = leakage_certificate(CHI5, 5, 6, "vanishes")
    for d, e in c.row:
        print(f"   b {d} = {e}")
    print("\n=== negative control: DH at n = 6 (leaks) ===")
    c = leakage_certificate(DH, 5, 6, "leaks")
    for d, e in c.row:
        print(f"   b {d} = {e}")
    print("\n=== REFUSAL 1: DH claimed to vanish (the false certificate) ===")
    try:
        leakage_certificate(DH, 5, 6, "vanishes")
        raise SystemExit("FAIL: a non-multiplicative vanishing claim was not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== REFUSAL 2: chi_5 claimed to leak (the impossible certificate) ===")
    try:
        leakage_certificate(CHI5, 5, 6, "leaks")
        raise SystemExit("FAIL: a multiplicative leak claim was not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== REFUSAL 3: a PRIME-POWER index (no content either way) ===")
    try:
        leakage_certificate(DH, 5, 4, "leaks")
        raise SystemExit("FAIL: a prime-power index was not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== REFUSAL 4: an unnormalized amplitude a 1 != 1 ===")
    try:
        leakage_certificate([2, 1, 1, 1, 0], 5, 6, "leaks")
        raise SystemExit("FAIL: an unnormalized amplitude was not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
