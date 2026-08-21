"""Real-Nullstellensatz emitter — a polynomial vanishes on the REAL variety of an
ideal.

The ordinary `NullstellensatzEmitter` proves `p = 0` on the (complex) variety
`V(g) = {g_k = 0}`.  A polynomial can vanish on the REAL points without lying in
the ideal (e.g. `x` vanishes on the real variety of `x² + y²` — which is just the
origin — yet `x ∉ ⟨x²+y²⟩`).  The Real Nullstellensatz certifies exactly this: `p`
vanishes on the real variety iff, for some `m` and sum of squares `s`,

    p^{2m} + s ≡ Σ_k h_k·g_k      (i.e.  p^{2m} + s ∈ ⟨g_1, …, g_n⟩).

Telperion is given `p`, the multiplicity `m`, and the SOS `s`, and COMPUTES the
cofactors `h_k` by Gröbner reduction of `p^{2m} + s` (a nonzero remainder is a
refusal).  The emitted Lean derives `p = 0`: on the variety the ideal side is
`0`, so `p^{2m} = −s ≤ 0`; but `p^{2m} = (p^m)² ≥ 0`, forcing `p^{2m} = 0` and
hence `p = 0`:

    theorem <name> : ∀ x y : ℝ, g_1 = 0 → … → g_n = 0 → p = 0 := by
      intro x y e_1 … e_n
      have hpow : (0:ℝ) ≤ p^(2m) := by positivity
      have hsos : (0:ℝ) ≤ s := by positivity
      have key : p^(2m) + s = 0 := by linear_combination h_1*e_1 + … + h_n*e_n
      have hz : p^(2m) = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp hz
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, expr_lean_raw, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _sos_expr(terms) -> sp.Expr:
    return sum((sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in terms), sp.Integer(0))


def find_real_nullstellensatz_certificate(p, gens, syms, max_m: int = 2):
    """SEARCH for a real-Nullstellensatz certificate: `(m, sos_terms)` with
    `p^{2m} + s ∈ ⟨gens⟩` and `s = Σ c_i b_i²` an exact sum of squares.

    Exact and sympy-only (no SDP): for m = 1, …, max_m the Gröbner normal form
    `s = NF(−p^{2m})` is the canonical candidate (any valid `s` is congruent to
    it mod the ideal), and `sos_decompose` attempts an exact rational SOS of
    it.  A hit is re-verified against the certifier's own gate — plain
    `sp.reduced` division by the ORIGINAL generator list — so the finder never
    returns a certificate the certifier would refuse.  The finder is untrusted
    (`certify_real_nullstellensatz_point` re-checks everything); a miss is a
    refusal, never a wrong theorem.  Returns ``(m, terms)`` or ``None``."""
    from .sos import sos_decompose

    p = sp.expand(sp.sympify(p))
    gens = [sp.expand(sp.sympify(g)) for g in gens]
    syms = tuple(syms)
    try:
        basis = sp.groebner(gens, *syms)
    except Exception:
        return None
    for m in range(1, max_m + 1):
        target = sp.expand(-(p ** (2 * m)))
        try:
            _, s = basis.reduce(target)
        except Exception:
            continue
        s = sp.expand(s)
        cert = sos_decompose(s, syms)
        if cert is None:
            continue
        terms = [(sp.Rational(c), sp.sympify(b)) for c, b in cert.terms]
        try:
            _, rem = sp.reduced(sp.expand(p ** (2 * m) + _sos_expr(terms)),
                                gens, *syms)
        except Exception:
            continue
        if sp.expand(rem) == 0:
            return m, terms
    return None


def certify_real_nullstellensatz_point(family, pt, name):
    """Certify one real-Nullstellensatz instance: (CertifiedInstance, n_checks).

    Reads (p, m, sos, gens) = family.special[1](pt): the target `p`, the
    multiplicity `m` (so the even power is `2m`), the SOS term list `sos` for `s`,
    and the ideal generators `gens`.  Reduces ``p^{2m} + s`` by the generators;
    certifies iff the remainder is zero (membership) and every SOS coefficient is
    nonnegative.  Refuses otherwise — `p` is not certified to vanish on the real
    variety by this `(m, s)`.

    FINDER mode: ``m = None`` (or ``sos = None``) searches for `(m, s)` — first
    the exact sympy-only `find_real_nullstellensatz_certificate` (no cvxpy, for
    the quick CI path), then the SDP `sdp_finder.find_real_nullstellensatz` as a
    fallback for cases outside `sos_decompose`'s v1 SOS class.  A miss by both is
    a refusal."""
    p, m, sos, gens = family.special[1](pt)
    p = sp.expand(sp.sympify(p))
    gens = [sp.expand(sp.sympify(g)) for g in gens]
    syms = tuple(family.symbols)
    if m is None or sos is None:
        # FINDER mode: SEARCH for (m, s).  Two finders, tried in order of cost:
        #   1. the exact, sympy-only Gröbner-NF + `sos_decompose` finder — no
        #      cvxpy, so it runs on the cvxpy-free `quick` CI path;
        #   2. the SDP finder (`sdp_finder.find_real_nullstellensatz`) as a
        #      fallback for cases outside `sos_decompose`'s v1 SOS class.
        # Both return the same (m, s_terms) interface and are untrusted — the
        # certifier below re-reduces regardless — so trying the cheap one first
        # never changes correctness, only which certificate is emitted.
        max_m = int(family.constants.get("real_nullstellensatz_max_m", 2))
        found = find_real_nullstellensatz_certificate(p, gens, syms, max_m=max_m)
        if found is None:
            # SDP fallback for cases outside `sos_decompose`'s v1 class.  cvxpy
            # is imported lazily inside the SDP solver; on the cvxpy-free CI path
            # that ImportError means the fallback is simply unavailable, so the
            # sympy miss stands as the refusal — never a leaked ImportError.
            from .sdp_finder import find_real_nullstellensatz
            m_max = int(family.constants.get("real_nss_m_max", 3))
            half_deg = int(family.constants.get("real_nss_half_deg", 1))
            try:
                found = find_real_nullstellensatz(p, gens, syms, m_max=m_max,
                                                  half_deg=half_deg)
            except ImportError:
                found = None
        if found is None:
            raise ValueError(
                f"real_nullstellensatz '{name}' REFUSED: no Real-Nullstellensatz "
                f"certificate (p^2m + s ∈ ⟨gₖ⟩, s SOS) found — p may not vanish "
                "on the real variety, or the search missed (a refusal, not a "
                "disproof)")
        m, sos = found

    m = int(m)
    if m < 1:
        raise ValueError(f"real_nullstellensatz '{name}' REFUSED: m must be ≥ 1")
    for c, _b in sos:
        if not sp.nsimplify(c).is_rational or sp.nsimplify(c) < 0:
            raise ValueError(
                f"real_nullstellensatz '{name}' REFUSED: SOS coefficient {c} is not "
                "a nonnegative rational")

    s = _sos_expr(sos)
    S = sp.expand(p ** (2 * m) + s)
    try:
        cofactors, remainder = sp.reduced(S, gens, *syms)
    except Exception as e:  # pragma: no cover
        raise ValueError(
            f"real_nullstellensatz '{name}' REFUSED: reduction failed ({e})") from e
    if sp.expand(remainder) != 0:
        raise ValueError(
            f"real_nullstellensatz '{name}' REFUSED: p^(2m) + s does not reduce to "
            f"0 modulo the generators (remainder {sp.expand(remainder)}) — not in "
            "the ideal for this (m, s)")
    checks = 2

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(p, m, list(sos), gens, [sp.expand(c) for c in cofactors]),
    )
    return inst, checks


@dataclass
class RealNullstellensatzEmitter(Emitter):
    """Emit `∀x, (⋀ g_k = 0) → p = 0` on the REAL variety from a real-Nullstellensatz
    certificate `p^{2m} + s = Σ h_k g_k` (`s` a sum of squares).  Deterministic
    order: grid order."""

    def __post_init__(self):
        self.kind = "real_nullstellensatz"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        binder = " ".join(str(s) for s in syms)
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            p, m, sos, gens, cofactors = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            exp = 2 * m
            pow_s = f"({p_s})^{exp}"
            s_s = " + ".join(
                f"{rat_lean(sp.nsimplify(c))} * ({expr_lean_raw(sp.sympify(b), syms)})^2"
                for c, b in sos) or "0"
            hyp_names = [f"e{i}" for i in range(1, len(gens) + 1)]
            arrows = "".join(
                f" {expr_lean(sp.expand(g), syms)} = 0 →" for g in gens)
            combo = " + ".join(
                f"({expr_lean(sp.expand(h), syms)}) * {hn}"
                for h, hn in zip(cofactors, hyp_names) if sp.expand(h) != 0) or "0"

            lines.append(
                f"-- {inst.lean_name}: Real-Nullstellensatz certificate  p^(2m) + s "
                f"= Σ h_k·g_k (s a sum of squares) — p vanishes on the REAL variety.\n"
                f"theorem {inst.lean_name} : ∀ {binder} : ℝ,{arrows} "
                f"{p_s} = 0 := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  have hpow : (0:ℝ) ≤ {pow_s} := by positivity\n"
                f"  have hsos : (0:ℝ) ≤ {s_s} := by positivity\n"
                f"  have key : {pow_s} + ({s_s}) = 0 := by linear_combination {combo}\n"
                f"  have hz : {pow_s} = 0 := by linarith\n"
                f"  exact (pow_eq_zero_iff (by norm_num)).mp hz\n"
            )
            n += 1
        return "\n".join(lines), n


def real_nullstellensatz_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a real-Nullstellensatz family (kind='real_nullstellensatz').

    spec: ``pt -> (p, m, sos, gens)`` — the target `p`, multiplicity `m` (even
    power `2m`), the SOS term list `sos` for `s`, and the ideal generators `gens`.
    ``certify_real_nullstellensatz_point`` reduces ``p^{2m} + s`` by the generators
    and refuses if it is not in the ideal.

    FINDER mode: return ``m = None, sos = None`` and Telperion SEARCHES for the
    certificate (`find_real_nullstellensatz_certificate`, exact and sympy-only,
    m ≤ constant ``real_nullstellensatz_max_m``, default 2) — upgrading the
    emitter from "you supply (m, s)" to "you supply the ideal."
    """
    if not tuple(symbols):
        raise ValueError("real-Nullstellensatz families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("real_nullstellensatz", spec),
        constants=dict(constants or {}),
    )
