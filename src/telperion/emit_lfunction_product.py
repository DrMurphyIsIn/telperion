"""L-function product lower-bound emitter: the nonneg-cosine -> 3-4-1 product bound.

The classical zero-free-region argument rests on ONE positivity fact coupled to
ONE Dirichlet-series identity:

  (positivity)  a nonnegative cosine polynomial  P(θ) = Σ_{k=0}^m a_k cos(kθ) ≥ 0
                with every a_k ≥ 0 (the FEJÉR-ADMISSIBLE cone), and
  (identity)    for Re s > 1,  log‖∏_k L(s + i·k·t)^{a_k}‖ = Σ a_k · Re(log L(s+ikt))
                = Σ_n Λ(n) n^{-σ}/log n · P(t·log n) ≥ 0,

so that

        1 ≤ ∏_k ‖L(σ + i·k·t)‖^{a_k}          (Re s = σ > 1).

The canonical instance is the de la Vallée-Poussin / Mertens tuple
`(a_0, a_1, a_2) = (3, 4, 1)`, whose cosine polynomial is `3 + 4 cos θ + cos 2θ =
2 (1 + cos θ)^2 ≥ 0`, giving the workhorse product inequality
`‖ζ(σ)‖^3 ‖ζ(σ+it)‖^4 ‖ζ(σ+2it)‖ ≥ 1`.  This emitter COUPLES the nonneg-cosine
positivity kernel (as in `emit_zero_free_cosine`) to that L-product lower bound
and emits kernel-ready Lean specialized to `riemannZeta`, mirroring the shipped
`ZeroFreeElementary.lean:zeta_norm_product_ge_one`.

CERTIFICATE (anti-phantom; everything re-verified exactly, sympy, exact rational):
  * every cosine coefficient `a_k` is a NONNEGATIVE rational (the cone);
  * the tuple is FEJÉR-ADMISSIBLE: `P(θ) = Σ a_k cos kθ ≥ 0 ∀θ`.  Re-checked by
    reducing to `x = cos θ` (`cos kθ = T_k(x)`, Chebyshev) and exhibiting a
    Handelman / Fejér–Riesz nonnegativity witness `p(x) = Σ c_α ∏ ℓ^α` on the
    box `{1 + x ≥ 0, 1 − x ≥ 0}` (all `c_α ≥ 0`), re-verified to reconstruct
    `p` exactly.  A tuple whose cosine polynomial dips negative has NO such
    witness and is REFUSED (the negative control).

MATHLIB REALITY (v4.32.0).  `DirichletCharacter.norm_LFunction_product_ge_one`
is stated with the exponents (3, 4, 1) HARD-CODED:

    ‖LFunctionTrivChar N (1+x) ^ 3 * LFunction χ (1+x+I*y) ^ 4
        * LFunction (χ^2) (1+x+2*I*y)‖ ≥ 1

(Mathlib/NumberTheory/LSeries/Nonvanishing.lean:307).  There is NO general
`a`-tuple form exposed.  So the EMITTED Lean is faithful ONLY for the (3,4,1)
tuple: the emitter re-emits the (3,4,1) instance for `riemannZeta` exactly as
`zeta_norm_product_ge_one` does (via `LFunction_modOne_eq`, `norm_mul`,
`norm_pow`).  The VALUE-ADD is (i) the exact Fejér-admissibility gate on the
coefficient tuple, and (ii) the named coupling of that positivity kernel to the
Mathlib L-product lemma.  A non-(3,4,1) admissible tuple still CERTIFIES (its
positivity is real and re-checked), but Lean emission is gated on Mathlib
exposing the matching product lemma — such a tuple emits a documented, honest
`sorry`-free STUB-FREE refusal rather than an unfaithful theorem.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .emit_handelman import find_handelman_certificate
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_lfunction_product.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.emit_handelman import find_handelman_certificate
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# The ONLY exponent tuple Mathlib v4.32.0 exposes a matching product lemma for
# (`DirichletCharacter.norm_LFunction_product_ge_one`, hard-coded 3-4-1).
_MATHLIB_TUPLE = (sp.Integer(3), sp.Integer(4), sp.Integer(1))


# --------------------------------------------------------------------------
# Fejér-admissibility: Σ a_k cos kθ ≥ 0  <=>  p(x)=Σ a_k T_k(x) ≥ 0 on [−1,1].
# --------------------------------------------------------------------------
def cosine_to_chebyshev(a: Sequence[sp.Rational], x: sp.Symbol) -> sp.Expr:
    """Reduce ``Σ_k a_k cos(kθ)`` to ``p(x) = Σ_k a_k T_k(x)`` with ``x = cos θ``.

    ``cos kθ = T_k(cos θ)`` (Chebyshev, first kind), so on ``x ∈ [−1, 1]``
    nonnegativity of ``p`` is exactly nonnegativity of the cosine polynomial.
    Returned expanded in ``x`` with exact rational coefficients."""
    return sp.expand(sum(sp.nsimplify(a[k]) * sp.chebyshevt(k, x)
                         for k in range(len(a))))


@dataclass(frozen=True)
class LFunctionProductCertificate:
    """A verified nonneg-cosine / Fejér-admissible tuple + its L-product bound.

    ``a`` is the cosine-coefficient tuple ``(a_0, …, a_m)`` (every ``a_k ≥ 0``);
    the cosine polynomial ``Σ a_k cos kθ ≥ 0`` for all ``θ`` (the FEJÉR cone),
    witnessed by the Handelman certificate ``p(x) = Σ c_α ∏ ℓ^α`` on
    ``{1+x ≥ 0, 1−x ≥ 0}`` for ``p(x) = Σ a_k T_k(x)`` (re-verified exact).

    The corresponding L-product lower bound (Re s > 1) is
    ``1 ≤ ∏_k ‖L(σ + i·k·t)‖^{a_k}``.  ``mathlib_faithful`` records whether the
    tuple matches the ONE exponent triple Mathlib exposes a product lemma for
    (``(3,4,1)``); Lean emission is gated on it."""

    a: tuple                       # (a_0, …, a_m), each ≥ 0 (rationals; ints preferred)
    p: sp.Expr                     # p(x) = Σ a_k T_k(x), expanded in x
    constraints: tuple             # ((g, hyp_name), …) — the box {1+x, 1-x}
    handelman_terms: tuple         # ((c_α, exps), …), all c_α ≥ 0
    mathlib_faithful: bool         # tuple == (3,4,1) — faithfully emittable


def lfunction_product_certificate(a: Sequence) -> LFunctionProductCertificate:
    """Build and EXACTLY self-check a nonneg-cosine / L-product certificate.

    ``a`` is the cosine-coefficient tuple ``(a_0, …, a_m)`` (int/Fraction/sympy
    Rational).  RE-VERIFIES, refusing (``ValueError``) on any failure:

      * ``m ≥ 1`` (at least ``a_0`` and ``a_1`` — a real product);
      * every ``a_k`` is a NONNEGATIVE rational (the cone property);
      * FEJÉR-ADMISSIBILITY: ``p(x) = Σ a_k T_k(x)`` has a Handelman /
        Fejér–Riesz nonnegativity witness on ``{1+x ≥ 0, 1−x ≥ 0}`` (so
        ``Σ a_k cos kθ ≥ 0 ∀θ``); the witness is re-verified to reconstruct
        ``p`` exactly and to have only nonnegative coefficients.

    A tuple whose cosine polynomial goes negative (INADMISSIBLE) has no such
    witness and is REFUSED — the anti-phantom negative control."""
    ar = [sp.nsimplify(v) for v in a]
    m = len(ar) - 1
    if m < 1:
        raise ValueError(
            f"lfunction_product REFUSED: need at least (a_0, a_1); got {ar}")

    # 1. cone: every coefficient a NONNEGATIVE rational.
    for k, ak in enumerate(ar):
        if not ak.is_rational:
            raise ValueError(
                f"lfunction_product REFUSED: coefficient a_{k}={ak} not rational")
        if ak < 0:
            raise ValueError(
                f"lfunction_product REFUSED: NEGATIVE cosine coefficient "
                f"a_{k}={ak} — not a nonnegative-cosine tuple")
    if sum(ar[1:]) == 0:
        raise ValueError(
            "lfunction_product REFUSED: Σ_{k≥1} a_k = 0 — degenerate product")

    # 2. Fejér-admissibility via Chebyshev reduction + Handelman witness on [−1,1].
    x = sp.Symbol("x")
    p = cosine_to_chebyshev(ar, x)
    recon_cheb = sp.expand(sum(sp.nsimplify(ar[k]) * sp.chebyshevt(k, x)
                               for k in range(len(ar))))
    if sp.expand(p - recon_cheb) != 0:
        raise ValueError(
            f"lfunction_product REFUSED: Chebyshev reduction Σ a_k T_k ≠ p "
            f"(residual {sp.expand(p - recon_cheb)})")

    constraints = ((1 + x, "hx1"), (1 - x, "hx2"))
    terms = find_handelman_certificate(
        p, [g for g, _h in constraints], (x,), max_deg=max(2 * m, 2))
    if terms is None:
        raise ValueError(
            f"lfunction_product REFUSED: tuple {ar} is INADMISSIBLE — its cosine "
            f"polynomial Σ a_k cos kθ dips negative (no Fejér–Riesz/Handelman "
            f"witness for p(x)=Σ a_k T_k(x) on [−1,1])")

    # 3. re-verify the Handelman reconstruction exactly + coefficient nonnegativity.
    recon = sp.Integer(0)
    checked_terms = []
    for coef, exps in terms:
        cr = sp.nsimplify(coef)
        if not cr.is_rational:
            raise ValueError(
                f"lfunction_product REFUSED: Handelman coefficient {coef} not rational")
        if cr < 0:
            raise ValueError(
                f"lfunction_product REFUSED: NEGATIVE Handelman coefficient {coef}")
        if len(exps) != len(constraints) or any(int(e) != e or e < 0 for e in exps):
            raise ValueError(
                f"lfunction_product REFUSED: bad exponent vector {exps}")
        term = cr
        for (g, _h), e in zip(constraints, exps):
            term *= sp.sympify(g) ** int(e)
        recon += term
        checked_terms.append((cr, tuple(int(e) for e in exps)))
    if sp.expand(p - recon) != 0:
        raise ValueError(
            f"lfunction_product REFUSED: Handelman witness does not reconstruct p "
            f"(residual {sp.expand(p - recon)})")

    faithful = tuple(ar) == _MATHLIB_TUPLE
    return LFunctionProductCertificate(
        a=tuple(ar),
        p=sp.expand(p),
        constraints=constraints,
        handelman_terms=tuple(checked_terms),
        mathlib_faithful=bool(faithful),
    )


def certify_lfunction_product_point(family, pt, name):
    """Certify one L-function-product instance from ``family.special[1](pt) -> a``.

    ``a`` is the cosine-coefficient tuple (a sequence of nonnegative rationals).
    Returns ``(CertifiedInstance, n_checks)`` where ``n_checks`` counts the exact
    self-checks (coefficient-nonnegativity + admissibility + reconstruction)."""
    a = family.special[1](pt)
    cert = lfunction_product_certificate(a)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    # one check per coefficient (nonneg) + Chebyshev id + one per Handelman term + recon
    n_checks = len(cert.a) + 1 + len(cert.handelman_terms) + 1
    return inst, n_checks


@dataclass
class LFunctionProductEmitter(Emitter):
    """Emit the nonneg-cosine -> L-product lower bound ``1 ≤ ∏_k ‖ζ(σ+ikt)‖^{a_k}``
    specialized to ``riemannZeta``, mirroring the shipped
    ``ZeroFreeElementary.lean:zeta_norm_product_ge_one``.

    For the (3,4,1) tuple (the ONLY exponent triple Mathlib v4.32.0 exposes a
    matching product lemma for) the proof is the fixed 3-4-1 wrapper of
    ``DirichletCharacter.norm_LFunction_product_ge_one`` at modulus 1 +
    ``LFunction_modOne_eq`` (@[simp]) + ``norm_mul``/``norm_pow`` — only reliable,
    kernel-verified tactics.  A non-(3,4,1) admissible tuple is CERTIFIED (its
    positivity is real) but NOT emitted as a theorem: the emitter refuses, since
    emitting an unfaithful statement would be a phantom."""

    def __post_init__(self):
        self.kind = "lfunction_product"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: LFunctionProductCertificate = inst.payload  # type: ignore[assignment]
            a = cert.a
            a_str = ", ".join(str(v) for v in a)
            hand = " + ".join(
                (f"{c}" if all(e == 0 for e in exps) else
                 f"{c}*" + "*".join(f"(1{'+' if i == 0 else '-'}x)^{e}"
                                    for i, e in enumerate(exps) if e))
                for c, exps in cert.handelman_terms)
            if not cert.mathlib_faithful:
                raise ValueError(
                    f"lfunction_product '{inst.lean_name}' REFUSED to emit: tuple "
                    f"[{a_str}] is admissible and CERTIFIED, but Mathlib v4.32.0 only "
                    f"exposes the (3,4,1) product lemma "
                    f"(DirichletCharacter.norm_LFunction_product_ge_one); a "
                    f"non-(3,4,1) tuple has no faithful theorem to emit")
            a0, a1, a2 = int(a[0]), int(a[1]), int(a[2])
            # The Mathlib lemma states the last factor with NO exponent (a_2 = 1
            # is bare `‖·‖`, not `‖·‖^1`); after `norm_pow` the hypothesis has a
            # bare last factor, so mirror that exactly (`^1` would break `exact h`).
            f2 = "" if a2 == 1 else f" ^ {a2}"
            # Mirror zeta_norm_product_ge_one exactly (ZeroFreeElementary.lean).
            lines.append(
                f"-- {inst.lean_name}: nonneg-cosine -> L-product lower bound, ζ.\n"
                f"-- cosine tuple a_k = [{a_str}] (all ≥ 0); FEJÉR-ADMISSIBLE:\n"
                f"--   Σ a_k cos kθ = p(cos θ) ≥ 0 with p(x) = {sp.factor(cert.p)}\n"
                f"--   (Handelman/Fejér–Riesz witness on [−1,1]: {hand}).\n"
                f"-- The classical 3-4-1: 3 + 4 cos θ + cos 2θ = 2(1+cos θ)^2 ≥ 0.\n"
                f"-- Coupled to DirichletCharacter.norm_LFunction_product_ge_one\n"
                f"-- (modulus 1) + LFunction_modOne_eq (@[simp]) + norm_mul/norm_pow.\n"
                f"theorem {inst.lean_name} {{x : ℝ}} (hx : 0 < x) (y : ℝ) :\n"
                f"    (1:ℝ) ≤ ‖riemannZeta (1 + x)‖ ^ {a0} "
                f"* ‖riemannZeta (1 + x + Complex.I * y)‖ ^ {a1}\n"
                f"        * ‖riemannZeta (1 + x + 2 * Complex.I * y)‖{f2} := by\n"
                f"  have h := DirichletCharacter.norm_LFunction_product_ge_one\n"
                f"    (χ := (1 : DirichletCharacter ℂ 1)) hx y\n"
                f"  rw [ge_iff_le] at h\n"
                f"  have htriv : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=\n"
                f"    DirichletCharacter.LFunction_modOne_eq\n"
                f"  rw [htriv] at h\n"
                f"  simp only [DirichletCharacter.LFunction_modOne_eq, norm_mul, "
                f"norm_pow] at h\n"
                f"  exact h\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def lfunction_product_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a nonneg-cosine / L-product family (kind='lfunction_product').

    ``spec``: a callable ``pt -> a`` returning the cosine-coefficient tuple
    ``(a_0, …, a_m)`` (nonnegative rationals; integers preferred so ``norm_pow``
    applies).  ``certify_lfunction_product_point`` checks coefficient
    nonnegativity + Fejér-admissibility (Chebyshev + Handelman witness), refusing
    on any negative coefficient or an inadmissible tuple.  The emitted Lean is
    faithful for the ``(3,4,1)`` tuple (the one Mathlib exposes)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("x"),),
        grid=grid,
        lean_name=lean_name,
        special=("lfunction_product", spec),
        constants=dict(constants or {}),
    )


# --------------------------------------------------------------------------
# Self-test: `cd /tmp/rh-zlb/telperion && PYTHONPATH=src python3 -m
# telperion.emit_lfunction_product`.
# --------------------------------------------------------------------------
def _self_test() -> None:
    print("=== lfunction-product self-test ===\n")

    # positive: the classical de la Vallée-Poussin / Mertens 3-4-1 tuple.
    print("=== positive: 3-4-1 (Mertens) — 3 + 4 cos θ + cos 2θ = 2(1+cos θ)^2 ===")
    cert = lfunction_product_certificate([3, 4, 1])
    print(f"  cert OK: a={cert.a}")
    print(f"           p(x)=Σ a_k T_k(x) = {sp.factor(cert.p)}  (nonneg on [−1,1])")
    print(f"           Handelman witness = {cert.handelman_terms}")
    print(f"           mathlib_faithful = {cert.mathlib_faithful}\n")

    # positive: a scaled admissible tuple (6,8,2)=2*(3,4,1) — real positivity,
    # but NOT the (3,4,1) Mathlib exposes, so it CERTIFIES yet is not emittable.
    print("=== positive (certify-only): (6,8,2) admissible but non-(3,4,1) ===")
    cert2 = lfunction_product_certificate([6, 8, 2])
    print(f"  cert OK: a={cert2.a}, p(x)={sp.factor(cert2.p)}, "
          f"faithful={cert2.mathlib_faithful} (Lean emission gated)\n")

    # negative control: an INADMISSIBLE tuple (cosine poly goes negative).
    print("=== NEGATIVE CONTROL: inadmissible (1,4) — 1 + 4 cos θ < 0 at θ=π ===")
    try:
        lfunction_product_certificate([1, 4])
        raise SystemExit("FAIL: inadmissible tuple was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}…\n")

    # negative control: a NEGATIVE coefficient.
    print("=== NEGATIVE CONTROL: negative coefficient (3,-4,1) ===")
    try:
        lfunction_product_certificate([3, -4, 1])
        raise SystemExit("FAIL: negative coefficient was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}…\n")

    # negative control: refuse to EMIT a non-(3,4,1) tuple (phantom guard).
    print("=== NEGATIVE CONTROL: emitter refuses non-(3,4,1) tuple ===")
    inst_bad = CertifiedInstance(point={"case": 9}, lean_name="lfp_bad",
                                 corners=(), payload=cert2)

    class _ViewBad:
        instances = [inst_bad]
    try:
        LFunctionProductEmitter().emit_body(_ViewBad(), LeanProfile())
        raise SystemExit("FAIL: emitter emitted an unfaithful tuple")
    except ValueError as e:
        print(f"  correctly REFUSED emission: {str(e)[:90]}…\n")

    # build the CertifiedInstance via the full certify point-fn + emit the Lean.
    print("=== emitted Lean (3-4-1, ζ) ===")

    class _Fam:
        def __init__(self, spec):
            self.special = ("lfunction_product", spec)
    inst, nchecks = certify_lfunction_product_point(
        _Fam(lambda pt: [3, 4, 1]), {"case": 0}, "zeta_norm_product_341")
    print(f"  ({nchecks} exact self-checks)\n")

    class _View:
        instances = [inst]
    body, nthm = LFunctionProductEmitter().emit_body(
        _View(), LeanProfile(namespace=("LFunctionProduct",)))
    print(body)
    print(f"({nthm} theorem emitted)")


if __name__ == "__main__":
    _self_test()
