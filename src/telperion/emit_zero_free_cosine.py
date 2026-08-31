"""Zero-free-region nonnegative-cosine-polynomial emitter.

A nonnegative cosine polynomial

    P(θ) = Σ_{k=0}^d a_k cos(k θ),      every a_k ≥ 0,   P(θ) ≥ 0,

is the analytic engine behind the classical zero-free region of ζ(s) (and its
Mossinghoff–Trudgian refinements).  The width of the region it delivers is
governed by the functional

    F(P) = (√a_1 − √a_0)² / Σ_{k≥1} a_k,

whose supremum over the nonnegative-cosine cone is the Mossinghoff–Trudgian
constant R_0 = 5.5734… .  The canonical (de la Vallée-Poussin) family
`P = (1 + cos θ)^n` realizes a monotone slice of this cone: its cosine
coefficients are the binomial autocorrelations

    a_0 = C(2n,n) / 2^n,   a_k = C(2n, n−k) / 2^{n−1}   (k ≥ 1),

and in the Chebyshev variable x = cos θ ∈ [−1, 1] it collapses to the single
factored polynomial

    p(x) = Σ_k a_k T_k(x) = (1 + x)^n ≥ 0 on [−1, 1].

So the *nonnegativity certificate* is the Fejér–Riesz / Handelman witness on the
box `{1 + x ≥ 0, 1 − x ≥ 0}`: `p(x) = 1 · (1+x)^n` — a nonnegative combination of
products of the box constraints.  This is exactly the shape
`find_handelman_certificate` finds and `HandelmanEmitter` discharges, so this
emitter REUSES that machinery: it computes the cosine cone data and F (the
zero-free-region analytic content), reduces to x = cos θ, obtains the exact
Handelman/SOS certificate, and emits kernel-ready Lean of the form

    theorem <name> : ∀ x : ℝ, 0 ≤ 1 + x → 0 ≤ 1 − x → 0 ≤ p(x) := by …

Telperion is the CERTIFICATE CHECKER.  The generator (this file, sympy) is
UNTRUSTED: everything is exact rational arithmetic, the Handelman reconstruction
is re-verified (`p − Σ c_α ∏ ℓ^α = 0`), every coefficient is checked nonnegative,
and the Chebyshev reduction `Σ a_k T_k(x) = p(x)` is re-verified before any Lean
is written — a decomposition that fails to reconstruct, or smuggles a negative
coefficient, is REFUSED.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .emit_handelman import find_handelman_certificate
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# --------------------------------------------------------------------------
# Nonnegative-cosine cone data (the zero-free-region analytic content).
# --------------------------------------------------------------------------
def vallee_poussin_coeffs(n: int) -> list[sp.Rational]:
    """Cosine coefficients ``[a_0, …, a_n]`` of ``P(θ) = (1 + cos θ)^n``.

    Closed form (binomial autocorrelation): ``a_0 = C(2n,n)/2^n`` and
    ``a_k = C(2n, n−k)/2^{n−1}`` for ``k ≥ 1``.  All ``a_k`` are positive
    rationals — the defining nonnegative-cosine property.  Exact and fast (no
    numerical Fourier integration).
    """
    if n < 1:
        raise ValueError(f"degree n must be ≥ 1, got {n}")
    a = [sp.Rational(sp.binomial(2 * n, n), 2 ** n)]
    for k in range(1, n + 1):
        a.append(sp.Rational(sp.binomial(2 * n, n - k), 2 ** (n - 1)))
    return a


def f_functional(a: Sequence[sp.Rational]) -> sp.Expr:
    """The zero-free-region functional ``F = (√a_1 − √a_0)² / Σ_{k≥1} a_k``.

    Exact (a sympy expression in surds); ``float(F)`` for the numeric value.
    Scale-invariant in ``a`` (numerator and denominator are both degree-1 in the
    ``a_k``), so integer-clearing the coefficients leaves ``F`` unchanged.
    """
    a = [sp.nsimplify(v) for v in a]
    if len(a) < 2:
        raise ValueError("F requires at least a_0 and a_1")
    tail = sum(a[1:])
    if tail == 0:
        raise ValueError("Σ_{k≥1} a_k = 0 — F undefined")
    return (sp.sqrt(a[1]) - sp.sqrt(a[0])) ** 2 / tail


def cosine_to_chebyshev(a: Sequence[sp.Rational], x: sp.Symbol) -> sp.Expr:
    """Reduce ``Σ_k a_k cos(k θ)`` to ``p(x) = Σ_k a_k T_k(x)`` with x = cos θ.

    ``T_k`` are Chebyshev polynomials of the first kind (``cos k θ = T_k(cos θ)``),
    so on ``x ∈ [−1, 1]`` nonnegativity of ``p`` is nonnegativity of ``P``.
    Returned expanded in ``x`` (exact rational coefficients).
    """
    return sp.expand(sum(sp.nsimplify(a[k]) * sp.chebyshevt(k, x)
                         for k in range(len(a))))


def clear_denominators(p: sp.Expr, a: Sequence[sp.Rational],
                       x: sp.Symbol) -> tuple[sp.Expr, sp.Integer]:
    """Scale ``p(x)`` by the LCM ``s`` of the *cosine-coefficient* denominators;
    return ``(s·p, s)``.  ``s`` is a positive integer, so nonnegativity is
    preserved and the (scale-invariant) F-functional is unchanged.

    This yields the MINIMAL integer-cleared normalization — the ``2·(x+1)^2``
    (d=2) / ``4·(1+x)^3`` (d=3) form (the denominators of ``a`` are the natural
    obstruction to integrality).  The literature's ``8·(1+x)^3`` uses the
    non-minimal ``2^n`` binomial scaling; the minimal LCM here is the canonical
    exact-arithmetic choice.
    """
    s = sp.Integer(1)
    for c in a:
        s = sp.ilcm(int(s), int(sp.Rational(c).q))
    return sp.expand(sp.Integer(s) * p), sp.Integer(s)


# --------------------------------------------------------------------------
# Certification (anti-phantom: everything re-verified exactly).
# --------------------------------------------------------------------------
def certify_zero_free_cosine_point(family, pt, name):
    """Certify one nonnegative-cosine instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(n, scale) = family.special[1](pt)`` — the de la Vallée-Poussin
    degree ``n`` and an optional integer-clearing flag ``scale``.  Builds the
    cosine cone data, reduces to ``p(x)`` on ``[−1, 1]``, obtains the exact
    Handelman/Fejér–Riesz certificate on ``{1+x ≥ 0, 1−x ≥ 0}``, and RE-VERIFIES:

      * every cosine coefficient ``a_k`` is a nonnegative rational (the cone);
      * ``Σ a_k T_k(x) = p(x)`` exactly (the Chebyshev reduction);
      * the Handelman reconstruction ``p = Σ c_α ∏ ℓ^α`` is exact;
      * every Handelman coefficient ``c_α`` is a nonnegative rational.

    Refuses (raises ``ValueError``) on any failure — no Lean for a non-certificate.
    """
    spec = family.special[1](pt)
    n, scale = spec if isinstance(spec, tuple) else (spec, True)
    x = sp.Symbol("x")

    # 1. cosine cone data + nonnegativity of the coefficients (the cone property)
    a = vallee_poussin_coeffs(int(n))
    checks = 0
    for k, ak in enumerate(a):
        akr = sp.nsimplify(ak)
        if not akr.is_rational:
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: coefficient a_{k}={ak} is "
                "not rational")
        if akr < 0:
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: NEGATIVE cosine coefficient "
                f"a_{k}={ak} — not a nonnegative-cosine polynomial")
        checks += 1

    # 2. reduce to x = cos θ, re-verify the Chebyshev identity exactly
    p_rat = cosine_to_chebyshev(a, x)
    recon_cheb = sp.expand(sum(sp.nsimplify(a[k]) * sp.chebyshevt(k, x)
                               for k in range(len(a))))
    if sp.expand(p_rat - recon_cheb) != 0:
        raise ValueError(
            f"zero_free_cosine '{name}' REFUSED: Chebyshev reduction "
            f"Σ a_k T_k(x) ≠ p(x) (residual {sp.expand(p_rat - recon_cheb)})")
    checks += 1

    p = p_rat
    scale_used = sp.Integer(1)
    if scale:
        p, scale_used = clear_denominators(p_rat, a, x)
        if sp.expand(p - scale_used * p_rat) != 0:
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: integer scaling corrupted p")
        checks += 1

    # 3. exact Handelman / Fejér–Riesz certificate on the box {1+x, 1-x}
    constraints = [(1 + x, "hx1"), (1 - x, "hx2")]
    terms = find_handelman_certificate(
        p, [g for g, _h in constraints], (x,), max_deg=int(n))
    if terms is None:
        raise ValueError(
            f"zero_free_cosine '{name}' REFUSED: no Fejér–Riesz/Handelman "
            f"certificate for p(x) on [−1, 1] up to degree {n}")

    # 4. re-verify the Handelman reconstruction exactly + coefficient nonnegativity
    recon = sp.Integer(0)
    for coef, exps in terms:
        cr = sp.nsimplify(coef)
        if not cr.is_rational:
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: Handelman coefficient {coef} "
                "not rational")
        if cr < 0:
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: NEGATIVE Handelman "
                f"coefficient {coef}")
        if len(exps) != len(constraints) or any(int(e) != e or e < 0 for e in exps):
            raise ValueError(
                f"zero_free_cosine '{name}' REFUSED: bad exponent vector {exps}")
        term = cr
        for (g, _h), e in zip(constraints, exps):
            term *= sp.sympify(g) ** int(e)
        recon += term
        checks += 1
    if sp.expand(p - recon) != 0:
        raise ValueError(
            f"zero_free_cosine '{name}' REFUSED: certificate does not reconstruct "
            f"p — residual {sp.expand(p - recon)}")
    checks += 1

    F = f_functional(a)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(int(n), a, p, list(constraints), list(terms), scale_used, F),
    )
    return inst, checks


@dataclass
class ZeroFreeCosineEmitter(Emitter):
    """Emit ``0 ≤ p(x)`` on ``[−1, 1]`` for the Chebyshev reduction of a
    nonnegative-cosine polynomial, from its Fejér–Riesz/Handelman certificate
    ``p = Σ c_α ∏ ℓ^α``.  Same Lean shape as `HandelmanEmitter`: each product term
    is nonnegative by a `mul_nonneg`/`pow_nonneg` fold over the box hypotheses,
    `ring` closes the identity, `linarith` sums.  A doc line records the degree,
    the cosine coefficients, and the F-functional value (the zero-free-region
    content).  Deterministic: grid order, then terms as certified."""

    def __post_init__(self):
        self.kind = "zero_free_cosine"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        x = sp.Symbol("x")
        syms = (x,)
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            n, a, p, constraints, terms, scale_used, F = inst.payload  # type: ignore[misc]
            p_s = expr_lean(sp.expand(p), syms)
            hyps = [(hyp, expr_lean(sp.expand(sp.sympify(g)), syms))
                    for g, hyp in constraints]
            hyp_arrows = "".join(f" (0:ℝ) ≤ {gs} →" for _h, gs in hyps)
            intro_hyps = " ".join(h for h, _g in hyps)

            haves, summands = [], []
            for j, (coef, exps) in enumerate(terms, start=1):
                factors = [rat_lean(sp.nsimplify(coef))]
                proof = f"(by norm_num : (0:ℝ) ≤ {rat_lean(sp.nsimplify(coef))})"
                for (h, gs), e in zip(hyps, exps):
                    if int(e) == 0:
                        continue
                    factors.append(f"({gs})^{int(e)}")
                    proof = f"mul_nonneg ({proof}) (pow_nonneg {h} {int(e)})"
                term_s = " * ".join(factors)
                haves.append(f"  have t{j} : (0:ℝ) ≤ {term_s} := {proof}")
                summands.append(term_s)
            rhs = " + ".join(summands)

            a_str = ", ".join(str(v) for v in a)
            scale_note = f", cleared ×{scale_used}" if scale_used != 1 else ""
            lines.append(
                f"-- {inst.lean_name}: zero-free-region nonnegative-cosine "
                f"polynomial P(θ)=(1+cos θ)^{n}.\n"
                f"-- cosine coeffs a_k = [{a_str}] (all ≥ 0); "
                f"F=(√a₁−√a₀)²/Σ_{{k≥1}}a_k ≈ {float(F):.6f}.\n"
                f"-- In x=cos θ: p(x)=Σ a_k T_k(x){scale_note}; nonneg on [−1,1] "
                f"by the Fejér–Riesz/Handelman witness p = Σ c_α ∏ ℓ^α.\n"
                f"theorem {inst.lean_name} : ∀ {x} : ℝ,{hyp_arrows} "
                f"(0:ℝ) ≤ {p_s} := by\n"
                f"  intro {x} {intro_hyps}\n"
                + "\n".join(haves) + "\n"
                f"  have hid : ({p_s} : ℝ) = {rhs} := by ring\n"
                f"  rw [hid]; linarith\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def zero_free_cosine_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a zero-free-region nonnegative-cosine family (kind='zero_free_cosine').

    ``spec``: ``pt -> n`` or ``pt -> (n, scale)`` where ``n`` is the de la
    Vallée-Poussin degree (``P = (1+cos θ)^n``) and ``scale`` (default ``True``)
    integer-clears the Chebyshev coefficients (the ``8·(1+x)^3`` normalization).
    ``certify_zero_free_cosine_point`` builds the cone data + F, reduces to
    ``x = cos θ``, obtains the Fejér–Riesz/Handelman certificate, and re-verifies
    everything exactly — refusing on any failure.
    """
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("x"),),
        grid=grid,
        lean_name=lean_name,
        special=("zero_free_cosine", spec),
        constants=dict(constants or {}),
    )


# --------------------------------------------------------------------------
# Self-test: run as `PYTHONPATH=telperion/src python3 -m
# telperion.emit_zero_free_cosine`.
# --------------------------------------------------------------------------
def _self_test() -> None:
    x = sp.Symbol("x")

    class _Fam:
        def __init__(self, spec):
            self.symbols = (x,)
            self.special = ("zero_free_cosine", spec)

    print("=== zero-free-cosine self-test ===\n")

    # d = 2, 3, 4: certificate + exact reconstruction + factored form + F
    for n in (2, 3, 4):
        fam = _Fam(lambda pt, n=n: (n, True))
        inst, nchecks = certify_zero_free_cosine_point(fam, {}, f"cos_d{n}")
        deg, a, p, constraints, terms, scale_used, F = inst.payload
        assert sp.expand(p - scale_used * cosine_to_chebyshev(a, x)) == 0
        # exact Handelman reconstruction
        recon = sum((sp.nsimplify(c) * sp.prod([sp.sympify(g) ** int(e)
                    for (g, _h), e in zip(constraints, exps)]))
                    for c, exps in terms)
        assert sp.expand(p - recon) == 0, f"reconstruction failed d={n}"
        print(f"d={n}: a={a}")
        print(f"      p(x) = {sp.factor(p)}  (cleared ×{scale_used})")
        print(f"      Handelman terms = {terms}")
        print(f"      F = {F} ≈ {float(F):.6f}   ({nchecks} exact checks)\n")

    # emitted Lean for d=3 — must be the 8·(1+x)^3 certificate
    emitter = ZeroFreeCosineEmitter()
    fam3 = _Fam(lambda pt: (3, True))
    inst3, _ = certify_zero_free_cosine_point(fam3, {}, "zero_free_cosine_d3")

    class _EmitFam:
        pass
    ef = _EmitFam()
    ef.instances = [inst3]
    body, ncount = emitter.emit_body(ef, None)
    print("=== emitted Lean (d=3) ===")
    print(body)
    print(f"({ncount} theorem emitted)\n")

    # F sweep d = 2..8
    print("=== F-functional sweep (de la Vallée-Poussin family) ===")
    for n in range(2, 9):
        a = vallee_poussin_coeffs(n)
        F = f_functional(a)
        print(f"d={n}: F ≈ {float(F):.6f}")

    # negative control: a hand-forged bad certificate must be refused
    print("\n=== negative control ===")

    def _bad_spec(pt):
        return (2, True)

    # monkeypatch the RUNNING module's globals (under `python -m` the running
    # module is `__main__`, so patch this function's own globals, not a
    # re-imported copy): force a wrong Handelman term via a corrupted finder.
    g = globals()
    orig = g["find_handelman_certificate"]
    try:
        g["find_handelman_certificate"] = lambda *args, **kw: [
            (sp.Rational(1), (1, 0))]  # wrong degree: (1+x)^1, not (1+x)^2
        try:
            certify_zero_free_cosine_point(_Fam(_bad_spec), {}, "bad")
            print("FAIL: forged certificate NOT refused")
        except ValueError as e:
            print(f"PASS: forged certificate refused — {str(e)[:70]}…")
    finally:
        g["find_handelman_certificate"] = orig


if __name__ == "__main__":
    _self_test()
