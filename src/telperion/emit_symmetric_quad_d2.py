"""Symmetric moment-matrix PSD emitter, DEGREE 2 — the symbolic-in-n three-piece
completing-the-square + Cauchy–Schwarz decomposition of the level-2 subset form.

This is the ``d = 2`` sibling of ``emit_symmetric_quad.py`` (which ships the
``d = 1`` object ``subsetForm_d1``).  The recurring object is the degree-``d``
subset-indexed knapsack *moment form*, PSD for every population size ``n``
symbolically:

    Q_d(x; n) = Σ_{|S|,|T| ≤ d}  x_S · x_T · f(n, |S ∪ T|)   ≥ 0,
    f(n, k) = Π_{j<k} (n/2 − j)/(n − j)   (the knapsack harmonic moments).

At level ``d = 2`` the index set is ``{∅} ∪ {{i}} ∪ {{i,j}}``.  Grouping by the
association-scheme orbits and collapsing the rank-one part gives the REDUCED
collective coordinates

    A   = x_∅
    s1  = Σ_i x_{i}          QY  = Σ_i x_{i}²
    s2  = Σ_{i<j} x_{i,j}    P   = Σ_{i<j} x_{i,j}²
    W   = Σ_i w_i²   (w_i = Σ_{j≠i} x_{i,j}, the row sums of the pair block)
    CYz = Σ_i x_{i} · w_i    (the y–z coupling)

in which the form is (verified entrywise-exact against the full
``1+n+C(n,2)`` moment matrix for n = 9, 11, 13, 15 — see
``examples/knapsack_sos/gen_d2_decomposition.py`` / ``D2_CERTIFICATE.md``):

    Q2 = f0·A² + 2f1·A·s1 + 2f2·A·s2 + f1·QY + f2·(s1²−QY)
       + 2f3·s1·s2 + 2(f2−f3)·CYz + f2·P + f3·(W−2P) + f4·(s2²−W+P).

THE EXACT THREE-PIECE CERTIFICATE (``D2_CERTIFICATE.md``):

    Q2 = (A + f1·s1 + f2·s2)²                     [level-0, rank one]
       + pcoef·( T2 − s1²/n )                      [level-1, centered CS]
       + a·N2                                       [level-2, projection]

where, with ``pcoef = n/(4(n−1))``, ``a = μ₂ = n(n−2)/(16(n−3)(n−1)) > 0`` (n>3),

    T2 = Σ_i t_i²      (t_i = y_i + (1/pcoef)·(Cz)_i,  Σt = s1)
       = (4·CYz·n + 4·QY·n + W·n − 8·s1·s2 − 4·s2²)/(4n)   [defining identity]

    N2 = P − (W − 4s2²/n)/(n−2) − 2s2²/(n(n−1))            [level-2 proj. norm]
       = the J(n,2) level-2 eigenspace norm  N2 ≥ 0.

The three pieces are nonnegative because (i) the level-0 term is a square;
(ii) ``pcoef ≥ 0`` and the CENTERED Cauchy–Schwarz remainder ``T2 − s1²/n ≥ 0``
(``s1²  ≤ n·T2``, the ``Σt=s1`` Cauchy–Schwarz); (iii) ``a > 0`` for n > 3 and
``N2 ≥ 0`` (the level-2 association-scheme positivity).

HONEST ALTITUDE.  Exactly like the shipped ``d = 1`` emitter — which proves the
reduced collective-coordinate form ``0 ≤ f0·A² + 2f1·A·X + f2·X² + (f1−f2)·Q``
and takes the Cauchy–Schwarz fact ``X² ≤ N·Q`` as a HYPOTHESIS rather than
re-deriving it from Finsets — this ``d = 2`` emitter proves the reduced
collective-coordinate form and takes the two level ≥ 1 nonnegativity facts as
hypotheses:

    hCSt : s1² ≤ N·T2      (the centered Cauchy–Schwarz on the t-vector)
    hN2  : 0 ≤ N2          (the level-2 J(n,2) eigenspace positivity)

together with the two exact DEFINING identities of ``T2`` and ``N2`` in the base
coordinates.  The N2-positivity fact is genuinely a THIRD, independent
association-scheme relation (``N2`` is the level-2 eigenspace norm ``μ₂`` in the
scheme; it does NOT follow from the two lower Cauchy–Schwarz facts
``W ≤ 2(n−1)P`` and ``nW ≥ 4s2²`` — those are the level-0/level-1 norms) — which
is exactly why ``D2_CERTIFICATE.md`` names ``N2 ≥ 0`` as the remaining Lean
target.  Supplying it as a hypothesis keeps the emitter at the SAME altitude as
the shipped ``d = 1`` (CS as hypothesis), while the completing-the-square /
centered-CS ASSEMBLY — the actual content — is proved symbolically in n by an
exact rational congruence (``field_simp``/``ring``).

The whole assembled identity ``Q2 = piece1 + pcoef·(T2 − s1²/n) + a·N2`` is
re-verified EXACTLY over ℚ(n) inside the certificate builder (with T2, N2
replaced by their defining expressions), and each piece is checked manifestly
nonnegative; a moment table that breaks the assembly or a piece that is not
manifestly nonneg is refused with ``ValueError`` (negative control).

conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass

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


# the free symbolic population size n (positive integer, n ≥ 4 keeps every
# denominator alive: 4(n−1), n, and 16(n−3)(n−1) with the μ₂ = a positivity).
_N = sp.Symbol("N", positive=True)


def _lean_ratfun(expr: sp.Expr) -> str:
    """Render a rational function of N as ℝ-ascribed Lean (N : ℝ in scope).

    The DENOMINATOR is rendered in FACTORED form (e.g. ``16*(N - 3)*(N - 1)``
    rather than the expanded ``16*N^2 - 64*N + 48``) so ``field_simp`` — supplied
    ``≠ 0`` for each atomic linear factor — clears every denominator instead of
    leaving a residual ``(…)⁻¹`` of an un-recognized composite quadratic."""
    expr = sp.nsimplify(sp.together(expr))
    num, den = sp.fraction(expr)
    ns = sp.sstr(sp.expand(num)).replace("**", "^")
    if den == 1:
        return f"({ns} : ℝ)"
    ds = sp.sstr(sp.factor(den)).replace("**", "^")
    return f"(({ns} : ℝ) / ({ds} : ℝ))"


def _knapsack_f(k: int) -> sp.Expr:
    """The knapsack harmonic moment f(N, k) = Π_{j<k} (N/2 − j)/(N − j)."""
    out = sp.Integer(1)
    for j in range(k):
        out *= (_N / 2 - j) / (_N - j)
    return sp.simplify(out)


@dataclass(frozen=True)
class SymmetricQuadD2Certificate:
    """A verified symbolic-in-n level-2 moment-matrix PSD certificate.

    Collective coordinates: ``A, s1, s2, QY, P, W, CYz`` (base) plus the two
    derived quantities ``T2 = Σ t_i²`` and ``N2`` (the level-2 projection norm),
    each with an exact defining identity in the base coordinates.  The reduced
    form ``Q2`` decomposes EXACTLY (symbolically in N) as

        Q2 = (A + f1·s1 + f2·s2)² + pcoef·(T2 − s1²/N) + a·N2,

    nonnegative on ``N ≥ n_min`` via the level-0 square, the centered
    Cauchy–Schwarz ``s1² ≤ N·T2`` and ``pcoef ≥ 0``, and ``a > 0`` with
    ``N2 ≥ 0``.  All coefficients are exact rational functions of N.
    """

    d: int                 # moment degree (this emitter: d = 2)
    f0: sp.Expr
    f1: sp.Expr
    f2: sp.Expr
    f3: sp.Expr
    f4: sp.Expr
    pcoef: sp.Expr         # centered-CS coefficient  n/(4(n−1))  (≥ 0)
    a: sp.Expr             # level-2 coefficient  μ₂ = n(n−2)/(16(n−3)(n−1)) (> 0, n>3)
    t2_expr: sp.Expr       # T2 defining identity in base coords
    n2_expr: sp.Expr       # N2 defining identity in base coords
    n_min: int             # domain floor: certificate stated ∀ N ≥ n_min


# the seven base collective coordinates + two derived quantities (module-level
# sympy symbols, reused by builder and emitter).
_A, _s1, _s2, _QY, _P, _W, _CYz, _T2, _N2 = sp.symbols(
    "A s1 s2 QY P W CYz T2 N2", real=True
)


def _reduced_Q2(f0, f1, f2, f3, f4) -> sp.Expr:
    """The reduced collective-coordinate level-2 form Q2 (orbit-summed, verified
    entrywise-exact against the full moment matrix — see gen_d2_decomposition)."""
    return sp.expand(
        f0 * _A**2
        + 2 * f1 * _A * _s1
        + 2 * f2 * _A * _s2
        + f1 * _QY
        + f2 * (_s1**2 - _QY)
        + 2 * f3 * _s1 * _s2
        + 2 * (f2 - f3) * _CYz
        + f2 * _P
        + f3 * (_W - 2 * _P)
        + f4 * (_s2**2 - _W + _P)
    )


def symmetric_quad_d2_certificate(
    f0, f1, f2, f3, f4, *, n_min: int = 4
) -> SymmetricQuadD2Certificate:
    """Build and EXACTLY self-check (over ℚ(N)) the level-2 symbolic-in-n
    moment-matrix PSD certificate for the harmonic moment table ``f0..f4``.

    Refuses (``ValueError``): a non-positive pivot ``f0``; a negative centered-CS
    coefficient ``pcoef``; a non-positive level-2 coefficient ``a = μ₂`` on the
    domain; or a moment table for which the exact three-piece assembly
    ``Q2 = piece1 + pcoef·(T2 − s1²/N) + a·N2`` FAILS to hold symbolically in N
    (so no symbolic-in-n completing-the-square congruence exists)."""
    N = _N
    f0, f1, f2, f3, f4 = (sp.nsimplify(sp.sympify(v)) for v in (f0, f1, f2, f3, f4))

    # ---- derived constants (the completing-square structure) ----------------
    p1 = sp.simplify(f1 - f1**2)          # y-diag
    q1 = sp.simplify(f2 - f1**2)          # y-offdiag
    pcoef = sp.simplify(p1 - q1)          # centered-CS coefficient
    c_inc = sp.simplify(f2 - f1 * f2)     # y–z cross, incident
    c_non = sp.simplify(f3 - f1 * f2)     # y–z cross, nonincident
    alpha = sp.simplify(c_inc - c_non)

    # (1) pivot must be strictly positive on the domain.
    piv_lo = sp.simplify(f0.subs(N, n_min))
    if not (piv_lo.is_number and piv_lo > 0):
        raise ValueError(
            f"REFUSED: pivot f0 = {f0} is NOT positive on N ≥ {n_min} "
            f"(negative control)"
        )

    # (2) centered-CS coefficient pcoef must be ≥ 0 on the domain.
    for k in range(n_min, n_min + 6):
        v = sp.simplify(pcoef.subs(N, k))
        if v.is_number and v < 0:
            raise ValueError(
                f"REFUSED: centered Cauchy–Schwarz coefficient pcoef = {pcoef} "
                f"is NEGATIVE at N = {k} — level-1 remainder indefinite "
                f"(negative control)"
            )

    # (3) the level-2 tie: q1 = −pcoef/N (the all-ones direction is the kernel).
    tie = sp.simplify(q1 + pcoef / N)
    if tie != 0:
        raise ValueError(
            f"REFUSED: level-2 tie q1 + pcoef/N = {tie} ≠ 0 — the centered-CS "
            f"completion does not hold (negative control)"
        )

    # kernel-compatibility of the cross block (Σ Cz = 0): N·c_non + 2·alpha = 0.
    ker = sp.simplify(N * c_non + 2 * alpha)
    if ker != 0:
        raise ValueError(
            f"REFUSED: cross-block kernel compatibility N·c_non + 2α = {ker} ≠ 0 "
            f"— the Schur (pseudo-inverse) step is not exact (negative control)"
        )

    # ---- level-2 coefficient a = μ₂ and the two defining identities ----------
    a = sp.simplify(N * (N - 2) / (16 * (N - 3) * (N - 1)))

    # (4) a = μ₂ must be strictly positive on the domain (n > 3).
    for k in range(max(n_min, 4), max(n_min, 4) + 6):
        v = sp.simplify(a.subs(N, k))
        if v.is_number and v <= 0:
            raise ValueError(
                f"REFUSED: level-2 coefficient a = μ₂ = {a} is NOT positive at "
                f"N = {k} (negative control)"
            )

    # T2 = Σ t_i² = QY + (2/pcoef)·(c_non·s1·s2 + α·CYz) + (1/pcoef²)·U,
    #   U = α²·W + (N·c_non² + 4·c_non·α)·s2².
    U = alpha**2 * _W + (N * c_non**2 + 4 * c_non * alpha) * _s2**2
    t2_expr = sp.simplify(
        _QY + 2 * (1 / pcoef) * (c_non * _s1 * _s2 + alpha * _CYz) + (1 / pcoef**2) * U
    )
    # N2 = P − (W − 4s2²/N)/(N−2) − 2s2²/(N(N−1))  (level-2 projection norm).
    n2_expr = sp.simplify(_P - (_W - 4 * _s2**2 / N) / (N - 2) - 2 * _s2**2 / (N * (N - 1)))

    # ---- (5) EXACT self-check of the three-piece assembly over ℚ(N) ----------
    Q2 = _reduced_Q2(f0, f1, f2, f3, f4)
    piece1 = (_A + f1 * _s1 + f2 * _s2) ** 2
    # assemble with T2, N2 replaced by their defining expressions:
    assembled = piece1 + pcoef * (t2_expr - _s1**2 / N) + a * n2_expr
    residual = sp.simplify(sp.expand(Q2 - assembled))
    if residual != 0:
        raise ValueError(
            f"REFUSED: symbolic three-piece assembly self-check failed "
            f"(residual {residual} ≠ 0) — no symbolic-in-n completing-the-square "
            f"congruence for this moment table (negative control)"
        )

    return SymmetricQuadD2Certificate(
        d=2,
        f0=f0, f1=f1, f2=f2, f3=f3, f4=f4,
        pcoef=sp.simplify(pcoef),
        a=a,
        t2_expr=sp.simplify(t2_expr),
        n2_expr=sp.simplify(n2_expr),
        n_min=int(n_min),
    )


def certify_symmetric_quad_d2_point(family, pt, name):
    """Certify one d=2 symmetric-quad instance from ``family.special[1](pt)``.

    ``spec`` is a dict with keys ``f0..f4`` (harmonic moment values as
    expressions in the free symbol ``N``) and optional ``n_min``."""
    spec = family.special[1](pt)
    cert = symmetric_quad_d2_certificate(
        spec["f0"], spec["f1"], spec["f2"], spec["f3"], spec["f4"],
        n_min=int(spec.get("n_min", 4)),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class SymmetricQuadD2Emitter(Emitter):
    """Emit the SYMBOLIC-IN-n level-2 moment-matrix PSD theorem

        theorem <name> (N : ℝ) (hN : n_min ≤ N)
            (A s1 s2 QY P W CYz T2 N2 : ℝ)
            (hT2 : T2 = <t2_expr>)          -- defining identity of Σ t_i²
            (hN2def : N2 = <n2_expr>)       -- defining identity of the level-2 norm
            (hCSt : s1^2 ≤ N * T2)          -- centered Cauchy–Schwarz on the t-vector
            (hN2 : 0 ≤ N2) :                -- level-2 J(n,2) eigenspace positivity
            0 ≤ Q2(A,s1,s2,QY,P,W,CYz)

    via the exact three-piece completing-the-square + centered-CS congruence
    (``D2_CERTIFICATE.md``): a rational identity closed by ``field_simp``/``ring``
    + ``sq_nonneg`` + ``mul_nonneg`` on the two supplied nonnegativity facts,
    assembled by ``linarith``.  ONE certificate, ALL N ≥ n_min.

    This is the ``d = 2`` sibling of ``SymmetricQuadFormEmitter`` (``d = 1``),
    at the same altitude: the completing-the-square ASSEMBLY is proved
    symbolically in n; the two level ≥ 1 nonnegativity facts (centered CS and the
    level-2 projection positivity ``N2 ≥ 0``) are supplied as hypotheses exactly
    as ``d = 1`` supplies its Cauchy–Schwarz fact ``X² ≤ N·Q``."""

    def __post_init__(self):
        self.kind = "symmetric_quad_d2"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: SymmetricQuadD2Certificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            f0 = _lean_ratfun(cert.f0)
            f1 = _lean_ratfun(cert.f1)
            f2 = _lean_ratfun(cert.f2)
            f3 = _lean_ratfun(cert.f3)
            f4 = _lean_ratfun(cert.f4)
            pcoef = _lean_ratfun(cert.pcoef)
            a = _lean_ratfun(cert.a)
            nmin = cert.n_min

            t2_lean = _lean_ratfun(cert.t2_expr)
            n2_lean = _lean_ratfun(cert.n2_expr)

            # collect distinct irreducible denominator atoms across every rational
            # coefficient appearing in the form / assembly, each proved ≠ 0.
            dens: list[sp.Expr] = []
            for e in (cert.f2, cert.f3, cert.f4, cert.pcoef, cert.a,
                      cert.t2_expr, cert.n2_expr):
                _, dd = sp.fraction(sp.together(sp.nsimplify(e)))
                for fac, _m in sp.factor_list(sp.expand(dd))[1]:
                    fac = sp.expand(fac)
                    if fac.free_symbols and fac not in dens:
                        dens.append(fac)
            den_lines = []
            den_ne_terms = []
            for k, dd in enumerate(dens):
                dstr = sp.sstr(dd).replace("**", "^")
                tac = ("linarith" if sp.Poly(dd, _N).degree() <= 1
                       else "nlinarith [sq_nonneg N, hN]")
                den_lines.append(f"  have hden{k} : (0:ℝ) < ({dstr} : ℝ) := by {tac}\n")
                den_ne_terms.append(f"ne_of_gt hden{k}")
            fs_args = (" [" + ", ".join(den_ne_terms) + "]") if den_ne_terms else ""

            # the reduced form Q2 in Lean.
            Q2 = (
                f"{f0} * A^2 + 2 * {f1} * A * s1 + 2 * {f2} * A * s2 "
                f"+ {f1} * QY + {f2} * (s1^2 - QY) "
                f"+ 2 * {f3} * s1 * s2 + 2 * ({f2} - {f3}) * CYz "
                f"+ {f2} * P + {f3} * (W - 2 * P) + {f4} * (s2^2 - W + P)"
            )
            piece1 = f"(A + {f1} * s1 + {f2} * s2)^2"
            piece2 = f"{pcoef} * (T2 - s1^2 / N)"
            piece3 = f"{a} * N2"

            # positivity of pcoef and a (for mul_nonneg on the remainders): both
            # numerator ≥ 0 and denominator > 0 on the domain N ≥ n_min.
            def _pos_pieces(expr):
                num, den = sp.fraction(sp.together(sp.nsimplify(expr)))
                num = sp.expand(num)
                den_exp = sp.expand(den)
                nstr = sp.sstr(num).replace("**", "^")
                # denominator string FACTORED, to match _lean_ratfun's rendering
                # (so hpden/haden are about the exact term appearing in the coeff).
                dstr = sp.sstr(sp.factor(den)).replace("**", "^")
                ntac = ("positivity" if not num.free_symbols
                        else ("linarith" if sp.Poly(num, _N).degree() <= 1
                              else "nlinarith [sq_nonneg N, hN]"))
                # positivity of a factored denominator: a product of positive
                # linear factors — positivity closes it from the hden* facts in
                # context; fall back to nlinarith otherwise.
                dtac = ("linarith" if (not den_exp.free_symbols
                                       or sp.Poly(den_exp, _N).degree() <= 1)
                        else "positivity")
                return nstr, ntac, dstr, dtac

            pnum_str, pnum_tac, pden_str, pden_tac = _pos_pieces(cert.pcoef)
            anum_str, anum_tac, aden_str, aden_tac = _pos_pieces(cert.a)

            lines.append(
                f"-- SYMBOLIC-IN-n level-2 moment-matrix PSD (the d=2 subset form).\n"
                f"-- Q2 = (A + f1·s1 + f2·s2)²  +  pcoef·(T2 − s1²/N)  +  a·N2,\n"
                f"--   pcoef = N/(4(N−1)) ≥ 0,  a = μ₂ = N(N−2)/(16(N−3)(N−1)) > 0 (N>3).\n"
                f"-- T2 = Σtᵢ² (centered CS: s1² ≤ N·T2); N2 = level-2 J(N,2) norm ≥ 0.\n"
                f"-- ONE certificate, ALL N ≥ {nmin}.  See D2_CERTIFICATE.md.\n"
                f"theorem {name} (N : ℝ) (hN : ({nmin} : ℝ) ≤ N)\n"
                f"    (A s1 s2 QY P W CYz T2 N2 : ℝ)\n"
                f"    (hT2 : T2 = {t2_lean})\n"
                f"    (hN2def : N2 = {n2_lean})\n"
                f"    (hCSt : s1^2 ≤ N * T2)\n"
                f"    (hN2 : (0:ℝ) ≤ N2) :\n"
                f"    (0:ℝ) ≤ {Q2} := by\n"
                f"  have hNpos : (0:ℝ) < N := by linarith\n"
                + "".join(den_lines)
                + f"  -- the exact three-piece completing-the-square congruence (in N):\n"
                f"  have hid : {Q2}\n"
                f"      = {piece1} + {piece2} + {piece3} := by\n"
                f"    subst hT2; subst hN2def\n"
                f"    field_simp{fs_args}\n"
                f"    ring\n"
                f"  -- piece 1: a square.\n"
                f"  have h1 : (0:ℝ) ≤ {piece1} := by positivity\n"
                f"  -- piece 2: pcoef ≥ 0 times the centered CS remainder T2 − s1²/N ≥ 0.\n"
                f"  have hpden : (0:ℝ) < ({pden_str} : ℝ) := by {pden_tac}\n"
                f"  have hpnum : (0:ℝ) ≤ ({pnum_str} : ℝ) := by {pnum_tac}\n"
                f"  have hpcoef : (0:ℝ) ≤ {pcoef} := div_nonneg hpnum (le_of_lt hpden)\n"
                f"  have hrem : (0:ℝ) ≤ T2 - s1^2 / N := by\n"
                f"    have hsq : s1^2 / N ≤ T2 := by\n"
                f"      rw [div_le_iff₀ hNpos]\n"
                f"      linarith [hCSt]\n"
                f"    linarith\n"
                f"  have h2 : (0:ℝ) ≤ {piece2} := mul_nonneg hpcoef hrem\n"
                f"  -- piece 3: a = μ₂ > 0 times the level-2 positivity N2 ≥ 0.\n"
                f"  have haden : (0:ℝ) < ({aden_str} : ℝ) := by {aden_tac}\n"
                f"  have hanum : (0:ℝ) ≤ ({anum_str} : ℝ) := by {anum_tac}\n"
                f"  have ha : (0:ℝ) ≤ {a} := div_nonneg hanum (le_of_lt haden)\n"
                f"  have h3 : (0:ℝ) ≤ {piece3} := mul_nonneg ha hN2\n"
                f"  rw [hid]; linarith\n"
            )
            nthm += 1
        return "".join(lines), nthm


def symmetric_quad_d2_family(name, grid, lean_name, spec, constants=None):
    """Build a symbolic-in-n level-2 moment-matrix PSD family
    (kind='symmetric_quad_d2').

    ``spec``: a callable ``pt -> {"f0":…, …, "f4":…, "n_min": int}`` giving the
    harmonic moment values ``f(N,0..4)`` as exact expressions in the free
    positive symbol ``N``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("symmetric_quad_d2", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    N = _N

    print("=== positive: knapsack harmonic moments f(N,0..4) ===")
    cert = symmetric_quad_d2_certificate(
        _knapsack_f(0), _knapsack_f(1), _knapsack_f(2), _knapsack_f(3), _knapsack_f(4),
        n_min=4,
    )
    print(f"  cert OK: d={cert.d}")
    print(f"    f1={cert.f1}, f2={cert.f2}, f3={cert.f3}, f4={cert.f4}")
    print(f"    pcoef={cert.pcoef}, a=μ₂={cert.a}, n_min={cert.n_min}")
    print(f"    T2 = {cert.t2_expr}")
    print(f"    N2 = {cert.n2_expr}")

    print("\n=== NEGATIVE CONTROL: wrong f3 breaks the assembly (expect ValueError) ===")
    try:
        symmetric_quad_d2_certificate(
            _knapsack_f(0), _knapsack_f(1), _knapsack_f(2),
            _knapsack_f(3) + sp.Rational(1, 7), _knapsack_f(4), n_min=4,
        )
        raise SystemExit("FAIL: broken assembly was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:80]}...")

    print("\n=== NEGATIVE CONTROL: non-positive pivot f0 = -1 (expect ValueError) ===")
    try:
        symmetric_quad_d2_certificate(
            sp.Integer(-1), _knapsack_f(1), _knapsack_f(2), _knapsack_f(3), _knapsack_f(4),
            n_min=4,
        )
        raise SystemExit("FAIL: negative pivot was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:80]}...")

    print("\n=== emitted Lean (one instance) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="sq_moment_d2_knapsack",
                          corners=(), payload=cert),
    ]

    class _View:
        instances = insts

    body, nthm = SymmetricQuadD2Emitter().emit_body(
        _View(), LeanProfile(namespace=("SymmetricQuadD2",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)
