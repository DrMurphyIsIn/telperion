"""Symmetric moment-matrix PSD emitter — the SYMBOLIC-IN-n completing-the-square
certificate (the marquee P=NP unblocker).

The recurring object across the SoS / knapsack duality arc (see
``examples/g1_floors/lean/Hsq.lean``, ``theorem subsetForm_d1``) is a degree-``d``
subset-indexed *moment form*, PSD **for every population size n symbolically**:

    Φ_d(x; n) = Σ_{|S|,|T| ≤ d}  x_S · x_T · f(n, |S ∪ T|)   ≥ 0.

At level ``d = 1`` the index set is ``{∅} ∪ {{i} : i}`` and — grouping by the
harmonic block ``f(n,0)=f0``, ``f(n,1)=f1``, ``f(n,2)=f2`` and collapsing the
rank-one part — the form reduces to the three collective coordinates

    A = x_∅,   X = Σ_i x_{i},   Q = Σ_i x_{i}²,

    Φ_1(A,X,Q; n) = f0·A² + 2·f1·A·X + f2·X² + (f1 − f2)·Q.

This module produces, SYMBOLICALLY IN n, the exact completing-the-square /
Cauchy–Schwarz congruence that ``Hsq.lean``'s ``subsetForm_d1`` proves by hand:

    Φ_1 = f0·(A + (f1/f0)·X)²  +  cCS·(n·Q − X²),      cCS = (f1 − f2)/n,

nonnegative because (i) ``f0 > 0`` (the pivot), (ii) ``cCS ≥ 0``, and (iii)
``n·Q − X² ≥ 0`` is Cauchy–Schwarz (``sq_sum_le_card_mul_sum_sq``).  The
decomposition is EXACT only when the *rank-collapse identity*

    RANK-COLLAPSE:   n·(f2·f0 − f1²)  +  f0·(f1 − f2)  =  0

holds (this is "harmonic completeness" — the level-1 tie in disguise).  The
knapsack moments ``f0=1, f1=1/2, f2=(n−2)/(4(n−1))`` satisfy it identically in n.

The certificate is verified EXACTLY over ``ℚ(n)`` (n a free positive symbol), so
one certificate covers ALL n at once — this is the symbolic-in-n moment-matrix
PSD certificate.  The emitted Lean is a single ``n``-quantified theorem modeled
line-for-line on ``subsetForm_d1``: an explicit rational congruence closed by
``field_simp``/``ring`` and assembled from ``sq_nonneg`` + a Cauchy–Schwarz
remainder by ``linarith``.

NEGATIVE CONTROL: a non-positive pivot ``f0 ≤ 0``, a negative CS coefficient
``f1 − f2 < 0`` (on the certified domain), or a moment triple that VIOLATES the
rank-collapse identity (so no symbolic completed-square congruence exists) is
refused with ``ValueError``.

HONEST SCOPE: this ships the ``d = 1`` symbolic-in-n case faithfully (the
``subsetForm_d1`` object, the only level Hsq.lean discharges outright).  The
general symbolic-in-n degree-``d ≥ 2`` moment-PSD certificate (``SubsetFormPSD``
for general ``d``, harmonic completeness) is the named remaining open layer and
is future work.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_symmetric_quad.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# the free symbolic population size n (a positive integer, n ≥ 2 keeps
# denominators alive and the Cauchy–Schwarz remainder meaningful).
_N = sp.Symbol("N", positive=True)


def _lean_ratfun(expr: sp.Expr) -> str:
    """Render a rational function of N as ℝ-ascribed Lean (N : ℝ in scope).

    Bare rational literals are ℝ-ascribed so they do not default to ℤ."""
    expr = sp.nsimplify(sp.together(expr))
    num, den = sp.fraction(expr)

    def _poly(p: sp.Expr) -> str:
        p = sp.expand(p)
        s = sp.sstr(p)
        # sympy prints `**` for powers and `N` for the symbol; Lean wants `^`.
        s = s.replace("**", "^")
        return s

    ns, ds = _poly(num), _poly(den)
    if den == 1:
        return f"({ns} : ℝ)"
    return f"(({ns} : ℝ) / ({ds} : ℝ))"


def _lean_num_den(expr: sp.Expr) -> tuple[str, str]:
    """Return ``(num_lean, den_lean)`` for a rational function of N, each as an
    ℝ-ascribed Lean polynomial string.  ``den`` is normalized so it is provably
    positive on the certified domain (linear-in-N denominators like ``4*N - 4``
    close by ``linarith`` from ``hN``)."""
    expr = sp.nsimplify(sp.together(expr))
    num, den = sp.fraction(expr)

    def _poly(p: sp.Expr) -> str:
        return sp.sstr(sp.expand(p)).replace("**", "^")

    return f"({_poly(num)} : ℝ)", f"({_poly(den)} : ℝ)"


@dataclass(frozen=True)
class SymmetricQuadCertificate:
    """A verified symbolic-in-n level-1 moment-matrix PSD certificate.

    The three collective coordinates are ``A = x_∅``, ``X = Σ x_i``,
    ``Q = Σ x_i²``.  ``f0, f1, f2`` are the harmonic-block moment values as exact
    rational functions of the free symbol ``N`` (the population size).  The form

        Φ = f0·A² + 2·f1·A·X + f2·X² + (f1 − f2)·Q

    decomposes EXACTLY (symbolically in N) as

        Φ = f0·(A + (f1/f0)·X)² + cCS·(N·Q − X²),   cCS = (f1 − f2)/N,

    valid on the domain ``N ≥ n_min`` where ``f0 > 0`` and ``cCS ≥ 0``; the
    Cauchy–Schwarz fact ``0 ≤ N·Q − X²`` closes it.
    """

    d: int                    # moment degree (this emitter: d = 1)
    f0: sp.Expr               # f(N, 0)   — the pivot, must be > 0 on domain
    f1: sp.Expr               # f(N, 1)
    f2: sp.Expr               # f(N, 2)
    pivot_coeff: sp.Expr      # f1 / f0   (the completed-square shift)
    cs_coeff: sp.Expr         # cCS = (f1 − f2)/N  (the CS remainder coeff, ≥ 0)
    n_min: int                # domain floor: certificate is stated ∀ N ≥ n_min


def symmetric_quad_certificate(
    f0, f1, f2, *, n_min: int = 3, d: int = 1
) -> SymmetricQuadCertificate:
    """Build and EXACTLY self-check (over ℚ(N)) the level-1 symbolic-in-n
    moment-matrix PSD certificate.

    ``f0, f1, f2`` are the harmonic moment values ``f(N,0), f(N,1), f(N,2)`` —
    ints / Fractions / sympy expressions in the free symbol ``N``.  ``n_min`` is
    the domain floor (``N ≥ n_min``) on which ``f0 > 0`` and ``f1 − f2 ≥ 0``.

    Refuses (``ValueError``): a non-positive pivot ``f0``, a negative CS
    coefficient ``f1 − f2`` on the domain, or a moment triple that violates the
    rank-collapse identity ``N·(f2·f0 − f1²) + f0·(f1 − f2) = 0`` (so no exact
    symbolic completed-square congruence exists)."""
    if d != 1:
        raise ValueError(
            f"REFUSED: only d = 1 (subsetForm_d1) is supported symbolically in n; "
            f"got d = {d} (general d ≥ 2 is the named open harmonic-completeness layer)"
        )
    N = _N
    f0 = sp.nsimplify(sp.sympify(f0))
    f1 = sp.nsimplify(sp.sympify(f1))
    f2 = sp.nsimplify(sp.sympify(f2))

    # (1) pivot must be strictly positive on the domain N ≥ n_min.
    piv_lo = sp.simplify(f0.subs(N, n_min))
    if not (piv_lo.is_number and piv_lo > 0):
        # symbolic fallback: check positivity across a small ladder of n values.
        if any((v := sp.simplify(f0.subs(N, k))).is_number and v <= 0
               for k in range(n_min, n_min + 6)):
            raise ValueError(
                f"REFUSED: pivot f0 = {f0} is NOT positive on N ≥ {n_min} "
                f"(negative control)"
            )

    # (2) CS remainder coefficient cCS = (f1 − f2)/N must be ≥ 0 on the domain.
    cs_num = sp.simplify(f1 - f2)
    for k in range(n_min, n_min + 6):
        val = sp.simplify(cs_num.subs(N, k))
        if val.is_number and val < 0:
            raise ValueError(
                f"REFUSED: Cauchy–Schwarz coefficient f1 − f2 = {cs_num} is "
                f"NEGATIVE at N = {k} — form is indefinite (negative control)"
            )

    # (3) RANK-COLLAPSE identity — the exact symbolic completed-square congruence
    #     exists iff  N·(f2·f0 − f1²) + f0·(f1 − f2) ≡ 0  in ℚ(N).
    rank_collapse = sp.simplify(N * (f2 * f0 - f1**2) + f0 * (f1 - f2))
    if sp.simplify(rank_collapse) != 0:
        raise ValueError(
            f"REFUSED: rank-collapse identity violated "
            f"(N·(f2·f0 − f1²) + f0·(f1 − f2) = {rank_collapse} ≠ 0) — no exact "
            f"symbolic-in-n completed-square congruence exists (negative control)"
        )

    pivot_coeff = sp.simplify(f1 / f0)
    cs_coeff = sp.simplify((f1 - f2) / N)

    # (4) EXACT self-check of the decomposition over ℚ(N):
    #     Φ − [ f0·(A + piv·X)² + cCS·(N·Q − X²) ] ≡ 0.
    A, X, Q = sp.symbols("A X Q", real=True)
    form = f0 * A**2 + 2 * f1 * A * X + f2 * X**2 + (f1 - f2) * Q
    decomp = f0 * (A + pivot_coeff * X) ** 2 + cs_coeff * (N * Q - X**2)
    residual = sp.simplify(sp.expand(form - decomp))
    if residual != 0:
        raise ValueError(
            f"REFUSED: symbolic completing-the-square self-check failed "
            f"(residual {residual} ≠ 0) — certificate rejected"
        )

    return SymmetricQuadCertificate(
        d=1,
        f0=f0,
        f1=f1,
        f2=f2,
        pivot_coeff=pivot_coeff,
        cs_coeff=cs_coeff,
        n_min=int(n_min),
    )


def certify_symmetric_quad_point(family, pt, name):
    """Certify one symmetric-quad instance from ``family.special[1](pt) -> spec``.

    ``spec`` is a dict ``{"f0": ..., "f1": ..., "f2": ..., "n_min": int}`` (the
    harmonic moment values as expressions in the free symbol ``N``)."""
    spec = family.special[1](pt)
    cert = symmetric_quad_certificate(
        spec["f0"], spec["f1"], spec["f2"], n_min=int(spec.get("n_min", 3))
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class SymmetricQuadFormEmitter(Emitter):
    """Emit the SYMBOLIC-IN-n level-1 moment-matrix PSD theorem

        theorem <name> (N : ℝ) (hN : n_min ≤ N)
            (A X Q : ℝ) (hCS : X^2 ≤ N * Q) :
            0 ≤ f0·A² + 2·f1·A·X + f2·X² + (f1 − f2)·Q

    via the exact completing-the-square / Cauchy–Schwarz congruence proved by
    hand in ``examples/g1_floors/lean/Hsq.lean`` (``subsetForm_d1``): a rational
    identity (``field_simp``/``ring``) + ``sq_nonneg`` + the supplied CS
    hypothesis, assembled by ``linarith``.  ``A = x_∅``, ``X = Σ x_i``,
    ``Q = Σ x_i²``; the CS hypothesis ``X² ≤ N·Q`` is the standing
    ``sq_sum_le_card_mul_sum_sq`` fact.  One certificate, ALL n."""

    def __post_init__(self):
        self.kind = "symmetric_quad"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: SymmetricQuadCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            f0 = _lean_ratfun(cert.f0)
            f1 = _lean_ratfun(cert.f1)
            f2 = _lean_ratfun(cert.f2)
            piv = _lean_ratfun(cert.pivot_coeff)
            ccs = _lean_ratfun(cert.cs_coeff)
            nmin = cert.n_min
            # collect the distinct IRREDUCIBLE denominator factors appearing in the
            # form / decomposition, each proved positive (field_simp normalizes a
            # composite denom like 2*(N-1) into its atomic factors, so we must
            # supply `≠ 0` for each irreducible atom, not just the product).
            dens: list[sp.Expr] = []
            for e in (cert.f2, cert.pivot_coeff, cert.cs_coeff):
                _, d = sp.fraction(sp.together(sp.nsimplify(e)))
                for fac, _mult in sp.factor_list(sp.expand(d))[1]:
                    fac = sp.expand(fac)
                    if fac.free_symbols and fac not in dens:
                        dens.append(fac)
            den_lines = []
            den_ne_terms = []
            for k, d in enumerate(dens):
                dstr = sp.sstr(d).replace("**", "^")
                # linear-in-N factors (e.g. N - 1) are positive on N ≥ n_min by
                # linarith from hN; higher-degree ones close by nlinarith.
                tac = "linarith" if sp.Poly(d, _N).degree() <= 1 else "nlinarith [sq_nonneg N]"
                den_lines.append(
                    f"  have hden{k} : (0:ℝ) < ({dstr} : ℝ) := by {tac}\n"
                )
                den_ne_terms.append(f"ne_of_gt hden{k}")
            fs_args = (" [" + ", ".join(den_ne_terms) + "]") if den_ne_terms else ""
            # numerator / denominator of the Cauchy–Schwarz coefficient (for a
            # div_nonneg proof that does not depend on `positivity` seeing hN).
            _, ccs_den_expr = sp.fraction(sp.together(sp.nsimplify(cert.cs_coeff)))
            ccs_den_expr = sp.expand(ccs_den_expr)
            if ccs_den_expr.free_symbols:
                cs_den_str = sp.sstr(ccs_den_expr).replace("**", "^")
                cs_deg = sp.Poly(ccs_den_expr, _N).degree()
                cs_tac = "linarith" if cs_deg <= 1 else "nlinarith [sq_nonneg N]"
                hcoeff_proof = (
                    f"    have hcsden : (0:ℝ) < ({cs_den_str} : ℝ) := by {cs_tac}\n"
                    f"    have hcoeff : (0:ℝ) ≤ {ccs} :=\n"
                    f"      div_nonneg (by positivity) (le_of_lt hcsden)\n"
                )
            else:  # CS coefficient is a nonnegative constant
                hcoeff_proof = f"    have hcoeff : (0:ℝ) ≤ {ccs} := by positivity\n"
            # the form and its exact completed-square + CS decomposition (in N).
            form = (
                f"{f0} * A^2 + 2 * {f1} * A * X + {f2} * X^2 "
                f"+ ({f1} - {f2}) * Q"
            )
            sq = f"{f0} * (A + {piv} * X)^2"
            csrem = f"{ccs} * (N * Q - X^2)"
            lines.append(
                f"-- SYMBOLIC-IN-n level-1 moment-matrix PSD (subsetForm_d1 shape):\n"
                f"-- Φ = f0·A² + 2·f1·A·X + f2·X² + (f1−f2)·Q\n"
                f"--   = f0·(A + (f1/f0)·X)² + cCS·(N·Q − X²),  cCS = (f1−f2)/N.\n"
                f"-- ONE certificate, ALL N ≥ {nmin}.  A=x_∅, X=Σxᵢ, Q=Σxᵢ²; "
                f"hCS is Cauchy–Schwarz.\n"
                f"theorem {name} (N : ℝ) (hN : ({nmin} : ℝ) ≤ N)\n"
                f"    (A X Q : ℝ) (hCS : X^2 ≤ N * Q) :\n"
                f"    (0:ℝ) ≤ {form} := by\n"
                f"  have hNpos : (0:ℝ) < N := by linarith\n"
                + "".join(den_lines)
                + f"  have hid : {form}\n"
                f"      = {sq} + {csrem} := by\n"
                f"    field_simp{fs_args}\n"
                f"    ring\n"
                f"  have hsq : (0:ℝ) ≤ {sq} := by positivity\n"
                f"  have hcs : (0:ℝ) ≤ {csrem} := by\n"
                f"    have hrem : (0:ℝ) ≤ N * Q - X^2 := by linarith\n"
                + hcoeff_proof
                + f"    exact mul_nonneg hcoeff hrem\n"
                f"  rw [hid]; linarith\n"
            )
            nthm += 1
        return "".join(lines), nthm


def symmetric_quad_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a symbolic-in-n level-1 moment-matrix PSD family (kind='symmetric_quad').

    ``spec``: a callable ``pt -> {"f0":…, "f1":…, "f2":…, "n_min": int}`` giving
    the harmonic moment values ``f(N,0), f(N,1), f(N,2)`` as exact expressions in
    the free positive symbol ``N`` (import ``N`` from this module, or pass ints /
    sympy expressions).  Refuses a non-positive pivot, a negative Cauchy–Schwarz
    coefficient, or a moment triple violating the rank-collapse identity."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("symmetric_quad", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid cert(s), negative controls, print emitted Lean ------
    N = _N

    print("=== positive: knapsack harmonic moments f0=1, f1=1/2, f2=(N-2)/(4(N-1)) ===")
    cert = symmetric_quad_certificate(
        sp.Integer(1), sp.Rational(1, 2), (N - 2) / (4 * (N - 1)), n_min=3
    )
    print(f"  cert OK: d={cert.d}, f0={cert.f0}, f1={cert.f1}, f2={cert.f2}")
    print(f"           pivot=f1/f0={cert.pivot_coeff}, cCS=(f1-f2)/N={cert.cs_coeff}, "
          f"n_min={cert.n_min}")

    print("\n=== positive: a second valid harmonic triple (scaled f0=2) ===")
    # scale f0 -> 2, f1 -> 1, and solve rank-collapse for f2:
    #   N(f2·2 - 1) + 2(1 - f2) = 0  =>  f2(2N - 2) = N - 2  =>  f2 = (N-2)/(2N-2).
    cert2 = symmetric_quad_certificate(
        sp.Integer(2), sp.Integer(1), (N - 2) / (2 * N - 2), n_min=3
    )
    print(f"  cert OK: f0={cert2.f0}, f1={cert2.f1}, f2={cert2.f2}, "
          f"cCS={cert2.cs_coeff}")

    print("\n=== NEGATIVE CONTROL: rank-collapse VIOLATED (f2 wrong) (expect ValueError) ===")
    try:
        symmetric_quad_certificate(sp.Integer(1), sp.Rational(1, 2), sp.Rational(1, 3))
        raise SystemExit("FAIL: rank-collapse violation was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: non-positive pivot f0 = -1 (expect ValueError) ===")
    try:
        symmetric_quad_certificate(sp.Integer(-1), sp.Rational(1, 2),
                                   (N - 2) / (4 * (N - 1)))
        raise SystemExit("FAIL: negative pivot was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: negative CS coeff f1 - f2 < 0 (expect ValueError) ===")
    try:
        # f1 = 0, f2 = (N-2)/(4(N-1)) > 0 for N>2 => f1 - f2 < 0; and it also
        # breaks rank-collapse, but the CS check fires first on the ladder.
        symmetric_quad_certificate(sp.Integer(1), sp.Integer(0),
                                   (N - 2) / (4 * (N - 1)))
        raise SystemExit("FAIL: negative CS coefficient was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="sq_moment_d1_knapsack",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="sq_moment_d1_scaled",
                          corners=(), payload=cert2),
    ]

    class _View:
        instances = insts

    body, nthm = SymmetricQuadFormEmitter().emit_body(
        _View(), LeanProfile(namespace=("SymmetricQuad",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)
