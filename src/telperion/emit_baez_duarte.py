"""Báez-Duarte emitter — Face 6 (spectral / approximation) of the RH obstruction.

The quantity certified here is the Báez-Duarte / Bagchi distance

    d²_N = inf_c ‖ 1 − Σ_{k=2}^{N} c_k · g_k ‖²_{L²(0,1)},
    g_k(x) = {1/(kx)} − k⁻¹·{1/x}     (Báez-Duarte's f_{1/k}, Bagchi's g_k),

the L²((0,1], dx) distance from the constant 1 to the span of g_2, …, g_N
(g_1 ≡ 0).  The spans are nested, so d²_N is non-increasing in N, and

    RH  ⟺  1 ∈ closed span{g_k : k ≥ 1} in L²(0,1)  ⟺  d²_N → 0.

Sources.  Báez-Duarte, "A strengthening of the Nyman–Beurling criterion for the
Riemann hypothesis", Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. 14 (2003)
5–11 (arXiv:math/0202141), proves RH ⟹ (the span condition).  Bagchi, "On Nyman,
Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann
hypothesis", Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006) 137–146
(arXiv:math/0607733), proves both directions: Theorem 2 in the Hardy space
H²(Ω), Ω = {Re s > 1/2}, for G_l(s) = (l^{−s} − l^{−1})·ζ(s)/s and E(s) = 1/s;
Theorem 7 in L²((0,1]) for exactly the g_l above (the space and norm used
here); Theorem 1 in the weighted ℓ² space with ⟨a,b⟩ = Σ a_n b̄_n/(n(n+1)),
γ_l(n) = {n/l} and target γ = (1,1,…), unitarily equivalent to Theorem 7.

Per-N certificate.  On x ∈ (1/(n+1), 1/n] each g_k is the constant {n/k}
(Bagchi eq. (5)), so the residual 1 − Σ c_k g_k is the constant
h_n = 1 − Σ_k c_k·{n/k} there, and for an EXPLICIT rational c

    Q(c) = ‖1 − Σ c_k g_k‖² = Σ_{n≥1} h_n² / (n(n+1))           (exact),

with d²_N ≤ Q(c) because d²_N is an infimum.  The integral over [δ, 1], δ = 1/Y,
is the finite sum n < Y: every term is an exact rational (the 1/x and ln x parts
of the piecewise antiderivative cancel identically for this family, so no
transcendental value enters), and each term is rounded UP to the 2^−prec_bits
grid.  The tail [0, δ] is bounded with its integrand weight: h_n depends only on
n mod L (L = lcm(2..N)), Y = M·L, and for n = jL + r ≥ jL, 1/(n(n+1)) ≤ 1/(jL)²,
so

    Σ_{n≥Y} h_n²/(n(n+1)) ≤ S/L² · Σ_{j≥M} 1/j² ≤ 2S / (L²(2M − 1)),
    S = Σ_{r=0}^{L−1} h_r²  (exact rational; 1/j² < 1/(j−½) − 1/(j+½)).

The tail bound is also rounded UP to the 2^−prec_bits grid.  The sum is a
rigorous dyadic rational ``Uexact ≥ Q(c) ≥ d²_N``; only this upper bound is
certified.  With Y ≈ 2·10⁵ and the coefficients from the exact Gram (digamma
closed form, ``optimal_coeffs``), ``Uexact`` is COMPUTED (mpmath, not
certified) to be within ~10⁻⁹ of the true d²_N.  At N = 2 the gap is certified
two-sided: d²_2 = 1 − ln 2 exactly and 0 ≤ U_2 − (1 − ln 2) ≈ 6.25·10⁻¹².

HONESTY SEAM (Arb-trust class, like winding_box / li_positivity): the fact
``d²_N ≤ Uexact`` — the inf-inequality plus the exact-rational evaluation above —
is the EXTERNAL numeric input, carried as the emitted theorem's hypothesis
``hval : dN2 ≤ Uexact``.  The kernel proves only the trivial rounding
``Uexact ≤ U`` (norm_num) and chains ``dN2 ≤ Uexact ≤ U``.  Certifying one N is
NOT progress toward RH: unconditionally liminf (log N)·d²_N > 0 (Burnol 2002),
so no finite rung can approach the limit.  conjecture1_proved = False.

EARLIER VERSIONS (main before the family fix, 2026-10-14) used the family
{1/(kx)}, k ≥ 2, WITHOUT the −k⁻¹{1/x} term.  That is NOT an RH criterion: on
(1/2, 1) every element of its span is C/x, so its d²_N ≥ 1/2 − (ln 2)² ≈ 0.019547
for every N, unconditionally (RH ⟹ d²_N → 0 is false for it).  The old bounds
(0.516, 0.377, 0.313, 0.270, 0.270, 0.289 for N = 2..7) were valid upper bounds
on THAT quantity, loose and not monotone.  No kernel theorem was false (each
rung is abstract in dN2), but the old rungs are not rungs of Face 6.

NEGATIVE CONTROL: a claimed upper bound ``U`` BELOW the certified ``Uexact`` (so
the bound is not actually established), or a degenerate N < 2 / empty
coefficient vector, is REFUSED at certification with a ``ValueError``.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
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

# default head cut-off: δ = 1/Y with Y ≥ this (rounded UP to a multiple of L)
DEFAULT_Y = 200_000


def _lcm(ks) -> int:
    L = 1
    for k in ks:
        L = L * k // math.gcd(L, k)
    return L


def _residuals(coeffs: dict[int, Fraction]) -> tuple[list[int], int, int]:
    """Integer residual numerators over one period: h_r = H[r]/D for r = 0..L−1,
    where h_n = 1 − Σ_k c_k·{n/k} depends only on n mod L.  Returns (H, D, L)."""
    ks = sorted(coeffs)
    L = _lcm(ks)
    D = _lcm(coeffs[k].denominator * k for k in ks)
    mult = {k: coeffs[k].numerator * (D // (coeffs[k].denominator * k)) for k in ks}
    H = [D - sum(mult[k] * (r % k) for k in ks) for r in range(L)]
    return H, D, L


def baez_duarte_upper_bound(coeffs: dict[int, Fraction], delta: Fraction | None = None,
                            prec_bits: int = 128) -> tuple[Fraction, int]:
    """A RIGOROUS rational upper bound on d²_N ≤ Q(c) for the explicit coefficient
    vector ``coeffs`` (a dict k -> c_k, k ≥ 2) of the Bagchi family g_k.  Returns
    ``(Uexact, N)`` where N is max(k) and d²_N ≤ Q(c) ≤ Uexact rigorously.

    ``delta``: the head/tail cut δ = 1/Y; Y is rounded UP to a multiple of
    L = lcm(k), so the effective δ is ≤ the requested one (default Y ≥ 2·10⁵).
    ``prec_bits``: each head term is rounded UP to a multiple of 2^−prec_bits."""
    ks = sorted(coeffs)
    if not ks or min(ks) < 2:
        raise ValueError("baez_duarte needs coefficients indexed by k ≥ 2")
    N = max(ks)
    H, D, L = _residuals(coeffs)
    Ywant = DEFAULT_Y if delta is None else math.ceil(1 / Fraction(delta))
    M = max(1, -(-Ywant // L))
    Y = M * L
    # head n = 1..Y−1, i.e. ∫ over [1/Y, 1]: Σ ceil(2^p·h_n²/(n(n+1))) / 2^p
    scale = 1 << prec_bits
    D2 = D * D
    head = 0
    for n in range(1, Y):
        h = H[n % L]
        head += -((-h * h * scale) // (D2 * n * (n + 1)))
    # tail n ≥ Y = M·L, i.e. ∫ over [0, 1/Y]: ≤ 2S/(L²(2M − 1)), S = Σ_period h_r²
    S = Fraction(sum(h * h for h in H), D2)
    tail = 2 * S / (L * L * (2 * M - 1))
    # round the tail UP onto the same grid, so Uexact is one short dyadic rational
    tail_up = -((-tail.numerator * scale) // tail.denominator)
    return (Fraction(head + tail_up, scale), N)


@dataclass(frozen=True)
class BaezDuarteCert:
    """The N-th Báez-Duarte rung: a rigorous rational upper bound ``U`` on d²_N,
    established by the coefficient vector ``coeffs`` (whose form value Q encloses to
    ``Uexact ≤ U``)."""

    N: int
    coeffs: tuple           # ((k, c_k), …)
    Uexact: Fraction        # certified upper bound on Q(c) ≥ d²_N
    U: Fraction             # readable rational bound emitted, Uexact ≤ U


def baez_duarte_certificate(coeffs, U=None, delta=None, prec_bits: int = 128) -> BaezDuarteCert:
    """Build (and exactly re-check) a Báez-Duarte rung certificate.

    ``coeffs``: dict k -> c_k (k ≥ 2).  ``U``: the readable rational bound to emit;
    defaults to ``Uexact``.  Refuses (``ValueError``): fewer than one coefficient /
    k < 2 (degenerate), or a supplied ``U`` BELOW the certified ``Uexact`` (the
    negative control — such a U is NOT actually established by the enclosure)."""
    coeffs = {int(k): (Fraction(sp.nsimplify(v)) if not isinstance(v, Fraction) else v)
              for k, v in dict(coeffs).items()}
    Uexact, N = baez_duarte_upper_bound(coeffs, delta=delta, prec_bits=prec_bits)
    if U is None:
        U = Uexact
    U = Fraction(sp.nsimplify(U)) if not isinstance(U, Fraction) else U
    if U < Uexact:
        raise ValueError(
            f"baez_duarte REFUSED: emitted bound U = {U} is below the certified "
            f"enclosure upper endpoint Uexact = {Uexact}; U is not established")
    return BaezDuarteCert(
        N=N, coeffs=tuple(sorted(coeffs.items())), Uexact=Uexact, U=U)


def certify_baez_duarte_point(family, pt, name):
    """Certify one Báez-Duarte rung.  Reads ``spec = family.special[1](pt)`` — a
    dict ``{"coeffs":{k:c_k}, "U":…}`` (U optional)."""
    spec = family.special[1](pt)
    cert = baez_duarte_certificate(spec["coeffs"], spec.get("U"), spec.get("delta"))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BaezDuarteEmitter(Emitter):
    """Emit the N-th Báez-Duarte rung ``dN2 ≤ U`` (with ``dN2`` the L²(0,1)
    infimum over the Bagchi family g_k carried abstractly, hypothesis
    ``hval : dN2 ≤ Uexact`` the certified form value ≥ d²_N) from an explicit
    coefficient vector.  Deterministic ``le_trans hval (by norm_num)``."""

    def __post_init__(self):
        self.kind = "baez_duarte"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BaezDuarteCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            Ue = rat_lean(cert.Uexact)
            U = rat_lean(cert.U)
            cvec = ", ".join(f"c_{k}={c}" for k, c in cert.coeffs)
            lines.append(
                f"-- {nm}: Báez-Duarte rung N={cert.N} — d²_N ≤ {cert.U}.\n"
                f"-- d²_N = inf_c ‖1 − Σ_{{k=2}}^N c_k·g_k‖²_{{L²(0,1)}}, g_k(x) = {{1/(kx)}} − {{1/x}}/k\n"
                f"-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).\n"
                f"-- Witnessing coefficient vector: {cvec}.  Its form value\n"
                f"-- Q(c) = Σ_n (1 − Σ c_k{{n/k}})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact\n"
                f"-- (the trust seam, hypothesis hval).\n"
                f"-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.\n"
                f"theorem {nm} (dN2 : ℝ) (hval : dN2 ≤ ({Ue} : ℝ)) : dN2 ≤ ({U} : ℝ) :=\n"
                f"  le_trans hval (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def baez_duarte_refutation_atom_lean() -> str:
    """The Báez-Duarte falsifiability face, emitted ONCE per generated file.

    The kernel statement is generic in P, dN2, L, eps.  It may be instantiated
    with dN2 = the Bagchi-family d²_N of this file, for which RH ⟹ d²_N → 0 is a
    theorem (Báez-Duarte 2003; Bagchi 2006, Thm 2 / Thm 7) — but hRH at one fixed N needs
    N beyond an inexplicit N₀(eps), so hRH stays an external hypothesis.  It must
    NOT be instantiated with the pre-fix family {1/(kx)} (no −k⁻¹{1/x} term):
    there d²_N ≥ 1/2 − (ln 2)² for every N, so hRH is false for eps ≤ 0.01954 and
    the face would fire spuriously.  Term-mode; not expected to fire.
    conjecture1_proved = False."""
    return (
        "-- bd_neg_refutes: the falsifiability face.  Generic in P, dN2, L, eps: a\n"
        "-- certified LOWER bound L ≤ dN2 with eps ≤ L contradicts hRH : P → dN2 < eps.\n"
        "-- Intended instance: P = RH and dN2 = the Báez-Duarte / Bagchi d²_N of THIS\n"
        "-- file (g_k = {1/(kx)} − {1/x}/k, k ≥ 2, in L²(0,1)), where RH ⟹ d²_N → 0 is\n"
        "-- a theorem (Báez-Duarte 2003; Bagchi 2006, Thm 2 / Thm 7); hRH at fixed N needs N\n"
        "-- past an inexplicit N₀(eps), so it is an external hypothesis.  Do NOT use the\n"
        "-- pre-2026-10-14 family {1/(kx)} without the −{1/x}/k term: its d²_N is\n"
        "-- ≥ 1/2 − (ln 2)² ≈ 0.019547 for every N, so hRH is false for eps ≤ 0.01954.\n"
        "-- Not expected to fire; makes the sequence falsifiable.\n"
        "theorem bd_neg_refutes {P : Prop} (dN2 L eps : ℝ)\n"
        "    (hRH : P → dN2 < eps) (hLo : L ≤ dN2) (hbad : eps ≤ L) : ¬P :=\n"
        "  fun hP => absurd (hRH hP) (not_lt.mpr (le_trans hbad hLo))\n"
    )


def baez_duarte_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Báez-Duarte family (kind ``baez_duarte``).
    ``spec``: ``pt -> {"coeffs": {k: c_k}, "U": …}`` (U optional)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("baez_duarte", spec),
        constants=dict(constants or {}),
    )


def exact_gram(N: int, dps: int = 50):
    """The exact Gram data of g_2..g_N in L²(0,1), as mpmath values at ``dps``
    digits: ``(ks, A, b)`` with A_jk = ⟨g_j, g_k⟩ = Σ_n {n/j}{n/k}/(n(n+1)) and
    b_k = ⟨1, g_k⟩ = Σ_n {n/k}/(n(n+1)) (and ‖1‖² = 1).  The summands are
    L-periodic in n, and Σ_{j≥0} 1/((r+jL)(r+jL+1)) = (ψ((r+1)/L) − ψ(r/L))/L."""
    import mpmath as mp

    with mp.workdps(dps):
        ks = list(range(2, N + 1))
        L = _lcm(ks)
        w = [None] + [(mp.digamma(mp.mpf(r + 1) / L) - mp.digamma(mp.mpf(r) / L)) / L
                      for r in range(1, L + 1)]
        fr = {k: [mp.mpf(r % k) / k for r in range(L + 1)] for k in ks}
        A = mp.matrix([[mp.fsum(fr[j][r] * fr[k][r] * w[r] for r in range(1, L + 1))
                        for k in ks] for j in ks])
        b = mp.matrix([mp.fsum(fr[k][r] * w[r] for r in range(1, L + 1)) for k in ks])
        return ks, A, b


def form_value(coeffs: dict[int, Fraction], dps: int = 50):
    """Q(c) = Σ_n h_n²/(n(n+1)) in closed form (digamma; mpmath, ``dps`` digits) —
    a numerical cross-check of ``baez_duarte_upper_bound``, NOT part of the rigour."""
    import mpmath as mp

    H, D, L = _residuals(coeffs)
    with mp.workdps(dps):
        return mp.fsum(mp.mpf(H[r % L] ** 2) / D ** 2
                       * (mp.digamma(mp.mpf(r + 1) / L) - mp.digamma(mp.mpf(r) / L)) / L
                       for r in range(1, L + 1))


def optimal_coeffs(N: int, prec_bits: int = 128) -> dict[int, Fraction]:
    """A near-optimal rational coefficient vector for the N-th rung: the solution of
    the normal equations A c = b on the EXACT Gram (``exact_gram``), rationalized
    with denominators ≤ 10⁸.  Its optimality is only a heuristic for a tight bound;
    the certificate's rigour comes from ``baez_duarte_upper_bound``, not from c
    being the true minimizer.  (``prec_bits`` is accepted for API compatibility.)"""
    import mpmath as mp

    ks, A, b = exact_gram(N)
    with mp.workdps(50):
        c = mp.lu_solve(A, b)
        return {k: Fraction(mp.nstr(c[i], 25)).limit_denominator(10**8)
                for i, k in enumerate(ks)}


if __name__ == "__main__":
    from fractions import Fraction as F

    print("=== positive cert N=4 (optimal-ish coeffs) ===")
    cs = optimal_coeffs(4)
    print("coeffs:", {k: str(v) for k, v in cs.items()})
    cert = baez_duarte_certificate(cs)
    print(f"cert OK: N={cert.N} Uexact≈{float(cert.Uexact):.9f}")

    print("\n=== certified upper bounds (non-increasing, as nested spans force) ===")
    for N in (2, 3, 4, 5, 6, 7):
        c = optimal_coeffs(N)
        ct = baez_duarte_certificate(c)
        print(f"N={N}: d²_N ≤ {float(ct.Uexact):.9f}")

    print("\n=== NEGATIVE CONTROL: U below the certified Uexact must raise ===")
    try:
        baez_duarte_certificate(cs, U=F(1, 1000))
        raise SystemExit("FAIL: too-small U not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL 2: degenerate (k<2) must raise ===")
    try:
        baez_duarte_certificate({1: F(1, 2)})
        raise SystemExit("FAIL: k<2 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean (N=4) ===")
    fam = baez_duarte_family(
        "T", GridSpec([("case", [0])]), lambda pt: "bd_N4",
        spec=lambda pt: {"coeffs": cs, "U": None},
    )
    inst, _ = certify_baez_duarte_point(fam, {"case": 0}, "bd_N4")

    class _V:
        instances = [inst]

    body, nthm = BaezDuarteEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
    print(baez_duarte_refutation_atom_lean())
