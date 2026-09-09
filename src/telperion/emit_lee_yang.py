"""LeeYangStablePair emitter — Schur stability of a rational-coefficient
polynomial, the finite-checkable core of the Dyson-quasicrystal / Kurasov–Sarnak
"zeros on a line by construction" analogue.

BACKGROUND (Kurasov–Sarnak, *J. Math. Phys.* 61:083501, 2020, "Stable
polynomials and crystalline measures").  A *stable* pair of polynomials
generates, by a fixed algebraic construction, a Fourier quasicrystal whose
derived Dirichlet series ``F(s) = Σ aᵢ e^{−is·λᵢ}`` has ALL of its zeros on a
single vertical line ``Re s = 0`` — an RH-analogue that holds BY CONSTRUCTION.
The load-bearing, finite-checkable hypothesis of that construction is **Schur
stability** of a concrete univariate polynomial: all of its zeros lie in the
open unit disk (``inside`` orientation), equivalently — via the reciprocal
polynomial ``zⁿ p(1/z)`` — that none lie in the closed unit disk (``outside``
orientation).

For a REAL (here: exact-rational) polynomial ``p(z) = Σ_{i=0}^{n} aᵢ zⁱ`` with
``aₙ ≠ 0``, Schur stability is decidable over the rationals by the SCHUR–COHN
reduction.  Writing the coefficient list ``(a₀ … aₙ)`` ascending, one step is

    bᵢ = aₙ·aᵢ − a₀·a_{n−i}          (i = 1 … n, dropping the identically-zero b₀)

which yields a degree ``(n−1)`` polynomial, together with the *test quantity*

    t = aₙ² − a₀².

The theorem (Schur–Cohn): ``p`` has all zeros in the open unit disk iff the test
quantity is strictly positive at every level of the recursion ``p ↦ (b₁ … bₙ)``.
This module emits that Jury/Schur–Cohn test-quantity chain as a chain of exact
rational strict inequalities discharged by ``norm_num``, with each ``tⱼ`` written
out as the explicit polynomial-in-the-coefficients expression so the kernel
recomputes it from the ``aᵢ`` literals (load-bearing, not pre-collapsed).

VALIDATION.  For every emitted instance the builder recomputes the actual roots
numerically (``sympy`` ``nroots``) and cross-checks the stability verdict; it
REFUSES on any disagreement, on any root modulus within ``1e-9`` of ``1``
(knife-edge), on a non-strict (``≤ 0``) test quantity, on degree ``0`` or
``aₙ = 0`` or non-rational coefficients, and on degree ``> 12`` (test-quantity
expression-size cap).  A false or borderline certificate is never emitted.

HONESTY SEAM.  The kernel verifies ONLY the exact rational Jury-chain positivity
(non-vacuous, recomputed from the coefficient literals).  The Schur–Cohn theorem
(positivity of the chain ⟹ all zeros in the open disk) and the Kurasov–Sarnak
conclusion (stability ⟹ the derived Dirichlet polynomial's zeros lie on
``Re s = 0``) are CITED analytic preludes, not anything the kernel establishes.
This is a category-(b) structural ANALOGUE certificate.  It is NOT a statement
about ζ: Kurasov–Sarnak note the prime explicit formula does not yield a Fourier
quasicrystal, so this line-of-zeros analogue is unrelated to zeta's RH.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# Test-quantity expression-size cap: degree > 12 blows up the written-out
# polynomial-in-coefficients test quantities (each bᵢ is bilinear in the running
# coefficient list, so the level-k tⱼ is a degree-≈2ᵏ polynomial in the aᵢ).
_MAX_DEGREE = 12

# Knife-edge tolerance: refuse if any numeric root modulus is within this of 1.
_BORDERLINE_TOL = sp.Rational(1, 10**9)


@dataclass(frozen=True)
class LeeYangStablePairCert:
    """One certified Schur-stability instance.

    ``coeffs`` — the ascending exact-rational coefficient list ``(a₀ … aₙ)`` of
        the polynomial actually tested (for ``outside`` mode this is the
        reciprocal ``(aₙ … a₀)`` of the user's polynomial — see ``mode``).
    ``orig_coeffs`` — the ascending coefficient list of the user's polynomial
        ``p`` as supplied (equals ``coeffs`` in ``inside`` mode).
    ``mode`` — ``"inside"`` (all zeros of ``p`` in the open unit disk) or
        ``"outside"`` (no zeros of ``p`` in the closed unit disk; tested via the
        reciprocal, whose zeros are the reciprocals of ``p``'s zeros).
    ``tests`` — the exact rational Schur–Cohn test-quantity chain ``(t₁ … t_n)``,
        each ``> 0`` (the certified positivity), where ``t_k = aₙ⁽ᵏ⁾² −
        a₀⁽ᵏ⁾²`` for the running coefficient list at level ``k``.
    ``levels`` — the running ascending coefficient lists ``(c⁽¹⁾ … c⁽ⁿ⁾)`` fed
        into each reduction step (``c⁽¹⁾ = coeffs``); used to write each ``t_k``
        out as an explicit expression in the previous level's endpoints.
    ``root_moduli`` — the numeric ``|root|`` of the USER polynomial ``p`` (for
        the docstring / provenance; the verdict cross-check).
    """

    coeffs: tuple[sp.Rational, ...]
    orig_coeffs: tuple[sp.Rational, ...]
    mode: str
    tests: tuple[sp.Rational, ...]
    levels: tuple[tuple[sp.Rational, ...], ...]
    root_moduli: tuple[sp.Float, ...]


def _schur_step(a: Sequence[sp.Rational]) -> tuple[tuple[sp.Rational, ...], sp.Rational]:
    """One Schur–Cohn reduction of an ascending coefficient list ``(a₀ … aₙ)``.

    Returns ``((b₁ … bₙ), t)`` where ``bᵢ = aₙ·aᵢ − a₀·a_{n−i}`` (the degree-
    ``(n−1)`` reduced list, dropping the identically-zero ``b₀``) and the test
    quantity ``t = aₙ² − a₀²``."""
    n = len(a) - 1
    an = a[n]
    a0 = a[0]
    b = tuple(an * a[i] - a0 * a[n - i] for i in range(1, n + 1))
    t = an**2 - a0**2
    return b, t


def _schur_chain(
    coeffs: Sequence[sp.Rational],
) -> tuple[bool, tuple[sp.Rational, ...], tuple[tuple[sp.Rational, ...], ...]]:
    """Run the Schur–Cohn reduction to a scalar.

    Returns ``(stable, tests, levels)``: ``stable`` = all test quantities are
    strictly positive AND no reduced leading coefficient vanished (a vanishing
    leading coefficient means the criterion breaks — a zero on/off the disk that
    the strict recursion rejects, i.e. NOT strictly stable)."""
    a = tuple(coeffs)
    tests: list[sp.Rational] = []
    levels: list[tuple[sp.Rational, ...]] = []
    stable = True
    while len(a) > 1:
        if a[-1] == 0:
            # Leading coefficient of the running polynomial vanished: strict
            # Schur–Cohn is inconclusive/failed — treat as NOT strictly stable.
            stable = False
            break
        levels.append(a)
        b, t = _schur_step(a)
        tests.append(t)
        if t <= 0:
            stable = False
        a = b
    return stable, tuple(tests), tuple(levels)


def lee_yang_stable_pair_certificate(
    coeffs: Sequence,
    mode: str = "inside",
) -> LeeYangStablePairCert:
    """Build (and exactly re-check, then numerically cross-check) a Schur-
    stability certificate for the polynomial ``p(z) = Σ coeffs[i]·zⁱ``.

    ``mode = "inside"``  certifies all zeros of ``p`` lie in the OPEN unit disk.
    ``mode = "outside"`` certifies NO zeros of ``p`` lie in the CLOSED unit disk
        (all moduli ``> 1``); tested via the reciprocal ``zⁿ p(1/z)`` (reversed
        coefficients), whose zeros are the reciprocals of ``p``'s zeros.

    Refuses, in order: a bad mode; a non-rational coefficient; degree ``0``
    (constant); a zero leading coefficient ``aₙ = 0``; degree ``> 12`` (the
    test-quantity expression-size cap); a numeric root modulus within ``1e-9`` of
    ``1`` (borderline / knife-edge); a Schur-chain verdict that disagrees with
    the numeric root count (verdict mismatch); and a non-strict test quantity.
    Each refusal is a ``ValueError`` (the negative control) — no false or
    knife-edge certificate is ever emitted."""
    if mode not in ("inside", "outside"):
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: mode ∈ {{'inside', 'outside'}}; got {mode!r}")
    try:
        p = tuple(sp.Rational(sp.nsimplify(c)) for c in coeffs)
    except (TypeError, ValueError, sp.SympifyError) as exc:  # non-rational input
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: non-rational coefficient in {list(coeffs)!r} "
            f"({exc})")
    for c in p:
        if not c.is_rational:
            raise ValueError(
                f"lee_yang_stable_pair REFUSED: non-rational coefficient {c} "
                "(exact-rational arithmetic only)")
    # trim a spurious trailing zero is NOT allowed silently: aₙ = 0 is a refusal.
    n = len(p) - 1
    if n < 1:
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: need degree ≥ 1 (non-constant p); got "
            f"coeffs {list(p)} of degree {n}")
    if p[-1] == 0:
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: leading coefficient aₙ = 0 in {list(p)} "
            "(degree must be exact)")
    if n > _MAX_DEGREE:
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: degree {n} > {_MAX_DEGREE} test-quantity "
            "expression-size cap (each Jury quantity is ≈degree-2ᵏ in the aᵢ)")

    # The polynomial actually fed to the Schur recursion.
    tested_coeffs = p if mode == "inside" else tuple(reversed(p))
    if tested_coeffs[-1] == 0:
        # For 'outside' this is p(0) = a₀ = 0, i.e. a root at the origin, which
        # is inside the closed disk: the 'outside' verdict is false.
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: constant term a₀ = 0 in {list(p)} — p has "
            "a root at 0 (inside the closed disk); 'outside' verdict is false")

    stable, tests, levels = _schur_chain(tested_coeffs)

    # Numeric cross-check against the actual roots of the USER polynomial p.
    z = sp.Symbol("z")
    poly = sp.Poly(sum(c * z**i for i, c in enumerate(p)), z)
    try:
        roots = poly.nroots(n=30, maxsteps=200)
    except Exception as exc:  # noqa: BLE001 — any numeric failure is an honest refusal
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: numeric root-finding failed for {list(p)} "
            f"({exc}); cannot cross-check the stability verdict")
    moduli = tuple(sp.Abs(r) for r in roots)
    # Borderline / knife-edge: refuse if any modulus is within 1e-9 of 1.
    for m in moduli:
        if abs(m - 1) < _BORDERLINE_TOL:
            raise ValueError(
                f"lee_yang_stable_pair REFUSED: root modulus {sp.Float(m, 12)} within "
                f"1e-9 of the unit circle for {list(p)} (borderline — no knife-edge cert)")
    if mode == "inside":
        numeric_verdict = all(m < 1 for m in moduli)
    else:
        numeric_verdict = all(m > 1 for m in moduli)

    if stable != numeric_verdict:
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: Schur–Cohn verdict ({stable}) disagrees with "
            f"the numeric root moduli {[float(m) for m in moduli]} (mode={mode!r}) — "
            "verdict mismatch; a false certificate is never emitted")
    if not stable:
        raise ValueError(
            f"lee_yang_stable_pair REFUSED: p {list(p)} is NOT Schur-stable in mode "
            f"{mode!r} (test-quantity chain {list(tests)} not all strictly positive)")
    # Non-strict guard (should be implied by `stable`, but assert the honesty gate).
    for t in tests:
        if t <= 0:
            raise ValueError(
                f"lee_yang_stable_pair REFUSED: non-strict Jury test quantity {t} ≤ 0 "
                f"in chain {list(tests)} (strict positivity required)")

    return LeeYangStablePairCert(
        coeffs=tested_coeffs,
        orig_coeffs=p,
        mode=mode,
        tests=tests,
        levels=levels,
        root_moduli=tuple(sp.Float(m, 12) for m in moduli),
    )


def certify_lee_yang_stable_pair_point(family, pt, name):
    """Certify one Schur-stability instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(coeffs[, mode]) = family.special[1](pt)``.  ``n_checks`` counts the
    Jury test quantities plus the numeric cross-check, all re-verified in
    ``lee_yang_stable_pair_certificate``."""
    spec = family.special[1](pt)
    if isinstance(spec, tuple) and len(spec) == 2 and not _is_coeff_list(spec):
        coeffs, mode = spec
    else:
        coeffs, mode = spec, "inside"
    cert = lee_yang_stable_pair_certificate(coeffs, str(mode))
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = len(cert.tests) + 1  # each strict Jury quantity + the numeric cross-check
    return inst, n_checks


def _is_coeff_list(spec) -> bool:
    """Disambiguate ``spec = coeffs`` (a bare coefficient list) from
    ``spec = (coeffs, mode)``.  A 2-tuple ``(x, y)`` is a spec-with-mode only
    when ``y`` is a mode string; otherwise the 2-tuple is itself the coeffs."""
    return not (isinstance(spec[1], str) and spec[1] in ("inside", "outside"))


@dataclass
class LeeYangStablePairEmitter(Emitter):
    """Emit the Schur–Cohn Jury test-quantity chain

        theorem <name>_jury : (t₁ : ℚ) > 0 ∧ (t₂ : ℚ) > 0 ∧ … := by norm_num

    where each ``tⱼ`` is the exact rational test quantity WRITTEN OUT as the
    explicit polynomial-in-the-coefficients expression (the kernel recomputes it
    from the ``aᵢ`` literals — load-bearing, not pre-collapsed).  The bridge
    (Schur–Cohn ⟹ zeros in the open disk ⟹ Kurasov–Sarnak zeros on ``Re s = 0``)
    is a cited analytic prelude, not emitted.  Self-contained over ℚ; the kernel
    closes it by ``norm_num``.  ``conjecture1_proved = False``."""

    def __post_init__(self):
        self.kind = "lee_yang_stable_pair"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: LeeYangStablePairCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            n = len(cert.orig_coeffs) - 1
            mode = cert.mode
            # Build each test-quantity conjunct as the EXPLICIT expression
            # tₖ = (leading of level-k)² − (constant of level-k)², with the level-k
            # endpoints themselves written out as expressions in the ORIGINAL aᵢ
            # via the running Schur reduction (kernel recomputes from literals).
            conjuncts = []
            for lvl in cert.levels:
                lead_src = _expr_lean(lvl[-1])
                const_src = _expr_lean(lvl[0])
                # The ℚ ascription is LOAD-BEARING: without it Lean elaborates the
                # rational literals at ℤ, where e.g. 63/64 = 0 (integer division)
                # collapses the inequality to False (caught by local kernel verify).
                conjuncts.append(f"(({lead_src} : ℚ))^2 - (({const_src}))^2 > 0")
            chain_src = " ∧ ".join(conjuncts)
            coeff_src = ", ".join(rat_lean(c) for c in cert.orig_coeffs)
            tested_note = (
                "p itself (inside orientation)"
                if mode == "inside"
                else "the reciprocal zⁿ·p(1/z) (outside orientation: reversed coeffs)"
            )
            verdict = (
                "all zeros of p lie in the OPEN unit disk"
                if mode == "inside"
                else "NO zeros of p lie in the CLOSED unit disk (all moduli > 1)"
            )
            lines.append(
                f"-- {nm}: Schur–Cohn Jury chain for p(z) = Σ aᵢ zⁱ, a = [{coeff_src}], "
                f"degree {n}, mode='{mode}'.\n"
                f"-- Tested polynomial: {tested_note}.  Numeric root moduli of p: "
                f"{[str(m) for m in cert.root_moduli]}.\n"
                f"-- Each conjunct tⱼ = (leadⱼ)² − (constⱼ)² is written out from the aᵢ "
                f"literals via the Schur reduction bᵢ = aₙ·aᵢ − a₀·a_{{n−i}}\n"
                f"-- (load-bearing: the kernel recomputes the chain, not a pre-collapsed "
                f"rational).\n"
                f"-- BRIDGE (cited analytic prelude, NOT emitted): positivity of this Jury "
                f"chain ⟹ [Schur–Cohn theorem] {verdict}\n"
                f"-- ⟹ [Kurasov–Sarnak, JMP 61:083501 2020] all zeros of the derived "
                f"Dirichlet polynomial F(s)=Σaᵢe^(−is·λᵢ) lie on Re s = 0 — the\n"
                f"-- Fourier-quasicrystal zeros-on-a-line RH-analogue BY CONSTRUCTION.  NOT "
                f"ζ's RH (KS: the prime explicit formula gives no Fourier quasicrystal).\n"
                f"-- conjecture1_proved = False.\n"
                f"theorem {nm}_jury : {chain_src} := by norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def _expr_lean(q: sp.Rational) -> str:
    """Render an exact rational as a Lean ℚ expression (parenthesised negatives
    handled by ``rat_lean``).  Kept separate so the emitted test quantities read
    as ``(lead)^2 - (const)^2`` with each endpoint a literal."""
    return rat_lean(q)


def lee_yang_stable_pair_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Lee–Yang / Schur-stability family (kind ``lee_yang_stable_pair``).

    ``spec: pt -> coeffs`` (ascending ``(a₀ … aₙ)``, mode defaults to
    ``"inside"``) or ``pt -> (coeffs, mode)`` with ``mode ∈ {"inside",
    "outside"}``.  The theorem is a closed rational conjunction, so a single
    dummy symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("lee_yang_stable_pair", spec),
        constants=dict(constants or {}),
    )
