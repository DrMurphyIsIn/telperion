"""Achievability-closure emitter — replace a relaxed inequality that is FALSE on
its full (relaxed) domain by its restriction to the *achievable* subset, where it
holds.

Some inequality ``Q(x) ≥ 0`` is stated over a RELAXED domain ``D = [l, d]`` — the
domain a naive relaxation allows — but is FALSE there: it dips negative on a band
``(b, d]``.  The real variable, however, is never in that band: an *achievability*
argument pins it to a smaller set ``A = [l, b] ⊆ D`` (e.g. a cavity message
``μ = 1/(j+1+S)`` with ``S ≥ 0, j ≥ 1`` satisfies ``μ ≤ 1/2``, never realizing any
``μ ∈ (1/2, 1)``).  Restricted to the ACHIEVABLE set ``A`` the inequality is TRUE.

This is exactly the ``R3Cert.CappedJointConfig`` pattern (see
``proof/formalization/R3Cert/CappedJointAchievable.lean``, PR #20): the
unconstrained ``Case2Property`` is false in ``(1/2, 1)`` (the g-step factor peaks
``≈ 1.076`` at ``μ = 13/16``), but ``Case2PropertyAchievable`` — with the
achievability hypothesis ``μ ≤ 1/2 ∨ μ = 1`` — is true, discharged by the
kernel-green single-child bound on ``0 < μ ≤ 1/2``.

The certificate has two exact, sympy-checked parts:

  (i)  ACHIEVABILITY BOUND — the concrete cap ``x ≤ b`` the real variable
       satisfies (the characterization ``x = 1/(j+1+S)`` with ``S ≥ 0, j ≥ 1``
       ⟹ ``x ≤ 1/2`` is an optional derivation helper, emitted separately);

  (ii) RESTRICTED-DOMAIN INEQUALITY — ``Q(x) ≥ 0`` for all ``x ∈ [l, b]``, verified
       exactly in sympy as a nonnegative Handelman/Bernstein combination of the
       corner products of ``(x − l)`` and ``(b − x)`` (so ``nlinarith`` closes it
       in Lean from the two bound hypotheses).

LOAD-BEARING NEGATIVE CONTROL: the certificate additionally REQUIRES a witness
that the restriction is not vacuous — a point ``x* ∈ (b, d]`` of the relaxed
domain where ``Q(x*) < 0`` — so we KNOW the achievability cap is doing work.
``achievability_certificate`` RAISES ``ValueError`` if ``Q`` is not ≥ 0 on the
achievable interval (a phantom), OR if no relaxed-domain violation exists (the
restriction would be pointless — the inequality already held on all of ``D``).

EMITTED LEAN (per instance):

    theorem <name> (x : ℝ) (hx_lo : l ≤ x) (hx_hi : x ≤ b) : 0 ≤ Q x := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - l)
                            (by linarith : (0:ℝ) ≤ b - x), hx_lo, hx_hi]

plus, optionally, the achievability derivation helper

    theorem <name>_achievable (j S : ℝ) (hj : 1 ≤ j) (hS : 0 ≤ S) :
        1 / (j + 1 + S) ≤ 1 / 2 := by ...

Bare rational literals are ℝ-ascribed (``(0:ℝ)``, ``(1/2:ℝ)``) so they don't
default to ℤ.

HONEST SCOPE: this closes ONLY the RESTRICTED inequality on the achievable set,
and certifies that the restriction is load-bearing.  It does NOT prove the (false)
relaxed statement, nor that ``[l,b]`` is the true achievable set for any particular
recursion — the caller supplies the achievability bound.  ``conjecture1_proved =
False``.  Cf. ``CappedJointAchievable.lean``.
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
except ImportError:  # run directly: `python src/telperion/emit_achievability.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


def _poly_lean(coeffs: tuple, x: str = "x") -> str:
    """Render ``Σ coeffs[k]·x^k`` as Lean source (descending powers, ℝ-safe)."""
    terms: list[str] = []
    for k in range(len(coeffs) - 1, -1, -1):
        c = sp.Rational(coeffs[k])
        if c == 0:
            continue
        cl = rat_lean(c)
        if k == 0:
            terms.append(f"{cl}")
        elif k == 1:
            terms.append(f"{cl} * {x}")
        else:
            terms.append(f"{cl} * {x}^{k}")
    return " + ".join(terms) if terms else "0"


@dataclass(frozen=True)
class AchievabilityCertificate:
    """A verified achievability-closure certificate.

    ``Q(x) = Σ coeffs[k]·x^k`` is ≥ 0 for all ``x`` in the ACHIEVABLE interval
    ``[l, b]`` (part ii), while it dips negative at ``x_violation ∈ (b, d]`` in the
    RELAXED domain ``[l, d]`` (the load-bearing witness).  ``achievable_derivation``,
    if present, is ``(j_min, S_min)`` metadata for the ``1/(j+1+S) ≤ b`` helper.
    """

    coeffs: tuple            # Q(x) = Σ coeffs[k] x^k, ascending powers
    l: sp.Rational           # achievable interval lower bound
    b: sp.Rational           # achievability cap (achievable upper bound), b < d
    d: sp.Rational           # relaxed-domain upper bound
    x_violation: sp.Rational  # a point in (b, d] with Q(x_violation) < 0
    q_violation: sp.Rational  # Q(x_violation) < 0
    emit_derivation: bool    # also emit the 1/(j+1+S) ≤ b achievability helper


def _Qval(coeffs, xv):
    return sp.Rational(
        sum(sp.Rational(c) * sp.Rational(xv) ** k for k, c in enumerate(coeffs))
    )


def achievability_certificate(
    coeffs, l, b, d, *, emit_derivation: bool = False
) -> AchievabilityCertificate:
    """Build and EXACTLY self-check an achievability-closure certificate.

    ``coeffs`` are the ascending-power rational coefficients of ``Q``.  The
    achievable interval is ``[l, b]`` inside the relaxed domain ``[l, d]`` with
    ``l < b < d``.  Verifies (exactly, in sympy):

      * ``Q ≥ 0`` on ``[l, b]`` — via a nonnegative Bernstein/Handelman expansion
        of ``Q`` in the corner products ``(x − l)^i (b − x)^j`` (all coefficients
        ≥ 0 ⟹ ``Q ≥ 0`` on ``[l, b]``);
      * the restriction is LOAD-BEARING — there is a witness ``x* ∈ (b, d]`` with
        ``Q(x*) < 0`` (so ``Q ≥ 0`` genuinely FAILS on the relaxed domain).

    RAISES ``ValueError`` if ``Q`` is not ≥ 0 on ``[l, b]`` (a phantom), if the
    interval nesting ``l < b < d`` is violated, or if no relaxed-domain violation
    is found (the achievability cap would be pointless).
    """
    coeffs = tuple(sp.nsimplify(c) for c in coeffs)
    l, b, d = sp.nsimplify(l), sp.nsimplify(b), sp.nsimplify(d)
    if not (l < b < d):
        raise ValueError(
            f"achievability needs l < b < d (achievable [l,b] strictly inside "
            f"relaxed [l,d]); got l={l}, b={b}, d={d}"
        )

    x = sp.symbols("x")
    Q = sum(c * x**k for k, c in enumerate(coeffs))
    deg = sp.Poly(Q, x).degree() if Q != 0 else 0

    # (ii) Q ≥ 0 on [l, b]: exact Bernstein/Handelman expansion in the corner
    #      products u = (x - l) ≥ 0, v = (b - x) ≥ 0 on [l, b].  Substitute the
    #      barycentric map x = l + (b - l)·s, s ∈ [0,1], and check the Bernstein
    #      coefficients of Q(x(s)) are all ≥ 0 (a sufficient certificate that
    #      nlinarith re-proves from mul_nonneg (x-l) (b-x)).
    s = sp.symbols("s")
    width = b - l
    Qs = sp.expand(Q.subs(x, l + width * s))
    # Bernstein coefficients on [0,1]: c_k = Σ_{i} a_i C(i,k)/C(n,k) ... use the
    # standard poly->Bernstein conversion via evaluating on the Bernstein basis.
    Qpoly = sp.Poly(Qs, s)
    n = max(Qpoly.degree(), 1)
    a = [Qpoly.coeff_monomial(s**k) for k in range(n + 1)]
    # poly->Bernstein on [0,1]: c_k = Σ_{i=0}^{k} a_i · C(k,i)/C(n,i).
    bern = []
    for k in range(n + 1):
        ck = sum(
            a[i] * sp.binomial(k, i) / sp.binomial(n, i)
            for i in range(0, k + 1)
        )
        bern.append(sp.nsimplify(ck))
    bernstein_ok = all(c >= 0 for c in bern)

    # Independent exact cross-check: minimum of Q on [l, b] is ≥ 0 (critical points
    # + endpoints), so we never certify a phantom even if the Bernstein basis is
    # a merely-sufficient witness that happens to fail.
    crit = [r for r in sp.solve(sp.diff(Q, x), x) if r.is_real and l <= r <= b]
    mins = [_Qval(coeffs, l), _Qval(coeffs, b)] + [_Qval(coeffs, r) for r in crit]
    true_min = min(mins)
    if true_min < 0:
        raise ValueError(
            f"achievability REFUSED: Q dips to {true_min} < 0 on the achievable "
            f"interval [{l}, {b}] — this is a PHANTOM, not a restricted-true "
            f"inequality"
        )
    if not bernstein_ok:
        raise ValueError(
            f"achievability REFUSED: no nonnegative Bernstein/Handelman witness on "
            f"[{l}, {b}] (coeffs {bern}); nlinarith is not guaranteed to close it "
            f"from the corner products"
        )

    # LOAD-BEARING witness: a point in (b, d] where Q < 0.  Search a fine grid,
    # then confirm exactly.
    x_violation = None
    q_violation = None
    steps = 200
    for i in range(1, steps + 1):
        xv = b + (d - b) * sp.Rational(i, steps)
        if xv > d:
            break
        qv = _Qval(coeffs, xv)
        if qv < 0:
            x_violation, q_violation = xv, qv
            break
    if x_violation is None:
        raise ValueError(
            f"achievability REFUSED: Q ≥ 0 everywhere on the relaxed domain "
            f"({b}, {d}] too — the achievability cap is NOT load-bearing (the "
            f"restriction does no work)"
        )

    return AchievabilityCertificate(
        coeffs=coeffs,
        l=l,
        b=b,
        d=d,
        x_violation=sp.Rational(x_violation),
        q_violation=sp.Rational(q_violation),
        emit_derivation=bool(emit_derivation),
    )


def certify_achievability_point(family, pt, name):
    """Certify one achievability instance from ``family.special[1](pt) -> spec``.

    ``spec`` is either ``(coeffs, l, b, d)`` or a dict with keys ``coeffs``,
    ``l``, ``b``, ``d`` and optional ``derivation``.  Returns
    ``(CertifiedInstance, n_checks)`` where ``n_checks`` is the number of emitted
    theorems (the restricted inequality, plus one for the achievability helper
    when enabled)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = achievability_certificate(
            spec["coeffs"], spec["l"], spec["b"], spec["d"],
            emit_derivation=bool(spec.get("derivation", False)),
        )
    else:
        coeffs, l, b, d = spec[0], spec[1], spec[2], spec[3]
        emit_derivation = bool(spec[4]) if len(spec) > 4 else False
        cert = achievability_certificate(
            coeffs, l, b, d, emit_derivation=emit_derivation
        )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = 1 + (1 if cert.emit_derivation else 0)
    return inst, n_checks


@dataclass
class AchievabilityClosureEmitter(Emitter):
    """Emit the restricted-to-achievable inequality ``0 ≤ Q x`` on ``[l, b]``,
    closed by ``nlinarith`` from the corner-product ``mul_nonneg (x-l) (b-x)``.

    Optionally also emits the achievability derivation helper
    ``1/(j+1+S) ≤ b`` (``j ≥ 1, S ≥ 0``).  Models ``CappedJointAchievable.lean``
    (``single_child_le_one`` on ``0 < μ ≤ 1/2``)."""

    def __post_init__(self):
        self.kind = "achievability"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: AchievabilityCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            l, b, d = rat_lean(cert.l), rat_lean(cert.b), rat_lean(cert.d)
            xv, qv = rat_lean(cert.x_violation), rat_lean(cert.q_violation)
            Qx = _poly_lean(cert.coeffs, "x")
            lines.append(
                f"-- Achievability closure: Q(x) ≥ 0 is FALSE on the relaxed domain "
                f"[{l}, {d}]\n"
                f"-- (witness Q({xv}) = {qv} < 0), but TRUE on the ACHIEVABLE subset "
                f"[{l}, {b}].\n"
                f"-- Restricted inequality, closed by nlinarith from the corner "
                f"product (x-l)(b-x) ≥ 0.\n"
            )
            lines.append(
                f"theorem {base} (x : ℝ) (hx_lo : {l} ≤ x) (hx_hi : x ≤ {b}) :\n"
                f"    (0:ℝ) ≤ {Qx} := by\n"
                f"  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - {l})\n"
                f"                        (by linarith : (0:ℝ) ≤ {b} - x),\n"
                f"             hx_lo, hx_hi, sq_nonneg x, sq_nonneg (x - {b})]\n"
            )
            nthm += 1
            if cert.emit_derivation:
                # the cavity-message achievability derivation: μ = 1/(j+1+S) with
                # j ≥ 1, S ≥ 0 ⟹ μ ≤ b (here b = 1/2, the CappedJointAchievable
                # case).  Denominator j+1+S ≥ 2 > 0, so 1/(j+1+S) ≤ 1/2.
                lines.append(
                    f"-- Achievability derivation: a cavity message μ = 1/(j+1+S) with "
                    f"j ≥ 1, S ≥ 0 satisfies μ ≤ {b}.\n"
                    f"theorem {base}_achievable (j S : ℝ) (hj : 1 ≤ j) (hS : 0 ≤ S) :\n"
                    f"    1 / (j + 1 + S) ≤ {b} := by\n"
                    f"  have hden : (2:ℝ) ≤ j + 1 + S := by linarith\n"
                    f"  have h2 : (0:ℝ) < 2 := by norm_num\n"
                    f"  -- 1/(j+1+S) ≤ 1/2 = {b} since 2 ≤ j+1+S; monotone reciprocal.\n"
                    f"  have hrec : 1 / (j + 1 + S) ≤ 1 / 2 :=\n"
                    f"    one_div_le_one_div_of_le h2 hden\n"
                    f"  simpa using hrec\n"
                )
                nthm += 1
        return "".join(lines), nthm


def achievability_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an achievability-closure family (kind='achievability').

    ``spec``: a callable ``pt -> (coeffs, l, b, d)`` or ``pt -> {"coeffs": ...,
    "l": ..., "b": ..., "d": ..., "derivation": bool}``, where ``coeffs`` are the
    ascending-power rational coefficients of ``Q`` and ``[l, b] ⊂ [l, d]``
    (``l < b < d``).  Refuses (at certification) a phantom (``Q`` not ≥ 0 on
    ``[l, b]``) or a non-load-bearing cap (no relaxed-domain violation)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("achievability", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # --- self-test: valid certs, negative controls, print emitted Lean ---------
    print("=== positive: the μ ≤ 1/2 cavity case  Q(x) = 1 - 2x  on [0,1/2] ===")
    # Q(x) = 1 - 2x: ≥ 0 on [0, 1/2], = 0 at 1/2, < 0 on (1/2, 1] (Q(1) = -1).
    # This is the CappedJointAchievable achievability characterization itself.
    cert = achievability_certificate((1, -2), 0, sp.Rational(1, 2), 1,
                                     emit_derivation=True)
    print(f"  cert OK: Q=1-2x on [0,1/2] ⊂ [0,1]; violation Q({cert.x_violation})="
          f"{cert.q_violation} < 0; derivation={cert.emit_derivation}")

    print("\n=== positive: quadratic  Q(x) = (1-x)(1-2x) = 1 - 3x + 2x^2  on [0,1/2] ===")
    # ≥ 0 on [0,1/2] (both factors ≥ 0), < 0 on (1/2, 1) (Q(3/4) = -1/8).
    cert2 = achievability_certificate((1, -3, 2), 0, sp.Rational(1, 2), 1)
    print(f"  cert OK: Q=(1-x)(1-2x) on [0,1/2]; violation Q({cert2.x_violation})="
          f"{cert2.q_violation} < 0")

    print("\n=== NEGATIVE CONTROL: Q < 0 on the achievable set (phantom) → ValueError ===")
    try:
        # Q(x) = 1 - 3x is negative at x = 1/2 (Q(1/2) = -1/2): NOT ≥ 0 on [0,1/2].
        achievability_certificate((1, -3), 0, sp.Rational(1, 2), 1)
        raise SystemExit("FAIL: phantom (Q<0 on achievable set) was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: cap NOT load-bearing (Q ≥ 0 on all of [l,d]) → ValueError ===")
    try:
        # Q(x) = 1 - x is ≥ 0 on all of [0, 1] (Q(1) = 0 ≥ 0): the achievability
        # cap b = 1/2 does NO work, so the restriction is pointless.
        achievability_certificate((1, -1), 0, sp.Rational(1, 2), 1)
        raise SystemExit("FAIL: non-load-bearing cap was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: bad interval nesting (b ≥ d) → ValueError ===")
    try:
        achievability_certificate((1, -2), 0, 1, sp.Rational(1, 2))
        raise SystemExit("FAIL: bad nesting was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="ach_cavity_half",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="ach_quadratic_half",
                          corners=(), payload=cert2),
    ]

    class _View:
        instances = insts

    body, nthm = AchievabilityClosureEmitter().emit_body(
        _View(), LeanProfile(namespace=("Achievability",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)
