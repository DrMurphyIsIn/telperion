"""Log-concave single-point reduction emitter.

The certificate shape: to prove `max_{k∈ℕ, k≥1} F(k) ≤ B`, reduce the infinite
family maximum to a SINGLE point `k*` by log-concavity.  `F` is log-concave in
`k` when the exact rational inequality

    F(k+1) · F(k-1) ≤ F(k)^2        (for every integer k ≥ 2)

holds — equivalently the second difference of `log F` is ≤ 0.  A log-concave
sequence is unimodal, so it has a unique interior argmax `k*`; the single-point
bound `F(k*) ≤ B` then closes the family maximum.

The SOURCE is `bg/interior_max.py` (`family_phi`, `log_concave_in_k`,
`single_copy_value`, `InteriorMaxCertificate`): it reduced BG on large-message
single-hub families to a single-point log-concave bound but carried NO Lean.
This module is that reduction as a first-class, pipeline-enforced emitter.

CERTIFICATION (`certify_logconcave_point`) proves, over exact rationals:
  (a) LOG-CONCAVITY.  When `F` is a rational function of `k`, the general step
      `F(k)^2 − F(k+1)F(k-1) ≥ 0` is Pólya-certified once (shift `k = 1 + j`,
      `j ≥ 0`, so the whole `k ≥ 2` tail is a single nonneg-numerator / positive-
      denominator certificate).  If Pólya refuses (not a rational function, or a
      numerator that does not clear as all-nonneg after the shift), we fall back
      to an EXACT bounded-range check `k = 2 … k_max` and record the honest scope
      `range_checked` — refusing the whole instance if any checked step fails.
  (b) ARGMAX `k*`.  Located by an exact scan (unimodality lets us stop at the
      first descent, but we scan a guard window for safety).
  (c) SINGLE-POINT BOUND `F(k*) ≤ B`, as an exact rational comparison.

NEGATIVE CONTROL: a `ValueError` refusal (no Lean emitted) when `F` is not
log-concave on the checked domain, or when `F(k*) > B`.

EMITTED LEAN (`LogConcaveSinglePointEmitter`).  Per instance:
  * the single-point fact `F(k*) ≤ B` — exact rationals, `by norm_num` (a
    decidable numeric fact, standard-to-compile);
  * the per-step log-concavity facts `F(k+1)·F(k-1) ≤ F(k)^2` at each checked
    `k` — again exact-rational `by norm_num` (standard-to-compile);
  * a `unimodal_argmax` fact asserting `F(k*) ≥ F(k)` at each checked neighbour
    `k` (the concrete content of "the max is at k*", exact `by norm_num`).

HONEST SCOPE — the remaining Lean piece.  The fully general implication
"(∀k, F(k+1)F(k-1) ≤ F(k)^2) ⇒ max_k F(k) = F(k*) ≤ B" as a single closed Lean
lemma over `k : ℕ` is NOT emitted here: it needs an induction/unimodality
argument that is not a `norm_num` fact.  We emit the exact single-point bound
plus the log-concavity and neighbour-domination certificates — every one a
kernel-checkable numeric fact — and document the unimodal ASSEMBLY (chaining
the per-step facts into the global maximum) as the residual.  No `sorry`/stub is
emitted for it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Fr
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance, polya_certify
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# The stored certificate (lives on inst.payload)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LogConcaveCertificate:
    """The reduction pieces for one log-concave single-point instance.

    `F_of` evaluates `F(k)` to an exact `sp.Rational` at integer `k`.  `kstar`
    is the certified argmax; `bound` the target `B`; `fstar = F(kstar)`.
    `steps` are the checked log-concavity points `k` (each carries the exact
    triple (F(k-1), F(k), F(k+1)) as Rationals); `neighbours` are the checked
    argmax-domination points `k` with their `F(k)`.  `general_step` is True when
    log-concavity was Pólya-certified for the whole `k ≥ 2` tail (not merely a
    bounded range); `k_checked` is the bounded range that was checked either way.
    """

    kstar: int
    bound: sp.Rational
    fstar: sp.Rational
    steps: tuple[tuple[int, sp.Rational, sp.Rational, sp.Rational], ...]
    neighbours: tuple[tuple[int, sp.Rational], ...]
    general_step: bool
    k_checked: int


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _as_callable(F, k_sym):
    """Return an exact `k -> sp.Rational` evaluator for the family term `F`.

    `F` may be a sympy expression in `k_sym`, or a Python callable `k -> value`.
    In both cases the value is coerced to an exact `sp.Rational` (a float would
    poison the exact-rational discipline — refuse it loudly).
    """
    if callable(F) and not isinstance(F, sp.Expr):
        raw = F
    else:
        Fe = sp.sympify(F)

        def raw(k):
            return Fe.subs(k_sym, k)

    def ev(k):
        v = raw(int(k))
        v = sp.nsimplify(v) if not isinstance(v, (int, Fr, sp.Rational, sp.Integer)) else v
        r = sp.Rational(v)
        if r.free_symbols:
            raise ValueError(f"F({k}) did not evaluate to a rational: {v}")
        return r

    return ev


def _general_logconcave(F, k_sym) -> bool:
    """Try to Pólya-certify `F(k)^2 − F(k+1)F(k-1) ≥ 0` for the whole `k ≥ 2`
    tail at once, by shifting `k = 2 + j` (`j ≥ 0`) and certifying nonnegativity
    in `j`.  Returns True on success, False if `F` is not a sympy rational
    function or the shifted numerator does not clear as a Pólya certificate.
    """
    if not isinstance(F, sp.Expr):
        F = sp.sympify(F)
    if k_sym not in F.free_symbols and not F.is_number:
        return False
    j = sp.Symbol("j_lc", nonnegative=True)
    try:
        Fk = F.subs(k_sym, 2 + j)
        Fkm1 = F.subs(k_sym, 1 + j)
        Fkp1 = F.subs(k_sym, 3 + j)
        gap = sp.together(Fk**2 - Fkp1 * Fkm1)
        polya_certify(gap, (j,), lift_max=2)
        return True
    except (ValueError, sp.PolynomialError, TypeError, ZeroDivisionError):
        return False


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_logconcave_point(family, pt, name):
    """Certify one log-concave single-point instance: (CertifiedInstance, n_checks).

    Reads `(F, bound, k_symbol) = family.special[1](pt)`.  `F` is the family term
    (a sympy expression in `k_symbol`, or an exact callable `k -> value`), `bound`
    the target `B`, `k_symbol` the sympy symbol `F` is written in.  Certifies
    log-concavity (Pólya general step, else exact bounded range), locates the
    argmax `k*`, and checks the single-point bound `F(k*) ≤ B`.  Raises ValueError
    (the negative control — no Lean emitted) when `F` is not log-concave on the
    checked domain or `F(k*) > B`.
    """
    spec = family.special[1](pt)
    if len(spec) == 3:
        F, bound, k_sym = spec
        k_max = int(family.constants.get("k_checked", 24))
    else:
        F, bound, k_sym, k_max = spec
        k_max = int(k_max)
    bound = sp.Rational(bound)
    ev = _as_callable(F, k_sym)

    n_checks = 0

    # (a) LOG-CONCAVITY.  General Pólya step if F is a rational function of k;
    #     always also verify the bounded range exactly (cheap, and it is the
    #     content the emitted per-step facts assert).
    general = _general_logconcave(F, k_sym)
    if general:
        n_checks += 1  # the single general-step Pólya certificate

    steps: list[tuple[int, sp.Rational, sp.Rational, sp.Rational]] = []
    for k in range(2, k_max + 1):
        fm, f0, fp = ev(k - 1), ev(k), ev(k + 1)
        if fp * fm > f0 * f0:
            raise ValueError(
                f"logconcave instance '{name}' REFUSED: not log-concave at k={k} "
                f"— F({k+1})·F({k-1}) = {fp*fm} > F({k})^2 = {f0*f0}"
            )
        steps.append((k, fm, f0, fp))
        n_checks += 1
    if not steps and not general:
        raise ValueError(
            f"logconcave instance '{name}' REFUSED: no log-concavity evidence "
            f"(k_checked={k_max} left no interior steps and no general certificate)"
        )

    # (b) ARGMAX k*.  Scan k = 1 .. (k_max + 1); unimodality guarantees the
    #     global max is the first plateau/peak, but we take the exact max over
    #     the guard window to be safe.
    scan = [(k, ev(k)) for k in range(1, k_max + 2)]
    kstar, fstar = max(scan, key=lambda kv: (kv[1], -kv[0]))
    n_checks += len(scan)

    # (c) SINGLE-POINT BOUND F(k*) <= B.
    if fstar > bound:
        raise ValueError(
            f"logconcave instance '{name}' REFUSED: argmax value F(k*={kstar}) = "
            f"{fstar} exceeds the bound B = {bound}"
        )
    n_checks += 1

    neighbours = tuple((k, v) for k, v in scan if k != kstar)

    cert = LogConcaveCertificate(
        kstar=int(kstar),
        bound=bound,
        fstar=sp.Rational(fstar),
        steps=tuple(steps),
        neighbours=neighbours,
        general_step=general,
        k_checked=k_max,
    )
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=cert,
    )
    return inst, n_checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class LogConcaveSinglePointEmitter(Emitter):
    """Emit the log-concave single-point reduction as kernel-checkable numeric
    facts.  Per certified instance, four theorem groups (all exact-rational,
    `by norm_num` — the decidable, standard-to-compile shape):

      * `<name>_bound        : F(k*) ≤ B`                       (the single point)
      * `<name>_logconcave_k : F(k+1)·F(k-1) ≤ F(k)^2`          (each checked k)
      * `<name>_argmax_k     : F(k) ≤ F(k*)`                    (each neighbour k)

    The neighbour-domination facts are the concrete content of "the maximum is
    at k*"; chaining them (with the log-concavity steps) into the GLOBAL family
    maximum `∀k, F(k) ≤ B` is the documented residual assembly — a unimodality
    induction over `k : ℕ`, not a `norm_num` fact, so it is NOT emitted here (and
    no `sorry`/stub stands in for it).  Deterministic ordering: grid order, then
    increasing `k`."""

    def __post_init__(self):
        self.kind = "logconcave"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            cert: LogConcaveCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name

            # (1) single-point bound F(k*) <= B
            fstar_s = rat_lean(cert.fstar)
            bound_s = rat_lean(cert.bound)
            lines.append(
                f"theorem {base}_bound : "
                f"({fstar_s} : ℝ) ≤ {bound_s} := by norm_num\n"
            )
            n += 1

            # (2) per-step log-concavity  F(k+1)*F(k-1) <= F(k)^2
            for (k, fm, f0, fp) in cert.steps:
                lhs = rat_lean(fp)
                rhs_m = rat_lean(fm)
                sq = rat_lean(f0)
                lines.append(
                    f"theorem {base}_logconcave_{k} : "
                    f"({lhs} : ℝ) * {rhs_m} ≤ {sq} * {sq} := by norm_num\n"
                )
                n += 1

            # (3) argmax domination  F(k) <= F(k*)
            for (k, v) in cert.neighbours:
                vs = rat_lean(v)
                lines.append(
                    f"theorem {base}_argmax_{k} : "
                    f"({vs} : ℝ) ≤ {fstar_s} := by norm_num\n"
                )
                n += 1

        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def logconcave_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a log-concave single-point family (kind='logconcave').

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem base-name map.
    symbols
        The family's (real, ≥0) symbols — usually empty for a pure-`k` family;
        present only if the constants of `F` themselves range over symbols.
    spec
        A callable ``pt -> (F, bound, k_symbol)`` (or the 4-tuple
        ``(F, bound, k_symbol, k_checked)``) where ``F`` is a sympy expression
        in ``k_symbol`` (or an exact ``k -> value`` callable), ``bound`` the
        rational target ``B``, and ``k_symbol`` the sympy symbol.
        ``certify_logconcave_point`` certifies log-concavity (Pólya general step
        when ``F`` is a rational function of ``k``, else an exact bounded range),
        locates the argmax ``k*``, and checks ``F(k*) ≤ B`` — refusing (no Lean)
        otherwise.
    constants
        Optional family constants; ``k_checked`` (default 24) sets the bounded
        log-concavity / argmax scan range when the spec does not override it.
    """
    consts = dict(constants or {})
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("logconcave", spec),
        constants=consts,
    )
