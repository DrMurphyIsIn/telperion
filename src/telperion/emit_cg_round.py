"""Chvatal-Gomory integer-rounding emitter (VIPR-style) -- a linear goal over
INTEGER variables, derived by nonnegative combination + integer rounding.

Where the Handelman / Positivstellensatz emitters certify positivity over the
REALS, this one lives in the INTEGER linear-arithmetic world, and its single new
ingredient is the deduction the reals cannot make: from a fact

    Sigma_j c_j x_j >= v        (every c_j an INTEGER, every x_j an integer var),

the left-hand side is an integer, so the bound may be ROUNDED UP:

    Sigma_j c_j x_j >= ceil(v).

That is a Chvatal-Gomory cut -- the elementary closure operation behind every
integer-programming branch-and-cut proof, and the `round`/`unsplit` core of the
VIPR MILP certificate format (Cheung-Gleixner-Steffy, arXiv:1611.08832).

A CERTIFICATE is a list of linear FACTS `Sigma c_j x_j >= v` over declared
integer variables plus an ordered DERIVATION of steps:

  * `lincomb`  -- a NONNEGATIVE rational combination `Sigma_i lambda_i * fact_i`
    (lambda_i >= 0) plus a rational constant slack, yielding a new fact.  A
    negative multiplier would flip an inequality and is REFUSED.
  * `cg_round` -- integer rounding of a prior fact whose coefficients are ALL
    integers; REFUSED if any coefficient is non-integer (the LHS is then not
    guaranteed integral) or if the rounding is VACUOUS (`v` already an integer,
    so `ceil(v) = v` and no cut is produced -- matching the nonvacuity
    philosophy, a rounding that does no work is not a proof step).
  * the GOAL is a final fact the derivation must DOMINATE (same/greater bound on
    the same linear form), checked exactly.

Telperion is the CHECKER: every step is verified in exact rational arithmetic and
the derivation refused on the first mismatch -- a wrong combination, a non-integer
rounding, an undominated goal.  A ROUNDING-SENSITIVITY self-check additionally
requires the cut to be load-bearing: replaying the derivation with every
`cg_round` DISARMED (`ceil(v)` reverted to `v`) must FAIL to dominate the goal,
otherwise the integer rounding proved nothing the reals did not already give and
the certificate is refused as vacuous.

The emitted Lean states the goal over `(x : Int)` variables with the input facts
as integer-cleared hypotheses, and discharges the whole chain with `omega` --
Mathlib's decision procedure for linear integer arithmetic, which performs the
Chvatal-Gomory rounding internally, so a valid certificate compiles and an
invalid one (already refused here) could not:

    theorem <name> : forall x y : Int, h1 -> ... -> (goal) := by
      intro x y h1 ...
      omega
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# A FACT is (coeffs, rhs): the inequality  Sigma coeffs[s]*s >= rhs.  Coefficients
# and rhs are exact rationals (sympy.Rational); variables are integer-valued.
def _as_rat(v) -> sp.Rational:
    """Coerce a Fraction / int / sympy number to an exact sympy Rational."""
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    return sp.Rational(v)


def _norm_fact(fact) -> tuple[dict, sp.Rational]:
    """Normalize a (coeffs, rhs) fact to (dict[sym -> Rational], Rational)."""
    coeffs, rhs = fact
    out = {sp.sympify(k): _as_rat(v) for k, v in coeffs.items() if _as_rat(v) != 0}
    return out, _as_rat(rhs)


def _lincomb_step(facts, step):
    """Apply a `lincomb` step: nonnegative combination of prior facts + const.

    combo: {fact_index -> lambda (>= 0)}; const: rational slack subtracted from
    the pooled rhs (a nonnegative combination of `>=` facts gives a `>=` fact).
    Returns the new fact.  Raises ValueError on a negative multiplier or an
    out-of-range index (a refusal)."""
    combo = {int(i): _as_rat(l) for i, l in step.get("combo", {}).items()}
    const = _as_rat(step.get("const", 0))
    new_coeffs: dict = {}
    new_rhs = sp.Rational(0)
    for i, lam in combo.items():
        if lam < 0:
            raise ValueError(
                f"lincomb REFUSED: NEGATIVE multiplier {lam} on fact {i} -- a "
                "negative coefficient flips the inequality sense")
        if not (0 <= i < len(facts)):
            raise ValueError(f"lincomb REFUSED: fact index {i} out of range")
        c, r = facts[i]
        for s, cs in c.items():
            new_coeffs[s] = new_coeffs.get(s, sp.Rational(0)) + lam * cs
        new_rhs += lam * r
    new_coeffs = {s: c for s, c in new_coeffs.items() if c != 0}
    return new_coeffs, new_rhs - const


def _cg_round_step(facts, step, *, disarm=False):
    """Apply a `cg_round` step to fact `src`: integer rounding of the rhs.

    Requires every coefficient of the source fact to be an INTEGER (so the
    integer-valued LHS is itself an integer) -- else REFUSED.  Refuses a VACUOUS
    round (`v` already an integer, `ceil(v) = v`).  With `disarm=True` the round
    is a no-op (rhs kept at `v`) -- the sensitivity probe."""
    i = int(step["src"])
    if not (0 <= i < len(facts)):
        raise ValueError(f"cg_round REFUSED: source index {i} out of range")
    coeffs, rhs = facts[i]
    for s, c in coeffs.items():
        if sp.Integer(c) != c:
            raise ValueError(
                f"cg_round REFUSED: coefficient {c} on {s} is not an integer -- "
                "the LHS is not guaranteed integral, rounding is unsound")
    if sp.Integer(rhs) == rhs:
        raise ValueError(
            f"cg_round REFUSED: bound {rhs} is already an integer -- ceil is a "
            "no-op, the rounding step is VACUOUS (produces no cut)")
    if disarm:
        return dict(coeffs), rhs
    return dict(coeffs), sp.ceiling(rhs)


def _run_derivation(facts0, deriv, *, disarm_rounds=False):
    """Execute a derivation, returning the full fact list (inputs + derived)."""
    facts = list(facts0)
    for k, step in enumerate(deriv):
        rule = step["rule"]
        if rule == "lincomb":
            facts.append(_lincomb_step(facts, step))
        elif rule == "cg_round":
            facts.append(_cg_round_step(facts, step, disarm=disarm_rounds))
        else:
            raise ValueError(f"step {k} REFUSED: unknown rule {rule!r}")
    return facts


def _dominates(derived, goal) -> bool:
    """True if `derived` (coeffs, rhs) implies the goal fact: identical linear
    form and derived rhs >= goal rhs (an exact rational comparison)."""
    dc, dr = derived
    gc, gr = goal
    if set(dc) != set(gc) or any(dc[s] != gc[s] for s in dc):
        return False
    return dr >= gr


def certify_cg_round_point(family, pt, name):
    """Certify one CG-rounding instance: (CertifiedInstance, n_checks).

    Reads (facts, deriv, goal) = family.special[1](pt).  Runs the derivation,
    verifying each `lincomb` (nonnegative) and `cg_round` (integer coeffs,
    non-vacuous) step exactly, requires the final derived fact to DOMINATE the
    goal, and runs the rounding-SENSITIVITY probe: the same derivation with every
    round disarmed must FAIL to dominate.  Any failure raises ValueError (a
    refusal); no Lean is emitted for a non-certificate."""
    facts_raw, deriv, goal_raw = family.special[1](pt)
    facts0 = [_norm_fact(f) for f in facts_raw]
    goal = _norm_fact(goal_raw)
    if not deriv:
        raise ValueError(f"cg_round instance '{name}' REFUSED: empty derivation")

    checks = 0
    facts = _run_derivation(facts0, deriv)          # verifies every step exactly
    checks += len(deriv)

    final = facts[-1]
    if not _dominates(final, goal):
        raise ValueError(
            f"cg_round instance '{name}' REFUSED: final derived fact "
            f"{final} does not dominate the goal {goal} (wrong linear form or "
            "insufficient bound)")
    checks += 1

    has_round = any(s["rule"] == "cg_round" for s in deriv)
    if has_round:
        # Sensitivity: disarm every rounding and require the goal to FAIL -- the
        # cut must be load-bearing (the nonvacuity discipline, made semantic).
        disarmed = _run_derivation(facts0, deriv, disarm_rounds=True)
        if _dominates(disarmed[-1], goal):
            raise ValueError(
                f"cg_round instance '{name}' REFUSED: the goal is dominated even "
                "with every rounding DISARMED -- the Chvatal-Gomory cut is not "
                "load-bearing (the reals already give it), so the certificate is "
                "vacuous")
        checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(tuple(family.symbols), facts0, list(deriv), goal),
    )
    return inst, checks


def _ineq_int_lean(coeffs, rhs, syms) -> str:
    """Render `Sigma c_j x_j >= v` as an INTEGER-cleared Lean `>=` over Int vars:
    multiply through by the common denominator D of the rationals so every
    coefficient and the bound are integers, giving `D*(Sigma c_j x_j) >= D*v`.
    Deterministic: terms in `syms` order, denominator = lcm of all denominators."""
    from math import lcm

    dens = [sp.Rational(c).q for c in coeffs.values()] + [sp.Rational(rhs).q]
    D = 1
    for d in dens:
        D = lcm(D, int(d))
    terms = []
    for s in syms:
        c = coeffs.get(s, sp.Rational(0))
        ic = int(sp.Rational(c) * D)
        if ic == 0:
            continue
        if ic == 1:
            terms.append(f"{s}")
        elif ic == -1:
            terms.append(f"-{s}")
        else:
            terms.append(f"{ic} * {s}")
    lhs = " + ".join(terms).replace("+ -", "- ") if terms else "0"
    b = int(sp.Rational(rhs) * D)
    return f"{lhs} >= {b}"


@dataclass
class CGRoundEmitter(Emitter):
    """Emit `forall x : Int, (facts) -> goal` from a Chvatal-Gomory derivation.

    Variables are `Int`; each input fact is an integer-cleared `>=` hypothesis;
    `omega` (Mathlib's linear-integer decision procedure, which performs CG
    rounding internally) discharges the whole chain.  Deterministic: grid order,
    facts and steps as supplied."""

    def __post_init__(self):
        self.kind = "cg_round"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            syms, facts0, deriv, goal = inst.payload  # type: ignore[misc]
            # Bind only the variables this instance actually mentions (family
            # order preserved) -- an unused binder is a Lean linter warning.
            used = set(goal[0])
            for c, _r in facts0:
                used |= set(c)
            syms = tuple(s for s in syms if s in used) or tuple(syms[:1])
            binder = " ".join(str(s) for s in syms)
            hyp_names = [f"h{i}" for i in range(1, len(facts0) + 1)]
            hyp_arrows = "".join(
                f" {_ineq_int_lean(c, r, syms)} ->" for c, r in facts0)
            goal_s = _ineq_int_lean(goal[0], goal[1], syms)
            n_round = sum(1 for s in deriv if s["rule"] == "cg_round")

            lines.append(
                f"-- {inst.lean_name}: Chvatal-Gomory derivation (VIPR-style) -- "
                f"{len(deriv)} step(s), {n_round} integer round(s); the integer "
                f"LHS lets a fractional bound round up.  omega discharges the "
                f"linear-integer chain.\n"
                f"theorem {inst.lean_name} : forall {binder} : Int,"
                f"{hyp_arrows} {goal_s} := by\n"
                f"  intro {binder} {' '.join(hyp_names)}\n"
                f"  omega\n"
            )
            n += 1
        return "\n".join(lines), n


def cg_round_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Chvatal-Gomory integer-rounding family (kind='cg_round').

    spec: ``pt -> (facts, deriv, goal)`` where ``facts`` is a list of
    ``(coeffs, rhs)`` linear inequalities ``Sigma coeffs[x]*x >= rhs`` over the
    (integer-valued) ``symbols``; ``deriv`` an ordered list of steps
    (``{"rule": "lincomb", "combo": {i: lambda}, "const": c}`` or
    ``{"rule": "cg_round", "src": i}``); and ``goal`` a ``(coeffs, rhs)`` fact the
    derivation must dominate.  ``certify_cg_round_point`` verifies every step
    exactly, requires goal-domination AND rounding-sensitivity, and refuses
    otherwise.
    """
    if not tuple(symbols):
        raise ValueError("cg_round families require at least one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("cg_round", spec),
        constants=dict(constants or {}),
    )
