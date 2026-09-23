"""exp_threshold emitter -- from a threshold on the Gaussian width to exponential domination,
by the one-line discipline `1 + t <= e^t` (Mathlib's `Real.add_one_le_exp`).

conjecture1_proved = False.  Nothing in this module bears on RH: every theorem it writes is an
elementary real inequality (a threshold hypothesis on a real parameter implies an exponential
bound), already kernel-checked by hand at the sites listed below.  The emitter makes the next
island cheaper and lets the CI kernel gate confirm regenerated instances.

WHY THIS EMITTER EXISTS (SHAPES_AUDIT_48H_2026-09-22.md section 2, rank 5; B N2, C 4.5)
-----------------------------------------------------------------------------------
Every "for lam beyond an explicit threshold the exponential wins" closure in the Weil-wall
cluster is assembled by hand, twice per site: `E6Bridge7.lean:575-590` (`hexpeta`, `hexpM`),
`E6Bridge12.lean:311-316` (`hexpkappa`), `E6Bridge14.lean:78-86` (`le_exp_of_log_le`, the only
site that factored the step into a lemma), `E6Bridge11.lean:1084-1095` (`exp(-x) <= 1/x`),
`E6Bridge11.lean:910-925` (`bumpR_le`), `E6Bridge16.lean:315-317` (`y e^-y <= 1`).  The kind
`eventual_threshold` builds the max-of-ratios witness; THIS kind consumes each conjunct into an
exponential.  The two compose: the emitted theorem reads the whole nested-max threshold
hypothesis (with the `max 1` guard as an ordinary conjunct, the audit's fold-in) and returns the
guard plus every exponential consequence as a conjunction.

THE STATEMENT FAMILY
--------------------
A *bundle* instance (modes `linear`, `log`, or a `mixed` list of steps) states, for real
theorem variables and the scale variable `lam`,

    max 1 (max t_1 (max t_2 ... t_n)) <= lam  ->  1 <= lam /\\ C_1 /\\ ... /\\ C_n

(the guard and the outer `max` are omitted when absent; a single unguarded step is just
`t_1 <= lam -> C_1`), where each step is one of

  * `linear`  t = Q / (s * a * K),        C = Q <= K * exp (s * lam * a)   (or `<` when strict)
              via `div_le_iff0` + `Real.add_one_le_exp` + `linarith`: crude, no sign needed on Q;
  * `log`     t = log (max 1 (Q / K)) / (s * a),   C = Q <= K * exp (s * lam * a)
              via `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp`: sharp, and
              `Q <= 0` is not refused, it is trivial (`Q <= max 1 Q`).

`K` is optional (the audit's "downstream `Q <= K exp(lam a)` after clearing `Q/K`"); `s` is a
positive rational scale (the cluster's `2 * lam * eta`).  Each of `Q`, `a`, `K` is INDEPENDENTLY
either a symbol (a universally quantified real, with `0 < a`, `0 < K` as hypotheses) or an exact
rational literal (then `0 < a`, `0 < K` are re-decided in the kernel by `positivity` /
`norm_num`, and the threshold is an exact number the generator computes).

Standalone atoms (one theorem shape each, no threshold hypothesis):

  * `product`       `y * exp (-y) <= 1` and the commuted `exp (-y) * y <= 1`
                    (`Real.exp_neg` + `div_le_one` / `inv_mul_le_iff0`; the E6Bridge11 `bumpR_le`,
                    E6Bridge12 `hexpkappa` and E6Bridge16 `hye` shapes, `y := 2 * lam * kappa`);
  * `inv`           `0 < x -> exp (-x) <= 1 / x`, and the rational-floor face
                    `x0 <= x -> exp (-x) <= bound` with `bound >= 1 / x0` (`inv_anti0`);
  * `shifted_rate`  `0 <= y -> (c1 * y + c0) * exp (-(r * y)) <= K * exp (-(r' * y))` for
                    rational `c0, c1, r' < r` with the EMITTED constant `K = max(c0, c1/(r - r'), 0)`
                    (or a declared `K` at least that), the C 4.5 rate-split mode restricted to
                    the affine, rational-rate case this one-line discipline actually proves.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
-----------------------------------------------------------
Only the stated implication / inequality, for the stated real parameters.  A symbolic instance
carries NO numeric content beyond its shape (mode, scale, strictness, arity, guard) -- the kernel
re-derives everything from `Real.add_one_le_exp`.  A rational instance additionally pins the
exact threshold value and the signs of `a`, `K`, `s`, which the kernel re-decides.  Nothing about
zeros, nothing about RH.

ANTI-PHANTOM REFUSALS (the forge face; the generator computes and compares EXACTLY)
------------------------------------------------------------------------------------
`exp_threshold_certificate` REFUSES, never widens or weakens:

* `a <= 0` for a rational `a` (the exponent would shrink with lam; the audit's headline
  phantom -- the negative-control adapter forges exactly this and the kernel rejects it);
* `K <= 0` for a rational `K`; a non-positive or non-rational scale `s`;
* a declared `threshold` that does not match the exact recomputation `Q/(s a K)` (linear) or
  `log(max 1 (Q/K))/(s a)` (log) -- "a rational `Q` whose `Q/a` or `log(max 1 Q)/a` does not
  match the declared threshold" (B N2);
* `strict` in `log` mode (the `max 1` route has no `+1` slack; only the linear route yields `<`);
* bundling a standalone atom, an empty bundle, or more than 6 steps;
* `inv` with `x0 <= 0`, or a claimed `bound < 1 / x0` (the route proves exactly `1 / x0`;
  a tighter claim is not this kind's -- `exp_enclosure` brackets `exp` at a point);
* `shifted_rate` with `r' >= r` (no rate to trade for the polynomial), or a declared `K` below
  the certified minimum `max(c0, c1/(r - r'), 0)`;
* floats anywhere, non-rational literals, symbol names that are not ASCII Lean identifiers,
  a quantity named like the scale variable, and a symbol colliding with a generated
  hypothesis name.

Composition: `eventual_threshold` (the witness), `exp_enclosure` / `transcendental_enclosure`
(rational brackets when a `log` threshold must become a number), `poly_exp_absorption` (the
uniform-in-lam split-rate sibling at `(4m)^m`).
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

MODES = ("linear", "log", "product", "inv", "shifted_rate")
#: the modes a bundle step may take (everything else is a standalone atom)
STEP_MODES = ("linear", "log")
#: arity cap of a bundle (mirrors `eventual_threshold`; the `le_max` chain grows linearly)
MAX_STEPS = 6

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
#: names that would shadow the vocabulary the emitted proof relies on, or Lean keywords
_RESERVED = frozenset({
    "by", "fun", "have", "show", "from", "at", "in", "let", "do", "then", "else", "if",
    "match", "with", "theorem", "lemma", "def", "example", "calc", "rfl", "max", "min",
    "Real", "exp", "log", "h", "this",
})


def _refuse(msg: str) -> ValueError:
    return ValueError(f"exp_threshold REFUSED: {msg}")


# --- exact coercions --------------------------------------------------------

def _rational(v, what: str) -> sp.Rational:
    """Exactly-rational coercion; REFUSES floats, sympy Floats and non-rational values."""
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(
            f"{what} was given as a float ({v!r}); a float carries its binary expansion, not "
            "the rational you wrote -- pass a str/Fraction/sp.Rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError) as exc:
        raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
    if not isinstance(q, sp.Rational):
        raise _refuse(f"{what} = {v!r} is not rational")
    return q


def _symbol(name, what: str) -> sp.Symbol:
    """A theorem-variable name: an ASCII Lean identifier, not reserved."""
    if isinstance(name, sp.Symbol):
        name = name.name
    if not isinstance(name, str) or not _IDENT.match(name):
        raise _refuse(
            f"{what} = {name!r} is not an ASCII Lean identifier (symbolic quantities are "
            "named by plain identifiers; rationals by '3', '1/2', Fraction or sp.Rational)")
    if name in _RESERVED:
        raise _refuse(f"{what} = {name!r} is a reserved name")
    return sp.Symbol(name)


def _quantity(v, what: str):
    """A quantity is EITHER a symbol (theorem variable) OR an exact rational literal.

    Strings that are identifiers become symbols; every other string/number is coerced exactly
    (`'3'`, `'1/2'`, `Fraction`, `sp.Rational`).  Floats are refused."""
    if v is None:
        raise _refuse(f"{what} is required")
    if isinstance(v, sp.Symbol):
        return _symbol(v, what)
    if isinstance(v, str):
        s = v.strip()
        if _IDENT.match(s):
            return _symbol(s, what)
        return _rational(s, what)
    return _rational(v, what)


def _is_sym(v) -> bool:
    return isinstance(v, sp.Symbol)


def _plain(e: sp.Basic) -> sp.Basic:
    """Strip symbol assumptions so a user-built expression compares against ours by NAME."""
    e = sp.sympify(e)
    return e.xreplace({s: sp.Symbol(s.name) for s in e.free_symbols})


def _same_expr(x, y) -> bool:
    return sp.simplify(_plain(x) - _plain(y)) == 0


def _parse_declared(threshold, symbols: dict[str, sp.Symbol]) -> sp.Basic:
    """The proposer's DECLARED threshold as a sympy expression (no floats)."""
    if isinstance(threshold, (float, sp.Float)):
        raise _refuse(f"declared threshold {threshold!r} is a float")
    if isinstance(threshold, Fraction):
        return sp.Rational(threshold.numerator, threshold.denominator)
    if isinstance(threshold, str):
        try:
            e = sp.sympify(threshold, locals=dict(symbols))
        except Exception as exc:  # noqa: BLE001 -- any parse failure is a refusal
            raise _refuse(f"declared threshold {threshold!r} does not parse ({exc})") from None
    else:
        try:
            e = sp.sympify(threshold)
        except Exception as exc:  # noqa: BLE001
            raise _refuse(f"declared threshold {threshold!r} is not sympy-able ({exc})") from None
    if e.atoms(sp.Float):
        raise _refuse(f"declared threshold {threshold!r} contains a float")
    return e


# --- the certificate --------------------------------------------------------

@dataclass(frozen=True)
class ExpThresholdStep:
    """One threshold-to-exponential step of a bundle.

    `Q`, `a` (and `K` when present) are each a `sp.Symbol` (theorem variable) or an exact
    `sp.Rational`; `scale` is the positive rational `s` in `s * lam * a`; `strict` selects the
    `<` consequence (linear only); `threshold` is the EXACT re-derived threshold expression the
    emitted hypothesis states verbatim (`Q/(s a K)` or `log(max 1 (Q/K))/(s a)`)."""

    mode: str
    Q: sp.Basic
    a: sp.Basic
    K: sp.Basic | None
    scale: sp.Rational
    strict: bool
    threshold: sp.Basic

    @property
    def symbolic(self) -> bool:
        """True when nothing numeric is pinned (every quantity is a theorem variable)."""
        return _is_sym(self.Q) and _is_sym(self.a) and (self.K is None or _is_sym(self.K))


@dataclass(frozen=True)
class ExpThresholdCert:
    """One exp-threshold certificate: a bundle (`linear` / `log` / `mixed`, with `steps`,
    `guard`, `lam`) or a standalone atom (`product`, `inv`, `shifted_rate`)."""

    mode: str
    steps: tuple[ExpThresholdStep, ...] = ()
    guard: bool = False
    lam: str = "lam"
    # product / shifted_rate variable, inv variable
    y: str = "y"
    x: str = "x"
    # inv floor face: `x0 <= x -> exp (-x) <= bound`
    x0: sp.Rational | None = None
    bound: sp.Rational | None = None
    # shifted_rate data: `(c1 y + c0) e^{-r y} <= K e^{-r' y}` on `0 <= y`
    c0: sp.Rational | None = None
    c1: sp.Rational | None = None
    r: sp.Rational | None = None
    r_prime: sp.Rational | None = None
    K: sp.Rational | None = None

    @property
    def is_bundle(self) -> bool:
        return self.mode in ("linear", "log", "mixed")

    @property
    def n_conjuncts(self) -> int:
        return (1 if self.guard else 0) + len(self.steps)


def _step(d: dict, default_mode: str, lam: str, idx: int) -> ExpThresholdStep:
    d = dict(d)
    mode = d.pop("mode", default_mode)
    if mode not in STEP_MODES:
        raise _refuse(
            f"step {idx}: mode {mode!r} is not a bundle step mode {STEP_MODES} (the atoms "
            f"{tuple(m for m in MODES if m not in STEP_MODES)} are standalone instances)")
    Q = _quantity(d.pop("Q", None), f"step {idx}: Q")
    a = _quantity(d.pop("a", None), f"step {idx}: a")
    Kraw = d.pop("K", None)
    K = _quantity(Kraw, f"step {idx}: K") if Kraw is not None else None
    scale = _rational(d.pop("scale", 1), f"step {idx}: scale")
    strict = d.pop("strict", False)
    declared = d.pop("threshold", None)
    if d:
        raise _refuse(f"step {idx}: unknown keys {sorted(d)}")
    if not isinstance(strict, bool):
        raise _refuse(f"step {idx}: strict must be a bool, got {strict!r}")
    if scale <= 0:
        raise _refuse(f"step {idx}: scale s = {scale} must be a positive rational")
    if not _is_sym(a) and a <= 0:
        raise _refuse(
            f"step {idx}: a = {a} <= 0 -- the exponent s * lam * a would not grow with lam; "
            "the implication is FALSE at lam = 0 (the audit's phantom instance)")
    if K is not None and not _is_sym(K) and K <= 0:
        raise _refuse(f"step {idx}: K = {K} <= 0 (the K-clearing step divides by K)")
    if strict and mode == "log":
        raise _refuse(
            f"step {idx}: strict consequence in log mode -- `Q <= max 1 Q = exp (log (max 1 Q))`"
            " has no +1 slack; only the linear route (`s lam a < s lam a + 1 <= exp`) yields `<`")
    for what, v in (("Q", Q), ("a", a), ("K", K)):
        if _is_sym(v) and v.name == lam:
            raise _refuse(f"step {idx}: {what} is named like the scale variable {lam!r}")
    # the EXACT threshold this step's hypothesis will state
    Kx = K if K is not None else sp.Integer(1)
    if mode == "linear":
        computed = Q / (scale * a * Kx)
    else:
        Qc = Q / K if K is not None else Q
        computed = sp.log(sp.Max(1, Qc)) / (scale * a)
    if declared is not None:
        syms = {v.name: v for v in (Q, a, K) if _is_sym(v)}
        dec = _parse_declared(declared, syms)
        if not _same_expr(dec, computed):
            raise _refuse(
                f"step {idx}: declared threshold {dec} does not match the exact recomputation "
                f"{computed} ({'Q/(s a K)' if mode == 'linear' else 'log(max 1 (Q/K))/(s a)'}); "
                "the generator computes and compares exactly and never adjusts the claim")
    return ExpThresholdStep(mode=mode, Q=Q, a=a, K=K, scale=scale, strict=strict,
                            threshold=computed)


def exp_threshold_certificate(
    mode: str = "linear", *,
    steps=None, guard: bool = False, lam: str = "lam",
    Q=None, a=None, K=None, scale=1, strict: bool = False, threshold=None,
    y: str = "y", x: str = "x", x0=None, bound=None,
    c0=None, c1=None, r=None, r_prime=None,
) -> ExpThresholdCert:
    """Build (and exactly re-check) an exp-threshold certificate.

    Bundle (`mode` in `linear` / `log`): either ONE step from the keyword arguments
    `Q, a, K, scale, strict, threshold`, or `steps=[{...}, ...]` (each dict carries the same
    keys plus an optional per-step `mode`); `guard=True` adds the `max 1` conjunct.
    Atoms: `product` (`y`), `inv` (`x`, optional rational floor `x0` and `bound`),
    `shifted_rate` (`y`, rationals `c0, c1, r, r_prime`, optional declared `K`).
    See the module docstring for the refusal list."""
    if mode not in MODES:
        raise _refuse(f"unknown mode {mode!r} (expected one of {MODES})")
    if not isinstance(guard, bool):
        raise _refuse(f"guard must be a bool, got {guard!r}")
    lam_sym = _symbol(lam, "lam").name
    if mode in STEP_MODES:
        if steps is None:
            steps = [dict(Q=Q, a=a, K=K, scale=scale, strict=strict, threshold=threshold)]
        elif any(v is not None for v in (Q, a, K, threshold)) or strict or scale != 1:
            raise _refuse("give either `steps=[...]` or the single-step keywords, not both")
        steps = list(steps)
        if not steps:
            raise _refuse("an empty bundle certifies nothing")
        if len(steps) > MAX_STEPS:
            raise _refuse(f"bundle arity {len(steps)} exceeds the cap {MAX_STEPS}")
        built = tuple(_step(d, mode, lam_sym, i + 1) for i, d in enumerate(steps))
        # a symbol may play several roles, but never collide with a generated hypothesis name
        names = {v.name for s in built for v in (s.Q, s.a, s.K) if _is_sym(v)}
        # Every name the emitted bodies bind: the per-symbol positivity hypotheses, the
        # guard, the per-step thresholds, and the block-locals of the step and atom
        # renderers.  A user symbol that shadows one of these would make the emitted
        # proof refer to the wrong term, so the shape is refused rather than emitted.
        hyps = ({f"h{n}0" for n in names} | {"hlam1"}
                | {f"ht{i+1}" for i in range(len(built))}
                | {"h1", "h2", "h3", "hmax", "hsplit", "hx0"})
        clash = sorted(names & hyps)
        if clash:
            raise _refuse(f"symbol name(s) {clash} collide with generated hypothesis names")
        modes = {s.mode for s in built}
        cmode = modes.pop() if len(modes) == 1 else "mixed"
        return ExpThresholdCert(mode=cmode, steps=built, guard=guard, lam=lam_sym)

    # --- standalone atoms ---
    if steps is not None or guard or any(v is not None for v in (Q, a, threshold)):
        raise _refuse(f"mode {mode!r} is a standalone atom: no steps, no guard, no Q/a/threshold")
    if mode != "shifted_rate" and K is not None:
        raise _refuse(f"mode {mode!r} takes no K (only shifted_rate emits a constant)")
    if mode == "product":
        yn = _symbol(y, "y").name
        return ExpThresholdCert(mode="product", y=yn, lam=lam_sym)
    if mode == "inv":
        xn = _symbol(x, "x").name
        if x0 is None:
            if bound is not None:
                raise _refuse("inv: a bound needs a rational floor x0 (the symbolic face proves "
                              "exp (-x) <= 1 / x only)")
            return ExpThresholdCert(mode="inv", x=xn, lam=lam_sym)
        x0q = _rational(x0, "inv: x0")
        if x0q <= 0:
            raise _refuse(f"inv: floor x0 = {x0q} <= 0 (1 / x0 is not a bound on exp (-x))")
        bq = _rational(bound, "inv: bound") if bound is not None else 1 / x0q
        if bq < 1 / x0q:
            raise _refuse(
                f"inv: claimed bound {bq} is BELOW 1 / x0 = {1 / x0q}; this route proves exactly "
                "exp (-x) <= 1 / x0 and never tightens (bracket exp with exp_enclosure instead)")
        return ExpThresholdCert(mode="inv", x=xn, x0=x0q, bound=bq, lam=lam_sym)
    # shifted_rate
    yn = _symbol(y, "y").name
    c0q = _rational(c0, "shifted_rate: c0")
    c1q = _rational(c1, "shifted_rate: c1")
    rq = _rational(r, "shifted_rate: r")
    rpq = _rational(r_prime, "shifted_rate: r_prime")
    delta = rq - rpq
    if delta <= 0:
        raise _refuse(
            f"shifted_rate: r' = {rpq} >= r = {rq} -- no rate is traded for the polynomial, "
            "P(y) e^{-r y} <= K e^{-r' y} fails as y -> oo for any K when c1 > 0")
    kmin = max(c0q, c1q / delta, sp.Integer(0))
    Kq = _rational(K, "shifted_rate: K") if K is not None else kmin
    if Kq < kmin:
        raise _refuse(
            f"shifted_rate: declared K = {Kq} is below the certified minimum "
            f"max(c0, c1/(r - r'), 0) = {kmin} (the `1 + t <= e^t` route needs c0 <= K and "
            "c1 <= K (r - r'))")
    return ExpThresholdCert(mode="shifted_rate", y=yn, c0=c0q, c1=c1q, r=rq, r_prime=rpq,
                            K=Kq, lam=lam_sym)


def certify_exp_threshold_point(family, pt, name):
    """Certify one exp-threshold point: ``(CertifiedInstance, n_checks)``.

    Reads the spec dict from ``family.special[1](pt)`` (the keyword arguments of
    :func:`exp_threshold_certificate`) and re-checks it (raising on every phantom)."""
    spec = dict(family.special[1](pt))
    cert = exp_threshold_certificate(**spec)
    n_checks = 1 + len(cert.steps)
    return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), n_checks


# --- Lean rendering ---------------------------------------------------------

def _q_lean(v) -> str:
    """A quantity as Lean: the symbol name, or an R-ascribed exact rational literal."""
    if _is_sym(v):
        return v.name
    return f"({rat_lean(v)} : ℝ)"


def _atomic(s: str) -> bool:
    """True when `s` needs no parentheses as a function argument."""
    if _IDENT.match(s) or s.isdigit():
        return True
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return False
        return True
    return False


def _par(s: str) -> str:
    return s if _atomic(s) else f"({s})"


def _nested_max(terms: list[str]) -> str:
    if len(terms) == 1:
        return terms[0]
    if len(terms) == 2:
        return f"max {_par(terms[0])} {_par(terms[1])}"
    return f"max {_par(terms[0])} ({_nested_max(terms[1:])})"


def _le_max_chain(j: int, m: int) -> str:
    """`term_j <= lam` from `h : max t_0 (max t_1 ... t_{m-1}) <= lam` (E6Bridge7's chain)."""
    if j < m - 1:
        expr, wraps = "(le_max_left _ _)", j
    else:
        expr, wraps = "(le_max_right _ _)", m - 2
    for _ in range(wraps):
        expr = f"({expr}.trans (le_max_right _ _))"
    return f"{expr}.trans h"


def _scaled(scale: sp.Rational, lam: str, a: str) -> str:
    """`s * lam * a` (the exponent), `lam * a` when s = 1."""
    return f"{lam} * {a}" if scale == 1 else f"{rat_lean(scale)} * {lam} * {a}"


def _den_parts(scale: sp.Rational, a: str, K: str | None) -> list[str]:
    parts = [] if scale == 1 else [rat_lean(scale)]
    parts.append(a)
    if K is not None:
        parts.append(K)
    return parts


def _den(parts: list[str]) -> str:
    return parts[0] if len(parts) == 1 else "(" + " * ".join(parts) + ")"


def _step_threshold(st: ExpThresholdStep, lam: str) -> str:
    Q, a = _q_lean(st.Q), _q_lean(st.a)
    K = _q_lean(st.K) if st.K is not None else None
    if st.mode == "linear":
        return f"{Q} / {_den(_den_parts(st.scale, a, K))}"
    Qc = f"{Q} / {K}" if K is not None else Q
    return f"Real.log (max 1 {_par(Qc)}) / {_den(_den_parts(st.scale, a, None))}"


def _step_conclusion(st: ExpThresholdStep, lam: str) -> str:
    Q, a = _q_lean(st.Q), _q_lean(st.a)
    rel = "<" if st.strict else "≤"
    rhs = f"Real.exp ({_scaled(st.scale, lam, a)})"
    if st.K is not None:
        rhs = f"{_q_lean(st.K)} * {rhs}"
    return f"{Q} {rel} {rhs}"


def _step_block(st: ExpThresholdStep, lam: str, ht: str, idx: int) -> list[str]:
    """The frozen tactic block closing `C_i` from `ht : t_i <= lam` (indent 0)."""
    Q, a = _q_lean(st.Q), _q_lean(st.a)
    K = _q_lean(st.K) if st.K is not None else None
    sla = _scaled(st.scale, lam, a)
    lines: list[str] = []
    hK = None
    if st.K is not None:
        if _is_sym(st.K):
            hK = f"h{st.K.name}0"
        else:
            hK = f"hK{idx}0"
            lines.append(f"have {hK} : (0 : ℝ) < {K} := by norm_num")
    if st.mode == "linear":
        prod = " * ".join(_den_parts(st.scale, a, K))
        if K is not None:
            rel = "<" if st.strict else "≤"
            lines += [
                f"have h1 : {Q} / {K} ≤ {sla} := by",
                f"  rw [div_le_iff₀ {hK}]",
                f"  have := (div_le_iff₀ (by positivity : (0 : ℝ) < {prod})).mp {ht}",
                "  linarith",
                f"have h2 : {sla} + 1 ≤ Real.exp ({sla}) := Real.add_one_le_exp _",
                f"have h3 : {Q} / {K} {rel} Real.exp ({sla}) := by linarith",
                f"rwa [div_{'lt' if st.strict else 'le'}_iff₀ {hK}, mul_comm] at h3",
            ]
        else:
            lines += [
                f"have h1 : {Q} ≤ {sla} := by",
                f"  have := (div_le_iff₀ (by positivity : (0 : ℝ) < {prod})).mp {ht}",
                "  linarith",
                f"have h2 : {sla} + 1 ≤ Real.exp ({sla}) := Real.add_one_le_exp _",
                "linarith",
            ]
        return lines
    # log mode
    prod = " * ".join(_den_parts(st.scale, a, None))
    Qc = f"{Q} / {K}" if K is not None else Q
    Qcp = _par(Qc)
    lines += [
        f"have hmax : 0 < max 1 {Qcp} := lt_max_of_lt_left one_pos",
        f"have h1 : Real.log (max 1 {Qcp}) ≤ {sla} := by",
        f"  have := (div_le_iff₀ (by positivity : (0 : ℝ) < {prod})).mp {ht}",
        "  linarith",
    ]
    calc = [
        f"calc {Qc} ≤ max 1 {Qcp} := le_max_right _ _",
        f"  _ = Real.exp (Real.log (max 1 {Qcp})) := (Real.exp_log hmax).symm",
        f"  _ ≤ Real.exp ({sla}) := Real.exp_le_exp.mpr h1",
    ]
    if K is not None:
        lines.append(f"have h3 : {Qc} ≤ Real.exp ({sla}) := by")
        lines += ["  " + c for c in calc]
        lines.append(f"rwa [div_le_iff₀ {hK}, mul_comm] at h3")
    else:
        lines += calc
    return lines


def _indent(lines: list[str], n: int) -> list[str]:
    pad = " " * n
    return [pad + ln if ln else ln for ln in lines]


def _bundle_theorem(cert: ExpThresholdCert, nm: str) -> str:
    lam = cert.lam
    # binders: symbols in order of first appearance (Q, a, K per step), then lam
    order: list[str] = []
    pos: list[str] = []
    for st in cert.steps:
        for v in (st.Q, st.a, st.K):
            if _is_sym(v) and v.name not in order:
                order.append(v.name)
        for v in (st.a, st.K):
            if _is_sym(v) and v.name not in pos:
                pos.append(v.name)
    binder = " ".join(order + [lam])
    hyps = "".join(f" (h{n}0 : 0 < {n})" for n in pos)
    thresholds = [_step_threshold(st, lam) for st in cert.steps]
    terms = (["1"] if cert.guard else []) + thresholds
    m = len(terms)
    hyp = f"{_nested_max(terms)} ≤ {lam}"
    concls = ([f"1 ≤ {lam}"] if cert.guard else []) + [
        _step_conclusion(st, lam) for st in cert.steps]
    concl = " ∧ ".join(concls)
    body: list[str] = []
    ht_names: list[str] = []
    if m == 1:
        ht_names = ["h"]
    else:
        j = 0
        if cert.guard:
            body.append(f"have hlam1 : 1 ≤ {lam} := {_le_max_chain(0, m)}")
            j = 1
        for i, t in enumerate(thresholds):
            one = f"have ht{i+1} : {t} ≤ {lam} := {_le_max_chain(j + i, m)}"
            if len(one) + 2 > 100:  # break before `:=` as E6Bridge14's hthr1/hthr2 do; the
                # continuation sits two columns deeper than the `have` (column 4 after indent)
                one = f"have ht{i+1} : {t} ≤ {lam} :=\n    {_le_max_chain(j + i, m)}"
            body.append(one)
            ht_names.append(f"ht{i+1}")
    blocks = [_step_block(st, lam, ht_names[i], i + 1) for i, st in enumerate(cert.steps)]
    if len(concls) == 1:
        body += blocks[0]
    else:
        holes = (["hlam1"] if cert.guard else []) + ["?_"] * len(cert.steps)
        body.append(f"refine ⟨{', '.join(holes)}⟩")
        for blk in blocks:
            body.append("· " + blk[0])
            body += _indent(blk[1:], 2)
    hyp_line = f"\n   {hyps}" if hyps else ""
    head = f"theorem {nm} ({binder} : ℝ){hyp_line}\n    (h : {hyp}) :\n    {concl} := by\n"
    return head + "\n".join(_indent(body, 2)) + "\n"


def _describe_step(st: ExpThresholdStep) -> str:
    bits = [st.mode, f"scale {st.scale}"]
    bits.append("K-cleared" if st.K is not None else "no K")
    if st.strict:
        bits.append("strict")
    pinned = [f"{w} = {v}" for w, v in (("Q", st.Q), ("a", st.a), ("K", st.K))
              if v is not None and not _is_sym(v)]
    bits.append("pinned " + ", ".join(pinned) if pinned else "symbolic")
    bits.append(f"threshold {st.threshold}")
    return "; ".join(bits)


def _product_theorems(cert: ExpThresholdCert, nm: str) -> str:
    y = cert.y
    return (
        f"theorem {nm} ({y} : ℝ) : {y} * Real.exp (-{y}) ≤ 1 := by\n"
        f"  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]\n"
        f"  linarith [Real.add_one_le_exp {y}]\n"
        f"\n"
        f"/-- `{nm}_comm` -- the commuted face `exp (-y) * y <= 1` (the E6Bridge12 `hexpkappa`\n"
        f"    shape, `y := 2 * lam * kappa`), by `Real.exp_neg` + `inv_mul_le_iff0`.\n"
        f"    conjecture1_proved = False. -/\n"
        f"theorem {nm}_comm ({y} : ℝ) : Real.exp (-{y}) * {y} ≤ 1 := by\n"
        f"  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]\n"
        f"  linarith [Real.add_one_le_exp {y}]\n"
    )


def _inv_theorem(cert: ExpThresholdCert, nm: str) -> str:
    x = cert.x
    core = (
        f"  rw [Real.exp_neg, one_div]\n"
        f"  exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp {x}])\n"
    )
    if cert.x0 is None:
        return (f"theorem {nm} ({x} : ℝ) (hx0 : 0 < {x}) : Real.exp (-{x}) ≤ 1 / {x} := by\n"
                + core)
    x0, b = rat_lean(cert.x0), rat_lean(cert.bound)
    return (
        f"theorem {nm} ({x} : ℝ) (hx : ({x0} : ℝ) ≤ {x}) : Real.exp (-{x}) ≤ ({b} : ℝ) := by\n"
        f"  have hx0 : 0 < {x} := lt_of_lt_of_le (by norm_num : (0 : ℝ) < {x0}) hx\n"
        f"  have h1 : Real.exp (-{x}) ≤ 1 / {x} := by\n"
        f"    rw [Real.exp_neg, one_div]\n"
        f"    exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp {x}])\n"
        f"  have h2 : 1 / {x} ≤ 1 / ({x0} : ℝ) := one_div_le_one_div_of_le (by norm_num) hx\n"
        f"  have h3 : 1 / ({x0} : ℝ) ≤ ({b} : ℝ) := by norm_num\n"
        f"  linarith\n"
    )


def _shifted_rate_theorem(cert: ExpThresholdCert, nm: str) -> str:
    y = cert.y
    c0, c1, r, rp, K = (rat_lean(v) for v in (cert.c0, cert.c1, cert.r, cert.r_prime, cert.K))
    d = rat_lean(cert.r - cert.r_prime)
    return (
        f"theorem {nm} ({y} : ℝ) (hy : 0 ≤ {y}) :\n"
        f"    ({c1} * {y} + {c0}) * Real.exp (-({r} * {y})) ≤ {K} * Real.exp (-({rp} * {y})) := by\n"
        f"  have hδ : 1 + {d} * {y} ≤ Real.exp ({d} * {y}) := by\n"
        f"    linarith [Real.add_one_le_exp ({d} * {y})]\n"
        f"  have h1 : {c1} * {y} + {c0} ≤ {K} * (1 + {d} * {y}) := by linarith\n"
        f"  have h2 : {K} * (1 + {d} * {y}) ≤ {K} * Real.exp ({d} * {y}) :=\n"
        f"    mul_le_mul_of_nonneg_left hδ (by norm_num)\n"
        f"  have hsplit : Real.exp ({d} * {y}) * Real.exp (-({r} * {y}))\n"
        f"      = Real.exp (-({rp} * {y})) := by\n"
        f"    rw [← Real.exp_add]\n"
        f"    congr 1\n"
        f"    ring\n"
        f"  calc ({c1} * {y} + {c0}) * Real.exp (-({r} * {y}))\n"
        f"      ≤ {K} * Real.exp ({d} * {y}) * Real.exp (-({r} * {y})) :=\n"
        f"        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le\n"
        f"    _ = {K} * Real.exp (-({rp} * {y})) := by rw [mul_assoc, hsplit]\n"
    )


@dataclass
class ExpThresholdEmitter(Emitter):
    """Emit threshold-to-exponential theorems (bundles reading a nested-max threshold, and
    the product / inverse / shifted-rate atoms), each proved from `Real.add_one_le_exp` by the
    frozen tactic skeleton of the hand proofs it regenerates (`div_le_iff0` + `linarith`;
    `Real.exp_log` + `Real.exp_le_exp`; `Real.exp_neg` + `inv_mul_le_iff0` / `inv_anti0`).
    No search, no `decide`, no `sorry`; `exp_threshold_certificate` refuses every phantom.
    conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "exp_threshold"

    def _header(self, cert: ExpThresholdCert, nm: str) -> str:
        if cert.is_bundle:
            what = (f"{cert.mode} bundle, {len(cert.steps)} step(s)"
                    + (", guarded by `max 1`" if cert.guard else ""))
            detail = "".join(f"\n    step {i+1}: {_describe_step(st)};"
                             for i, st in enumerate(cert.steps))
            extract = ("each conjunct extracted from the nested `max` by a `le_max` chain"
                       if cert.n_conjuncts > 1 else "the threshold read directly from `h`")
            route = (f"{extract},\n    then `div_le_iff0` + `Real.add_one_le_exp` + "
                     "`linarith` (linear) or\n    `Real.exp_log (lt_max_of_lt_left one_pos)` "
                     "+ `Real.exp_le_exp` (log)")
        elif cert.mode == "product":
            what, detail = "product atom `y * exp (-y) <= 1`", ""
            route = "`Real.exp_neg` + `div_le_one` / `inv_mul_le_iff0` + `Real.add_one_le_exp`"
        elif cert.mode == "inv":
            what = ("inverse atom `exp (-x) <= 1 / x`" if cert.x0 is None else
                    f"inverse atom at the rational floor x0 = {cert.x0}, bound {cert.bound}")
            detail = ""
            route = "`Real.exp_neg` + `inv_anti0` + `Real.add_one_le_exp`"
        else:
            what = (f"shifted-rate atom, P(y) = {cert.c1} y + {cert.c0}, rates r = {cert.r}, "
                    f"r' = {cert.r_prime}, emitted constant K = {cert.K}")
            detail = ""
            route = ("`Real.add_one_le_exp` at the rate difference, `mul_le_mul_of_nonneg_*`, "
                     "`Real.exp_add`")
        return (
            f"/-- `{nm}` -- exp_threshold: {what}.{detail}\n"
            f"    Route: {route}.\n"
            f"    An elementary real inequality re-derived in the kernel; the generator REFUSES\n"
            f"    a non-positive rational `a`/`K`/scale and a declared threshold that does not\n"
            f"    match its exact recomputation.  Nothing about zeros; nothing about RH.\n"
            f"    conjecture1_proved = False. -/"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ExpThresholdCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            lines.append(self._header(cert, nm))
            if cert.is_bundle:
                lines.append(_bundle_theorem(cert, nm))
                n_thm += 1
            elif cert.mode == "product":
                lines.append(_product_theorems(cert, nm))
                n_thm += 2
            elif cert.mode == "inv":
                lines.append(_inv_theorem(cert, nm))
                n_thm += 1
            else:
                lines.append(_shifted_rate_theorem(cert, nm))
                n_thm += 1
        return "\n".join(lines), n_thm


def exp_threshold_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an exp-threshold family (kind ``exp_threshold``).

    ``spec: pt -> dict`` -- the keyword arguments of :func:`exp_threshold_certificate`
    (``mode``, ``steps`` / ``Q, a, K, scale, strict, threshold``, ``guard``, ``lam``; or the
    atom data ``y`` / ``x, x0, bound`` / ``c0, c1, r, r_prime, K``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("exp_threshold", spec),
        constants=dict(constants or {}),
    )
