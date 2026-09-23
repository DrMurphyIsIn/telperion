"""zero_sum_majorant emitter -- a zero-supported family is summable through a finite ordinate
window plus the local-count tail `m(rho) C/(1 + |gamma_rho|^2)`.

conjecture1_proved = False.  Nothing in this module bears on RH: every theorem it writes is a
summability / pointwise-majorant fact about a family indexed by the nontrivial zeros, true
whatever their real parts are, plus one rational inequality on the open strip `0 < Re rho < 1`.
It says nothing about WHERE the zeros are.

WHY THIS EMITTER EXISTS (SHAPES_AUDIT_48H_2026-09-22.md section 2, rank 2; C 3.1 merged with B N5)
-----------------------------------------------------------------------------------------------
Thirteen hand-written sites on the rvm_bridge / li / Zeta23 islands prove the SAME thing the SAME
way.  A term family `f : C -> C` supported on the nontrivial zeros is shown summable by

  (a) `f rho = 0` off `IsNontrivialZero` (a hypothesis-free rewrite through
      `RvMBridge4.zeroMult_eq_zero_of_not_nontrivial`);
  (b) the finitely many zeros of a centred ordinate window `|Im rho - a| < h` absorbed by a
      `Set.indicator` (finite by `zetaSeam.finite_window`);
  (c) every OTHER zero bounded by the local-count majorant `m(rho) C_far/(1 + normSq gamma_rho)`,
      which `RvMBridgeGauss.summable_mult_div_one_add_normSq` sums.

(a)-(c) are ONE abstract atom on the island since the P1 prelude (`RvMBridgeXi.zeroBoundAt`,
`norm_le_zeroBoundAt`, `summable_zeroBoundAt`; the window of `E6Bridge19.lean`'s `zeroBound`
generalised to a centre `a` and radius `h`).  What every site re-proves BY HAND is the step that
feeds (c): ONE two-variable rational inequality on the strip, e.g.

    1/|rho|^2           <= (9/4)/(1 + |gamma_rho|^2)             (E6Bridge15 liBound, E6Bridge19 zbound)
    1/(Im rho - Im s)^2 <= (13/4 + 2 (Im s)^2)/(1 + |gamma_rho|^2) (E6Bridge18 polBound)

(79 hand `nlinarith` strip calls in the cluster, audit C 5.3).  That inequality is the kernel
content this emitter certifies, exactly; the composition with the atom is a fixed skeleton.

THE STATEMENT FAMILY (mode `zero_window`)
-----------------------------------------
With `x = Re rho`, `w = Im rho`, a centre `a` (a rational, or a polynomial in declared real
parameters such as `Im s`), a near radius `h in {0, 1, 2}`, a far constant `C >= 0`, a numerator
`N >= 0` and a denominator shape `D` (`normSq rho`, `(Im rho - a)^2` or `1 + (Im rho - a)^2`),
each instance `nm` emits up to three theorems (faces):

  nm_strip     : IsNontrivialZero rho -> h <= |Im rho - a| -> N / D <= C / (1 + normSq (gammaOf rho))
  nm_le        : (f = 0 off the zeros) -> (norm f <= b on the window |Im rho - a| < h)
                 -> (norm f <= m(rho) * ([K *] (N / D)) off it)
                 -> norm (f rho) <= RvMBridgeXi.zeroBoundAt a h ([K *] C) b rho
  nm_summable  : the support and far-shape hypotheses -> Summable f

`K` is present when `prefactor=True`: the instance's size prefactor (`2^n` for the Li kernel,
`(k+1)! 2^(k+2)` for the Taylor ladder), a real `K >= 0` that multiplies BOTH the far-shape
hypothesis and the emitted constant, so it never touches the certified strip inequality.  The
term family's own analysis (that `norm f` has the shape `m * N/D` off the window) is NOT emitted:
it enters `nm_le` / `nm_summable` as the named hypotheses `hzero`, `hwin`, `hshape`.

THE STATEMENT FAMILY (mode `tail_envelope`, audit B N5, the consumer face)
------------------------------------------------------------------------
  nm_envelope  : ‖f x‖ <= E * w x on S, w >= 0 summable -> ‖Sum'_{x : S} f x‖ <= E * Sum' w
                 (`E` a rational >= 0 re-checked by `norm_num`, or symbolic with `0 <= E` as a
                 hypothesis -- then the face IS the prelude's `norm_tsum_subtype_le_mul_tsum`);
  nm_rate      : 1 <= lam -> phi <= P ->
                 exp (2 lam phi) <= exp (2 (lam - 1) P) * exp (2 phi)  /\\  exp (2 (lam - 1) P) <= 1
                 for a RATIONAL `P < 0`.  The first conjunct holds for every P; the second is the
                 content `P < 0` buys (the envelope factor does not grow with lam), and it is
                 FALSE for every `P > 0` at lam = 2, so a forged sign cannot compile.

THE CERTIFICATE (untrusted; the Lean kernel is the only trust)
--------------------------------------------------------------
Clearing both (positive) denominators of the strip inequality leaves the residual

    R(x, w) = C * D(x, w) - N * (1 + w^2 + (1/2 - x)^2),

which must be `>= 0` on `{0 < x < 1} cap {(w - a)^2 >= h^2}`.  The certificate is an EXACT
nonnegative combination over the generators

    g0 = x,   g1 = 1 - x,   g2 = (w - a)^2 - h^2,   p^2 (each parameter),   S^2 (declared squares)

    R = sum_alpha c_alpha * g0^i * g1^j * g2^k * prod (p^2)^e * prod (S^2)^m,   c_alpha >= 0.

It is found by the audit's route: shift to `y = w - a`, remove the odd-in-`y` part with a
nonnegative multiple of a declared square (the default square for a centre `a != 0` is
`(w - 2a)^2`, the hand hint `sq_nonneg (rho.im - 2 * s.im)` of `E6Bridge18.lean`), substitute
`y^2 -> h^2 + t`, and expand every `(t, parameter)`-coefficient in the Bernstein basis
`x^i (1-x)^(d-i)` of `[0, 1]` with degree elevation up to a cap (the Polya / Handelman form).
Verification is ONE exact `sympy.expand` equality -- no LP and no floating point.

The emitted strip proof states that identity as `key` and closes it by `ring` (so every
coefficient is load-bearing: corrupt one and `ring` fails), proves each summand `0 <= c * P`
by an explicit `mul_nonneg` term over the generator facts, and finishes with
`linarith only [key, t1, ..., tn]` -- the kernel re-derives nothing by search beyond summing the
listed facts.

ANTI-PHANTOM REFUSALS (the forge face; `zero_sum_majorant_certificate` refuses, never widens)
------------------------------------------------------------------------------------------
* `C < 0`, or `C` / `N` with a negative coefficient or an odd parameter power (then `positivity`
  cannot close `0 <= C` and the majorant is meaningless);
* the Polya / Bernstein check fails: a rational point of the domain with `R < 0` is reported and
  the claim named FALSE; otherwise the refusal is OBSTRUCTED (unproved, not refuted) with the
  elevation cap reached.  The audit's named phantom -- `h = 0` with a `1/|rho|^2` shape -- lands
  here: `|rho|` is not bounded below on the strip, located witness `Re rho` small, `Im rho = 0`;
* `h` not in `{0, 1, 2}` (the near set must be a BOUNDED ordinate window) and `window` other than
  `"ordinate"` (no finiteness lemma stands behind any other near set);
* `support` other than `"hypothesis_free"` (the support fact must be the
  `zeroMult_eq_zero_of_not_nontrivial` rewrite, never a conditional claim);
* a denominator outside the certified-positive list, and `den_kind = "ordinate_sq"` with `h = 0`
  (`D = (Im rho - a)^2` vanishes on the strip: no `Summable` claim survives a zero denominator);
* a supplied term list with a negative coefficient, a malformed exponent vector, or an expansion
  that is not EXACTLY the residual;
* tail faces: `P >= 0` (the envelope factor then does not decay with lam and the decoupling buys
  nothing; for `P > 0` the second conjunct is false), `E < 0`;
* floats anywhere (a float carries its binary expansion, not the rational you wrote), symbols in
  `C`, `N` or the centre that are not declared parameters, parameter / binder names that are not
  Lean identifiers or that collide with a name the emitted proofs bind, keys of the other mode.

WHAT IT DOES NOT DO
-------------------
It does not prove that the zero set is countable, that a window is finite, or that any particular
`f` has the claimed norm shape: those are the island's own lemmas (the prelude atom and the
instance's analysis) and enter the emitted theorems as named hypotheses or prelude calls.  It
says nothing about where the zeros are.  conjecture1_proved = False.
"""
from __future__ import annotations

import re
import textwrap
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import _poly_any_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .nonvacuity import assert_certificate_sensitive
from .workflow import Emitter

#: The two modes.  `zero_window` is audit C 3.1; `tail_envelope` is the consumer face of B N5.
MODES = ("zero_window", "tail_envelope")

#: Near radii the window-finiteness lemma covers (a bounded ordinate window).
ALLOWED_H = (0, 1, 2)

#: Denominator shapes with a certified positivity route on the strip.
DEN_KINDS = ("normSq", "ordinate_sq", "one_plus_ordinate_sq")

#: Faces of the `zero_window` mode, in emission order (each consumes the previous one).
ZERO_WINDOW_FACES = ("strip", "majorant", "summable")

#: Faces of the `tail_envelope` mode.
TAIL_FACES = ("envelope", "rate")

#: The only support fact and near set the kind accepts.
SUPPORT = "hypothesis_free"
WINDOW = "ordinate"

#: Bernstein degree-elevation cap for the `x` direction, and the certificate-length cap.
MAX_ELEVATION = 8
MAX_TERMS = 48

#: Lean spellings of the two zero coordinates; the sympy symbols carry these names so the
#: polynomial renderer prints straight into Lean source.
RE_NAME = "ρ.re"
IM_NAME = "ρ.im"

#: Island vocabulary the emitted `zero_window` faces reference (Zeta23 + E6Bridge4 + the P1
#: prelude RvMBridgeXi).  Fully qualified, so the emitted text depends on imports only.
LEAN_IS_ZERO = "Zeta23.IsNontrivialZero"
LEAN_GAMMA = "Zeta23.gammaOf"
LEAN_GAMMA_RE = "Zeta23.WeilEF.gammaOf_re"
LEAN_GAMMA_IM = "Zeta23.WeilEF.gammaOf_im"
LEAN_MULT = "WeilExplicit.zeroMult"
LEAN_BOUND = "RvMBridgeXi.zeroBoundAt"
LEAN_NORM_LE = "RvMBridgeXi.norm_le_zeroBoundAt"
LEAN_SUMMABLE = "RvMBridgeXi.summable_zeroBoundAt"

#: Lean modules the emitted `zero_window` theorems CALL but do not define.
PRELUDE_IMPORTS = ("RvMBridgeXi",)

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_LEAN_PATH = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")
#: Lean types a parameter binder may carry (the parameters are real projections of these).
_BINDER_TYPES = frozenset({"ℝ", "ℂ"})

#: Every name an emitted proof binds, plus Lean keywords a binder must not shadow.
_RESERVED = frozenset({
    "ρ", "f", "b", "K", "hK", "hzero", "hwin", "hshape", "hz", "him", "_him", "him'", "hw",
    "hre", "hre1", "hx0", "hu0", "ht0", "h2", "hg", "hn", "hden", "hγ", "key", "hm",
    "ι", "S", "w", "hw0", "hle", "hE", "hM", "hM0", "hsumM", "hsumN", "E", "x",
    "lam", "φ", "hlam", "hφ", "hl", "hP",
    "by", "fun", "have", "show", "from", "at", "in", "let", "do", "then", "else", "if",
    "match", "with", "theorem", "lemma", "def", "example", "calc", "rfl", "Real", "Complex",
    "Zeta23", "WeilExplicit", "RvMBridgeXi", "this",
    # bound to `rho.re` / `rho.im` when a declared square base is parsed (`_expr_w`)
    "re", "im",
})
_T_NAME = re.compile(r"^t[0-9]+$")


def _refuse(msg: str) -> ValueError:
    return ValueError(f"zero_sum_majorant REFUSED: {msg}")


# ---------------------------------------------------------------------------
# Symbols and exact coercions
# ---------------------------------------------------------------------------

def zsm_symbols(params: Sequence = ()) -> tuple[sp.Symbol, sp.Symbol, tuple[sp.Symbol, ...]]:
    """`(x, w, params)` as sympy symbols NAMED by their Lean spellings.

    `x` is `rho.re`, `w` is `rho.im`; each parameter is given as a Lean spelling (`"c"`,
    `"s.im"`) or an `(identifier, lean_spelling)` pair, and its symbol is named by the spelling,
    so every rendered polynomial is Lean source by construction."""
    x = sp.Symbol(RE_NAME, real=True)
    w = sp.Symbol(IM_NAME, real=True)
    return x, w, tuple(sp.Symbol(_param_lean(p), real=True) for p in params)


def _param_lean(p) -> str:
    return str(p[1]) if isinstance(p, (tuple, list)) else str(p)


def _param_ident(p) -> str:
    return str(p[0]) if isinstance(p, (tuple, list)) else str(p)


def _rational(v, what: str) -> sp.Rational:
    """Exactly-rational coercion; REFUSES bools, floats and non-rational values."""
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(
            f"{what} was given as a float ({v!r}); a float carries its binary expansion, not "
            "the rational you wrote -- pass a str/Fraction/sp.Rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    if isinstance(v, str):
        try:
            q = sp.sympify(v)
        except (sp.SympifyError, SyntaxError, TypeError) as exc:
            raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
        if q.atoms(sp.Float):
            raise _refuse(f"{what} = {v!r} is a float literal; write it as a fraction")
    else:
        try:
            q = sp.sympify(v)
        except (sp.SympifyError, TypeError) as exc:
            raise _refuse(f"{what} = {v!r} is not rational ({exc})") from None
    if not isinstance(q, sp.Rational):
        raise _refuse(f"{what} = {v!r} is not rational")
    return q


def _expr(v, what: str, pmap: dict, psyms: Sequence[sp.Symbol]) -> sp.Expr:
    """A polynomial in the declared parameters (or a rational); REFUSES floats and undeclared
    symbols.  Strings are parsed with the parameter identifiers bound to their symbols."""
    if isinstance(v, bool):
        raise _refuse(f"{what} was given as a bool ({v!r})")
    if isinstance(v, (float, sp.Float)):
        raise _refuse(
            f"{what} was given as a float ({v!r}); a float carries its binary expansion, not "
            "the rational you wrote -- pass a str/Fraction/sp.Rational")
    if isinstance(v, Fraction):
        return sp.Rational(v.numerator, v.denominator)
    if isinstance(v, str):
        try:
            e = sp.sympify(v, locals=dict(pmap))
        except (sp.SympifyError, SyntaxError, TypeError, AttributeError) as exc:
            raise _refuse(f"{what} = {v!r} does not parse ({exc})") from None
    elif isinstance(v, (int, sp.Basic)):
        e = sp.sympify(v)
    else:
        raise _refuse(f"{what} = {v!r} has unsupported type {type(v).__name__}")
    if e.atoms(sp.Float):
        raise _refuse(f"{what} = {v!r} contains a float literal; write it as a fraction")
    stray = sorted(str(s) for s in e.free_symbols if s not in set(psyms))
    if stray:
        raise _refuse(
            f"{what} = {e} uses {stray}, which are not declared parameters "
            f"{[str(p) for p in psyms]} (the zero coordinates may not appear in it)")
    e = sp.expand(e)
    if psyms:
        try:
            coeffs = sp.Poly(e, *psyms).coeffs()
        except sp.PolynomialError:
            raise _refuse(f"{what} = {e} is not a polynomial in the parameters") from None
        if not all(sp.sympify(c).is_Rational for c in coeffs):
            raise _refuse(f"{what} = {e} has a non-rational coefficient")
    elif not e.is_Rational:
        raise _refuse(f"{what} = {e} is not rational")
    return e


def _nonneg_class(e: sp.Expr, psyms: Sequence[sp.Symbol], what: str) -> None:
    """REFUSE unless every monomial of `e` (in the parameters) has a nonnegative coefficient and
    even exponents -- exactly the class `positivity` closes `0 <= e` on."""
    if not psyms:
        if sp.Rational(e) < 0:
            raise _refuse(f"{what} = {e} < 0 (the majorant would be meaningless)")
        return
    poly = sp.Poly(e, *psyms)
    for monom, coeff in zip(poly.monoms(), poly.coeffs()):
        c = sp.Rational(coeff)
        if c < 0:
            raise _refuse(
                f"{what} = {e} has a NEGATIVE coefficient {c} on {monom}; `positivity` cannot "
                "close 0 <= it, so the majorant is not certified nonnegative")
        if any(d % 2 for d in monom):
            raise _refuse(
                f"{what} = {e} has an ODD parameter power {monom}; the sign of a real "
                "parameter is unknown, so `positivity` cannot close 0 <= it")


# ---------------------------------------------------------------------------
# The certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ZeroSumMajorantCert:
    """One zero-sum majorant certificate.

    `terms` is the load-bearing datum of the `zero_window` mode: exponent vectors over the
    generator list `(x, 1 - x, (w - a)^2 - h^2, p^2..., S^2...)` paired with NONNEGATIVE rational
    coefficients whose expansion is EXACTLY `residual`.  The emitted strip proof states that
    identity and closes it by `ring`: corrupt one coefficient and the kernel rejects the file.
    """

    mode: str
    faces: tuple[str, ...]
    # --- zero_window ---
    centre: sp.Expr = sp.Integer(0)
    h: int = 1
    c_far: sp.Expr = sp.Integer(0)
    num: sp.Expr = sp.Integer(1)
    den_kind: str = "normSq"
    prefactor: bool = False
    params: tuple[tuple[str, str], ...] = ()     # (identifier, Lean spelling)
    binders: tuple[tuple[str, str], ...] = ()    # (name, Lean type)
    squares: tuple[sp.Expr, ...] = ()
    terms: tuple[tuple[tuple[int, ...], sp.Rational], ...] = ()
    residual: sp.Expr = sp.Integer(0)
    support: str = SUPPORT
    window: str = WINDOW
    # --- tail_envelope ---
    envelope_E: sp.Rational | None = None        # None with envelope_symbolic: E is a binder
    envelope_symbolic: bool = False
    rate_P: sp.Rational | None = None

    @property
    def param_symbols(self) -> tuple[sp.Symbol, ...]:
        return zsm_symbols(self.params)[2]

    @property
    def generators(self) -> tuple[sp.Expr, ...]:
        """The generator list the exponent vectors index, in order."""
        x, w, ps = zsm_symbols(self.params)
        return (x, 1 - x, (w - self.centre) ** 2 - self.h ** 2) + tuple(
            p ** 2 for p in ps) + tuple(s ** 2 for s in self.squares)

    def reconstruct(self) -> sp.Expr:
        """Expand the certificate back to a polynomial; equals `residual` by construction."""
        return _reconstruct(self.generators, self.terms)


def _reconstruct(gens, terms) -> sp.Expr:
    out = sp.Integer(0)
    for expo, coeff in terms:
        term = sp.Integer(1)
        for g, e in zip(gens, expo):
            if e:
                term *= g ** e
        out += sp.Rational(coeff) * term
    return sp.expand(out)


def _den_expr(den_kind: str, centre: sp.Expr) -> sp.Expr:
    x, w, _ = zsm_symbols()
    if den_kind == "normSq":
        return x ** 2 + w ** 2
    if den_kind == "ordinate_sq":
        return (w - centre) ** 2
    return 1 + (w - centre) ** 2


def _odd_part(e: sp.Expr, y: sp.Symbol) -> sp.Expr:
    return sp.expand((e - e.subs(y, -y)) / 2)


def _bernstein_weights(cx: sp.Expr, x: sp.Symbol, elevation_cap: int):
    """`(d, [w_0..w_d])` with `cx = sum_i w_i x^i (1-x)^(d-i)` and every `w_i >= 0`, or None.

    `w_i = sum_{j<=i} a_j C(d - j, i - j)` for `cx = sum_j a_j x^j` -- the exact monomial to
    Bernstein change of basis, with degree elevation until the coefficients turn nonnegative
    (the Polya / Handelman form on `[0, 1]`)."""
    poly = sp.Poly(sp.expand(cx), x)
    coeffs = [sp.Rational(c) for c in reversed(poly.all_coeffs())]  # a_0 .. a_deg
    deg = len(coeffs) - 1
    for d in range(deg, deg + elevation_cap + 1):
        weights = []
        for i in range(d + 1):
            wi = sp.Integer(0)
            for j in range(0, min(i, deg) + 1):
                wi += coeffs[j] * sp.binomial(d - j, i - j)
            weights.append(sp.Rational(wi))
        if all(wi >= 0 for wi in weights):
            return d, weights
    return None


def _sample_grid(h: int, psyms: Sequence[sp.Symbol]):
    """The exact rational sample grid `_locate_negative` walks (domain points only)."""
    xs = [sp.Rational(1, 1000), sp.Rational(1, 100), sp.Rational(1, 10), sp.Rational(1, 4),
          sp.Rational(1, 2), sp.Rational(3, 4), sp.Rational(9, 10), sp.Rational(99, 100),
          sp.Rational(999, 1000)]
    ys = [sp.Integer(0)] if h == 0 else []
    for k in (sp.Integer(0), sp.Rational(1, 2), sp.Integer(1), sp.Integer(3), sp.Integer(10)):
        ys += [h + k, -(h + k)]
    pvals = [sp.Integer(0), sp.Rational(1, 2), sp.Integer(-1), sp.Integer(1), sp.Integer(2),
             sp.Integer(-3)]
    if not psyms:
        psets = [{}]
    elif len(psyms) == 1:
        psets = [{psyms[0]: v} for v in pvals]
    else:  # a diagonal and an anti-diagonal sweep keep the grid small for several parameters
        psets = [{p: v for p in psyms} for v in pvals]
        psets += [{p: (v if i % 2 == 0 else -v) for i, p in enumerate(psyms)} for v in pvals]
    return xs, ys, psets


def _locate_negative(residual: sp.Expr, centre: sp.Expr, h: int, psyms: Sequence[sp.Symbol]):
    """An exact rational point of the domain with `residual < 0`, or None.

    The domain is `0 < x < 1` and `(w - a)^2 >= h^2`; at every sampled point both cleared
    denominators are positive, so a hit means the CLAIM IS FALSE, not merely unproved."""
    x, w, _ = zsm_symbols()
    xs, ys, psets = _sample_grid(h, psyms)
    for ps in psets:
        a_val = sp.expand(centre.subs(ps)) if ps else centre
        for yv in ys:
            for xv in xs:
                pt = dict(ps)
                pt[x] = xv
                pt[w] = sp.expand(yv + a_val)
                val = sp.expand(residual.subs(pt))
                if val.free_symbols:  # pragma: no cover -- every symbol is substituted
                    continue
                if sp.Rational(val) < 0:
                    return {str(k): v for k, v in pt.items()}, sp.Rational(val)
    return None


def _find_terms(residual: sp.Expr, centre: sp.Expr, h: int, psyms: Sequence[sp.Symbol],
                squares: Sequence[sp.Expr], elevation_cap: int):
    """The nonnegative-combination certificate, or raise ValueError (the caller refuses).

    Step 1 shifts to the ordinate variable `y = w - a`.  Step 2 removes the odd-in-`y` part with
    a nonnegative rational multiple of a declared square.  Step 3 applies the audit's
    substitution `y^2 -> h^2 + t`.  Step 4 expands each `(t, parameter)`-coefficient in the
    Bernstein basis on `0 <= x <= 1`."""
    x, w, _ = zsm_symbols()
    y = sp.Symbol("_zsm_y", real=True)
    t = sp.Symbol("_zsm_t", real=True)
    n_sq = len(squares)
    width = 3 + len(psyms) + n_sq

    ry = sp.expand(residual.subs(w, y + centre))
    mus = [sp.Integer(0)] * n_sq
    for idx, s_expr in enumerate(squares):
        odd = _odd_part(ry, y)
        if odd == 0:
            break
        sq_y = sp.expand(s_expr.subs(w, y + centre) ** 2)
        odd_s = _odd_part(sq_y, y)
        if odd_s == 0:
            continue
        ratio = sp.cancel(odd / odd_s)
        if not ratio.is_Rational or ratio < 0:
            continue
        mus[idx] = sp.Rational(ratio)
        ry = sp.expand(ry - mus[idx] * sq_y)

    leftover = _odd_part(ry, y)
    if leftover != 0:
        raise ValueError(
            f"the residual keeps an ODD power of the ordinate after the declared squares are "
            f"removed (leftover {leftover}); supply a square or the term list explicitly -- "
            "the emitter does not guess")

    poly_y = sp.Poly(ry, y)
    shifted = sp.Integer(0)
    for (deg,), coeff in poly_y.terms():
        shifted += coeff * (t + h ** 2) ** (deg // 2)
    shifted = sp.expand(shifted)

    out: list[tuple[tuple[int, ...], sp.Rational]] = []
    poly_tp = sp.Poly(shifted, t, *psyms)
    for monom, coeff in zip(poly_tp.monoms(), poly_tp.coeffs()):
        k, pexp = monom[0], monom[1:]
        if any(d % 2 for d in pexp):
            raise ValueError(
                f"the residual carries an ODD parameter power {pexp} on t^{k}; the sign of a "
                "real parameter is unknown, so no nonnegative-combination form exists")
        found = _bernstein_weights(sp.expand(coeff), x, elevation_cap)
        if found is None:
            raise ValueError(
                f"no nonnegative Bernstein form on 0 <= {RE_NAME} <= 1 for the coefficient "
                f"{sp.expand(coeff)} of t^{k} (parameter powers {list(pexp)}) up to elevation "
                f"{elevation_cap}")
        d, weights = found
        for i, wi in enumerate(weights):
            if wi == 0:
                continue
            expo = [0] * width
            expo[0], expo[1], expo[2] = i, d - i, k
            for pi, e in enumerate(pexp):
                expo[3 + pi] = e // 2
            out.append((tuple(expo), sp.Rational(wi)))
    for idx, mu in enumerate(mus):
        if mu == 0:
            continue
        expo = [0] * width
        expo[3 + len(psyms) + idx] = 1
        out.append((tuple(expo), sp.Rational(mu)))
    out.sort(key=lambda it: (it[0], it[1].p, it[1].q))
    return tuple(out)


def _check_name(n: str, what: str, pattern=_IDENT) -> None:
    if not isinstance(n, str) or not pattern.match(n):
        raise _refuse(f"{what} {n!r} is not a Lean identifier")
    if n in _RESERVED or _T_NAME.match(n):
        raise _refuse(
            f"{what} {n!r} collides with a name the emitted proofs bind (or a Lean keyword / "
            "vocabulary head); rename it rather than shadow the proof")


def _check_params_binders(params, binders) -> tuple[tuple[tuple[str, str], ...],
                                                    tuple[tuple[str, str], ...]]:
    ps: list[tuple[str, str]] = []
    for p in params:
        ident, lean = _param_ident(p), _param_lean(p)
        _check_name(ident, "parameter identifier")
        if not _LEAN_PATH.match(lean):
            raise _refuse(f"parameter spelling {lean!r} is not a Lean identifier path")
        if lean.split(".")[0] in _RESERVED:
            raise _refuse(f"parameter spelling {lean!r} starts with a name the proofs bind")
        ps.append((ident, lean))
    if len({i for i, _ in ps}) != len(ps) or len({s for _, s in ps}) != len(ps):
        raise _refuse(f"duplicate parameter in {ps}")
    bs: list[tuple[str, str]] = []
    for b in binders:
        if not isinstance(b, (tuple, list)) or len(b) != 2:
            raise _refuse(f"binder {b!r} must be a (name, Lean type) pair")
        n, ty = str(b[0]), str(b[1])
        _check_name(n, "binder name")
        if ty not in _BINDER_TYPES:
            raise _refuse(f"binder {n!r} has type {ty!r}; only {sorted(_BINDER_TYPES)} are allowed")
        bs.append((n, ty))
    if len({n for n, _ in bs}) != len(bs):
        raise _refuse(f"duplicate binder in {bs}")
    heads = {n for n, _ in bs}
    for _, lean in ps:
        if lean.split(".")[0] not in heads:
            raise _refuse(
                f"parameter {lean!r} is not bound: declare its head as a binder, e.g. "
                f"binders=[({lean.split('.')[0]!r}, 'ℝ' or 'ℂ')]")
    return tuple(ps), tuple(bs)


def zero_sum_majorant_certificate(
    *,
    mode: str = "zero_window",
    centre=0,
    h=1,
    c_far=None,
    num=1,
    den_kind: str = "normSq",
    prefactor: bool = False,
    params: Sequence = (),
    binders: Sequence = (),
    squares=None,
    terms=None,
    support: str = SUPPORT,
    window: str = WINDOW,
    faces: Sequence[str] | None = None,
    elevation_cap: int = MAX_ELEVATION,
    envelope_E=None,
    rate_P=None,
) -> ZeroSumMajorantCert:
    """Build (and EXACTLY re-check) a zero-sum majorant certificate.

    See the module docstring for the statement family and the full refusal list.  Nothing is
    widened: a claim the exact nonnegative-combination check does not reach is REFUSED, with a
    located rational counterexample when the claim is outright FALSE."""
    if mode not in MODES:
        raise _refuse(f"unknown mode {mode!r} (expected one of {MODES})")

    if mode == "tail_envelope":
        stray = [k for k, v in (("c_far", c_far), ("terms", terms), ("squares", squares))
                 if v is not None]
        stray += [k for k, v, dflt in (("centre", centre, 0), ("h", h, 1), ("num", num, 1),
                                       ("den_kind", den_kind, "normSq"),
                                       ("prefactor", prefactor, False))
                  if not (v is dflt or v == dflt)]
        stray += [k for k, v in (("params", params), ("binders", binders)) if tuple(v)]
        if stray:
            raise _refuse(f"zero_window key(s) {stray} given in tail_envelope mode")
        if envelope_E is None:
            raise _refuse("tail_envelope mode needs envelope_E (a rational E >= 0, or 'symbolic')")
        symbolic = isinstance(envelope_E, str) and envelope_E.strip() == "symbolic"
        E = None
        if not symbolic:
            E = _rational(envelope_E, "envelope_E")
            if E < 0:
                raise _refuse(f"tail_envelope needs E >= 0, got E = {E}")
        P = None
        if rate_P is not None:
            P = _rational(rate_P, "rate_P")
            if P >= 0:
                raise _refuse(
                    f"the rate-splitting companion needs P < 0, got P = {P}; at P >= 0 the "
                    "factor exp(2 (lam - 1) P) does not decay with lam (for P > 0 it GROWS) and "
                    "the decoupling buys nothing")
        fs = tuple(faces) if faces is not None else (
            ("envelope", "rate") if P is not None else ("envelope",))
        if not fs:
            raise _refuse("no faces requested")
        for f in fs:
            if f not in TAIL_FACES:
                raise _refuse(f"unknown tail_envelope face {f!r} (expected {TAIL_FACES})")
        if len(set(fs)) != len(fs):
            raise _refuse(f"duplicate face in {fs}")
        if "rate" in fs and P is None:
            raise _refuse("face 'rate' requires a rational rate_P < 0")
        if P is not None and "rate" not in fs:
            raise _refuse("rate_P given but face 'rate' not requested")
        fs = tuple(f for f in TAIL_FACES if f in fs)
        return ZeroSumMajorantCert(mode=mode, faces=fs, envelope_E=E,
                                   envelope_symbolic=symbolic, rate_P=P)

    # --- zero_window ---
    if envelope_E is not None or rate_P is not None:
        raise _refuse("tail_envelope key(s) envelope_E / rate_P given in zero_window mode")
    if support != SUPPORT:
        raise _refuse(
            f"support = {support!r}; the support fact must be the hypothesis-free "
            "`zeroMult_eq_zero_of_not_nontrivial` rewrite, never a conditional claim")
    if window != WINDOW:
        raise _refuse(
            f"window = {window!r}; the near set must be a bounded ORDINATE window -- its "
            "finiteness comes only from `zetaSeam.finite_window`")
    if isinstance(h, bool) or not isinstance(h, int) or h not in ALLOWED_H:
        raise _refuse(f"near radius h = {h!r} is not one of {ALLOWED_H}")
    if den_kind not in DEN_KINDS:
        raise _refuse(f"unknown den_kind {den_kind!r} (expected one of {DEN_KINDS})")
    if den_kind == "ordinate_sq" and h == 0:
        raise _refuse(
            "den_kind 'ordinate_sq' with h = 0: the denominator (Im rho - a)^2 is not bounded "
            "away from 0 on the zeros, so no Summable claim survives (a phantom)")
    if not isinstance(prefactor, bool):
        raise _refuse(f"prefactor must be a bool, got {prefactor!r}")
    if isinstance(elevation_cap, bool) or not isinstance(elevation_cap, int) or not (
            0 <= elevation_cap <= 32):
        raise _refuse(f"elevation_cap = {elevation_cap!r} must be an int in [0, 32]")
    fs = tuple(faces) if faces is not None else ZERO_WINDOW_FACES
    if not fs:
        raise _refuse("no faces requested")
    for f in fs:
        if f not in ZERO_WINDOW_FACES:
            raise _refuse(f"unknown face {f!r} (expected {ZERO_WINDOW_FACES})")
    if len(set(fs)) != len(fs):
        raise _refuse(f"duplicate face in {fs}")
    if "summable" in fs and "majorant" not in fs:
        raise _refuse("face 'summable' consumes 'majorant'; emit both or neither")
    if "majorant" in fs and "strip" not in fs:
        raise _refuse("face 'majorant' consumes 'strip'; emit both or neither")
    fs = tuple(f for f in ZERO_WINDOW_FACES if f in fs)

    ps, bs = _check_params_binders(params, binders)
    x, w, psyms = zsm_symbols(ps)
    pmap = {ident: sym for (ident, _), sym in zip(ps, psyms)}
    a = _expr(centre, "centre", pmap, psyms)
    if c_far is None:
        raise _refuse("c_far is required in zero_window mode")
    C = _expr(c_far, "c_far", pmap, psyms)
    N = _expr(num, "num", pmap, psyms)
    _nonneg_class(C, psyms, "c_far")
    _nonneg_class(N, psyms, "num")
    if N == 0:
        raise _refuse("num = 0: the family is identically zero, nothing to certify")

    den = _den_expr(den_kind, a)
    G = 1 + w ** 2 + (sp.Rational(1, 2) - x) ** 2
    residual = sp.expand(C * den - N * G)

    if squares is None:
        sq = [sp.expand(w - 2 * a)] if a != 0 else []
    else:
        sq = [_expr_w(s, pmap, psyms) for s in squares]

    if terms is None:
        try:
            terms_t = _find_terms(residual, a, h, psyms, sq, elevation_cap)
        except ValueError as exc:
            hit = _locate_negative(residual, a, h, psyms)
            if hit is not None:
                pt, val = hit
                raise _refuse(
                    f"the strip inequality is FALSE: at the domain point {pt} the cleared "
                    f"residual C*D - N*(1 + |gamma|^2) is {val} < 0.  ({exc})") from None
            raise _refuse(
                f"OBSTRUCTED: no nonnegative-combination certificate up to elevation "
                f"{elevation_cap}, and no rational counterexample on the sample grid, so the "
                f"claim is unproved rather than refuted.  ({exc})") from None
    else:
        terms_t = _coerce_terms(terms)

    width = 3 + len(psyms) + len(sq)
    if not terms_t:
        raise _refuse("empty certificate: the residual is never identically zero here")
    if len(terms_t) > MAX_TERMS:
        raise _refuse(f"certificate has {len(terms_t)} terms, above the cap {MAX_TERMS}")
    for expo, coeff in terms_t:
        if len(expo) != width:
            raise _refuse(
                f"term exponent vector {expo} has length {len(expo)}, expected {width} "
                f"(x, 1-x, t, {len(psyms)} parameter squares, {len(sq)} extra squares)")
        if any(e < 0 for e in expo):
            raise _refuse(f"term exponent vector {expo} has a negative exponent")
        if coeff < 0:
            raise _refuse(
                f"term {expo} carries a NEGATIVE coefficient {coeff}; a nonnegative "
                "combination is the whole certificate")
        if coeff == 0:
            raise _refuse(f"term {expo} carries a zero coefficient; drop it")

    cert = ZeroSumMajorantCert(
        mode=mode, faces=fs, centre=a, h=h, c_far=C, num=N, den_kind=den_kind,
        prefactor=prefactor, params=ps, binders=bs, squares=tuple(sq), terms=terms_t,
        residual=residual,
    )
    gap = sp.expand(cert.reconstruct() - residual)
    if gap != 0:
        hit = _locate_negative(residual, a, h, psyms)
        extra = ""
        if hit is not None:
            pt, val = hit
            extra = f"  The claim is also FALSE: residual = {val} < 0 at {pt}."
        raise _refuse(
            f"the supplied term list does NOT expand to the cleared residual (difference "
            f"{gap}); the certificate is the identity, so a mismatched term list ships "
            f"nothing.{extra}")
    # the identity must DEPEND on the certificate (the X = X class is refused here)
    _check_sensitive(cert)
    return cert


def _expr_w(s, pmap, psyms) -> sp.Expr:
    """A declared extra square base: a polynomial in `rho.im`, `rho.re` and the parameters."""
    x, w, _ = zsm_symbols()
    loc = dict(pmap)
    loc.update({"re": x, "im": w})
    if isinstance(s, (float, sp.Float)):
        raise _refuse(f"square base {s!r} is a float")
    try:
        e = sp.sympify(s, locals=loc) if isinstance(s, str) else sp.sympify(s)
    except (sp.SympifyError, SyntaxError, TypeError) as exc:
        raise _refuse(f"square base {s!r} does not parse ({exc})") from None
    if e.atoms(sp.Float):
        raise _refuse(f"square base {s!r} contains a float literal")
    stray = sorted(str(v) for v in e.free_symbols if v not in {x, w} | set(psyms))
    if stray:
        raise _refuse(f"square base {e} uses undeclared symbols {stray}")
    return sp.expand(e)


def _coerce_terms(terms) -> tuple[tuple[tuple[int, ...], sp.Rational], ...]:
    out = []
    for item in terms:
        try:
            expo, c = item
        except (TypeError, ValueError):
            raise _refuse(f"term {item!r} must be an (exponent vector, coefficient) pair") from None
        ex = []
        for e in expo:
            if isinstance(e, bool) or not isinstance(e, int):
                raise _refuse(f"term exponent {e!r} in {expo!r} is not an int")
            ex.append(int(e))
        out.append((tuple(ex), _rational(c, f"coefficient of term {tuple(ex)}")))
    return tuple(out)


def _check_sensitive(cert: ZeroSumMajorantCert) -> None:
    """Wire `nonvacuity.assert_certificate_sensitive`: the emitted identity `key` must break
    when any coefficient is corrupted (or a term dropped)."""
    gens = cert.generators

    def claim(ts):
        return _reconstruct(gens, ts) - cert.residual

    perturbations = []
    for i in range(len(cert.terms)):
        perturbations.append(
            lambda ts, i=i: tuple((e, c + 1) if j == i else (e, c) for j, (e, c) in enumerate(ts)))
    perturbations.append(lambda ts: ts[1:])
    assert_certificate_sensitive(claim, cert.terms, perturbations,
                                 label="zero_sum_majorant strip identity")


def certify_zero_sum_majorant_point(family, pt, name):
    """Certify one zero-sum majorant point: `(CertifiedInstance, n_checks)`.

    Reads the spec dict from `family.special[1](pt)` (the keyword arguments of
    :func:`zero_sum_majorant_certificate`) and re-checks it, raising on every dishonest claim."""
    spec = dict(family.special[1](pt))
    cert = zero_sum_majorant_certificate(**spec)
    n_checks = 1 + len(cert.terms) if cert.mode == "zero_window" else len(cert.faces)
    return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), n_checks


# ---------------------------------------------------------------------------
# Lean rendering
# ---------------------------------------------------------------------------

_ATOMIC = re.compile(r"^[A-Za-z0-9_.'ρ]+$")


def _is_atomic(s: str) -> bool:
    """True when `s` needs no extra parentheses: an identifier path / numeral, or wrapped."""
    if _ATOMIC.match(s):
        return True
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    return False
        return depth == 0
    return False


def _paren(s: str) -> str:
    return s if _is_atomic(s) else f"({s})"


def _lean_poly(e: sp.Expr, cert: ZeroSumMajorantCert) -> str:
    """A polynomial in the zero coordinates and the parameters, rendered monomial-wise (never
    `together`d into one quotient), so `13/4 + 2 s.im^2` prints as the island spells it."""
    x, w, ps = zsm_symbols(cert.params)
    return _poly_any_lean(sp.expand(e), (x, w) + ps)


class _Spell:
    """Every Lean spelling one `zero_window` instance needs, computed once."""

    def __init__(self, cert: ZeroSumMajorantCert):
        self.cert = cert
        a_s = _lean_poly(cert.centre, cert)
        self.centre_arg = _paren(a_s)
        self.ord = IM_NAME if cert.centre == 0 else f"{IM_NAME} - {_paren(a_s)}"
        self.ord_abs = f"|{self.ord}|"
        self.ord_sq = f"{_paren(self.ord)} ^ 2"
        hh = cert.h * cert.h
        self.t_gen = f"{self.ord_sq} - {hh}" if cert.h else self.ord_sq
        self.h = str(cert.h)
        self.c = _paren(_lean_poly(cert.c_far, cert))
        self.n = _paren(_lean_poly(cert.num, cert))
        if cert.den_kind == "normSq":
            self.den_stmt = "Complex.normSq ρ"
            self.den_unf = f"({RE_NAME} ^ 2 + {IM_NAME} ^ 2)"
        elif cert.den_kind == "ordinate_sq":
            self.den_stmt = self.ord_sq
            self.den_unf = self.ord_sq
        else:
            self.den_stmt = f"(1 + {self.ord_sq})"
            self.den_unf = self.den_stmt
        self.ratio = f"{self.n} / {self.den_stmt}"
        self.shape = f"(K * ({self.ratio}))" if cert.prefactor else f"({self.ratio})"
        self.const = f"(K * {self.c})" if cert.prefactor else self.c
        self.gamma_sq = f"(1 + ({IM_NAME} ^ 2 + (1 / 2 - {RE_NAME}) ^ 2))"
        self.binders = "".join(f" ({n} : {ty})" for n, ty in cert.binders)
        self.args = "".join(f" {n}" for n, _ in cert.binders)


def _top_level_sum(s: str) -> bool:
    """True when `s` has a `+` / `-` operator at parenthesis depth 0 (so it needs parentheses
    to stand as a factor or as the base of a power)."""
    depth = 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and ch in "+-" and 0 < i < len(s) - 1 and s[i - 1] == " " \
                and s[i + 1] == " ":
            return True
    return False


def _factor(expo: tuple[int, ...], cert: ZeroSumMajorantCert, sp_: _Spell):
    """`(factor strings, nonnegativity proofs)` of one certificate monomial, left to right.

    Each factor is a generator power `g ^ e`; its proof is the generator fact (`hx0`, `hu0`,
    `ht0`, `sq_nonneg _`) or `pow_nonneg <fact> e`.  The factor strings are exactly the types
    those proof terms elaborate to, so the emitted `mul_nonneg` chain needs no unification."""
    fs: list[str] = []
    prs: list[str] = []

    def push(base: str, proof: str, e: int):
        if e == 1:
            fs.append(f"({base})" if _top_level_sum(base) else base)
            prs.append(proof)
        else:
            b = base if _is_atomic(base) else f"({base})"
            fs.append(f"{b} ^ {e}")
            prs.append(f"(pow_nonneg {proof} {e})")

    if expo[0]:
        push(RE_NAME, "hx0", expo[0])
    if expo[1]:
        push(f"1 - {RE_NAME}", "hu0", expo[1])
    if expo[2]:
        push(sp_.t_gen, "ht0", expo[2])
    ps = cert.param_symbols
    for i, p in enumerate(ps):
        e = expo[3 + i]
        if e:
            pl = _paren(str(p))
            push(f"{pl} ^ 2", f"(sq_nonneg {pl})", e)
    for j, s_expr in enumerate(cert.squares):
        e = expo[3 + len(ps) + j]
        if e:
            sl = _paren(_lean_poly(s_expr, cert))
            push(f"{sl} ^ 2", f"(sq_nonneg {sl})", e)
    return fs, prs


def _term(expo, coeff, cert: ZeroSumMajorantCert, sp_: _Spell) -> tuple[str, str]:
    """`(term string c * P, proof of 0 <= c * P)`; the coefficient `c >= 0` is re-checked by
    `norm_num` in the kernel."""
    c = rat_lean(coeff)
    fs, prs = _factor(expo, cert, sp_)
    if not fs:
        return c, "by norm_num"
    if len(fs) == 1:
        return f"{c} * {fs[0]}", f"mul_nonneg (by norm_num) {_paren(prs[0])}"
    proof = prs[0]
    for pr in prs[1:]:
        proof = f"mul_nonneg {_paren(proof)} {_paren(pr)}"
    return f"{c} * ({' * '.join(fs)})", f"mul_nonneg (by norm_num) ({proof})"


def _wrap(items: Sequence[str], indent: str, sep: str, width: int = 96) -> str:
    """Join `items` with `sep` onto as few lines as fit inside `width` columns (the separator
    ends a line; the continuation is indented by `indent`)."""
    lines: list[str] = []
    cur = ""
    for i, it in enumerate(items):
        piece = it + (sep.rstrip() if i < len(items) - 1 else "")
        cand = piece if not cur else f"{cur} {piece}"
        if cur and len(indent) + len(cand) > width:
            lines.append(cur)
            cur = piece
        else:
            cur = cand
    if cur:
        lines.append(cur)
    return ("\n" + indent).join(lines)


def _doc(text: str) -> str:
    """A Lean doc comment: `text` word-wrapped at 96 columns (deterministic `textwrap`), the
    continuation lines indented by four spaces."""
    lines = textwrap.wrap(" ".join(text.split()), width=92, break_long_words=False,
                          break_on_hyphens=False)
    return "/-- " + "\n    ".join(lines) + " -/\n"


def _strip_doc(cert: ZeroSumMajorantCert, name: str, sp_: _Spell) -> str:
    den_word = {"normSq": "normSq rho", "ordinate_sq": "(Im rho - a)^2",
                "one_plus_ordinate_sq": "1 + (Im rho - a)^2"}[cert.den_kind]
    gens = "`Re rho`, `1 - Re rho`, `" + sp_.t_gen + "`"
    if cert.params:
        gens += ", the parameter squares"
    if cert.squares:
        gens += ", the declared squares " + ", ".join(
            f"`({_lean_poly(s, cert)}) ^ 2`" for s in cert.squares)
    return _doc(
        f"`{name}` -- zero_sum_majorant, the per-instance certificate (the strip inequality): on a "
        f"nontrivial zero with `{sp_.h} <= {sp_.ord_abs}`, `N / D <= C / (1 + |gamma_rho|^2)` with "
        f"`N = {_lean_poly(cert.num, cert)}`, `D = {den_word}`, "
        f"`C = {_lean_poly(cert.c_far, cert)}`.  Cleared, `C * D - N * (1 + |gamma_rho|^2)` is the "
        f"EXACT nonnegative combination `key` ({len(cert.terms)} term(s)) of the generators "
        f"{gens} -- the Bernstein / Polya form on the strip after `w^2 -> h^2 + t` -- checked by "
        f"`ring`, each summand nonnegative by an explicit `mul_nonneg` term.  A strip inequality: "
        f"nothing about WHERE the zeros are.  conjecture1_proved = False.")


def _strip_theorem(cert: ZeroSumMajorantCert, name: str) -> str:
    sp_ = _Spell(cert)
    him = "him" if cert.h else "_him"
    lines = [
        f"theorem {name}{sp_.binders} {{ρ : ℂ}} (hz : {LEAN_IS_ZERO} ρ)",
        f"    ({him} : ({sp_.h} : ℝ) ≤ {sp_.ord_abs}) :",
        f"    {sp_.ratio} ≤ {sp_.c} / (1 + Complex.normSq ({LEAN_GAMMA} ρ)) := by",
        f"  have hre : (0 : ℝ) < {RE_NAME} := hz.2.1",
        f"  have hre1 : {RE_NAME} < 1 := hz.2.2",
        f"  have hx0 : (0 : ℝ) ≤ {RE_NAME} := hre.le",
        f"  have hu0 : (0 : ℝ) ≤ 1 - {RE_NAME} := by linarith",
    ]
    if cert.h:
        lines += [
            f"  have ht0 : (0 : ℝ) ≤ {sp_.t_gen} := by",
            f"    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ {sp_.h}) him 2",
            f"    rw [sq_abs] at h2",
            f"    linarith",
        ]
    else:
        lines.append(f"  have ht0 : (0 : ℝ) ≤ {sp_.t_gen} := sq_nonneg _")
    lines += [
        f"  have hg : Complex.normSq ({LEAN_GAMMA} ρ) = {IM_NAME} ^ 2 + (1 / 2 - {RE_NAME}) ^ 2 := by",
        f"    rw [Complex.normSq_apply, {LEAN_GAMMA_RE}, {LEAN_GAMMA_IM}]",
        f"    ring",
    ]
    rws = []
    if cert.den_kind == "normSq":
        lines += [
            f"  have hn : Complex.normSq ρ = {RE_NAME} ^ 2 + {IM_NAME} ^ 2 := by",
            f"    rw [Complex.normSq_apply]",
            f"    ring",
            f"  have hden : (0 : ℝ) < {sp_.den_unf} :=",
            f"    add_pos_of_pos_of_nonneg (pow_pos hre 2) (sq_nonneg _)",
        ]
        rws.append("hn")
    elif cert.den_kind == "ordinate_sq":
        lines.append(f"  have hden : (0 : ℝ) < {sp_.den_unf} := by linarith")
    else:
        lines.append(f"  have hden : (0 : ℝ) < {sp_.den_unf} := by positivity")
    lines += [
        f"  have hγ : (0 : ℝ) < {sp_.gamma_sq} := by positivity",
        f"  rw [{', '.join(rws + ['hg', 'div_le_div_iff₀ hden hγ'])}]",
    ]
    rendered = [_term(e, c, cert, sp_) for e, c in cert.terms]
    rhs = _wrap([t for t, _ in rendered], "        ", " +")
    lhs = f"  have key : {sp_.c} * {sp_.den_unf} - {sp_.n} * {sp_.gamma_sq}"
    if len(lhs) > 100:
        lhs = f"  have key : {sp_.c} * {sp_.den_unf}\n      - {sp_.n} * {sp_.gamma_sq}"
    lines += [
        lhs,
        f"      = {rhs} := by",
        f"    ring",
    ]
    names = []
    for i, (t, pr) in enumerate(rendered, start=1):
        one = f"  have t{i} : (0 : ℝ) ≤ {t} := {pr}"
        if len(one) > 100:
            one = f"  have t{i} : (0 : ℝ) ≤ {t} :=\n    {pr}"
        lines.append(one)
        names.append(f"t{i}")
    lines.append(f"  linarith only [{_wrap(['key'] + names, '    ', ',')}]")
    return "\n".join(lines) + "\n"


def _le_theorem(cert: ZeroSumMajorantCert, nm: str) -> str:
    sp_ = _Spell(cert)
    kb = " {K : ℝ} (hK : 0 ≤ K)" if cert.prefactor else ""
    hC = "(mul_nonneg hK (by positivity))" if cert.prefactor else "(by positivity)"
    centred = cert.centre != 0
    far = "(fun ρ hz _ => ?_)" if cert.h == 0 else "(fun ρ hz him => ?_)"
    if centred:
        body = [f"  refine {LEAN_NORM_LE} hzero hwin {far}",
                f"    {hC} ρ"]
    else:
        body = [f"  refine {LEAN_NORM_LE} hzero",
                f"    (fun ρ hz hw => hwin ρ hz (by simpa using hw)) {far}",
                f"    {hC} ρ"]
    if cert.h == 0:
        hname = "(abs_nonneg _)"
    elif centred:
        hname = "him"
    else:
        body.append(f"  have him' : ({sp_.h} : ℝ) ≤ {sp_.ord_abs} := by simpa using him")
        hname = "him'"
    body += [
        f"  refine (hshape ρ hz {hname}).trans ?_",
        f"  have hm : (0 : ℝ) ≤ ({LEAN_MULT} ρ : ℝ) := Nat.cast_nonneg _",
        f"  refine mul_le_mul_of_nonneg_left ?_ hm",
    ]
    call = f"{nm}_strip{sp_.args} hz {hname}"
    if cert.prefactor:
        body += [
            f"  rw [mul_div_assoc]",
            f"  exact mul_le_mul_of_nonneg_left ({call}) hK",
        ]
    else:
        body.append(f"  exact {call}")
    doc = _doc(
        f"`{nm}_le` -- the zero-sum majorant: a family vanishing off the nontrivial zeros, bounded "
        f"by `b` on the finite ordinate window `{sp_.ord_abs} < {sp_.h}` and by "
        f"`m(rho) * {sp_.shape}` off it, is bounded pointwise by the island atom "
        f"`RvMBridgeXi.zeroBoundAt` (the window indicator plus the local-count tail "
        f"`m(rho) C/(1 + |gamma_rho|^2)`), through the certified `{nm}_strip`.  "
        f"conjecture1_proved = False.")
    return (
        doc +
        f"theorem {nm}_le{sp_.binders} {{f : ℂ → ℂ}} {{b : ℂ → ℝ}}{kb}\n"
        f"    (hzero : ∀ ρ, ¬ {LEAN_IS_ZERO} ρ → f ρ = 0)\n"
        f"    (hwin : ∀ ρ, {LEAN_IS_ZERO} ρ → {sp_.ord_abs} < ({sp_.h} : ℝ) → ‖f ρ‖ ≤ b ρ)\n"
        f"    (hshape : ∀ ρ, {LEAN_IS_ZERO} ρ → ({sp_.h} : ℝ) ≤ {sp_.ord_abs} →\n"
        f"      ‖f ρ‖ ≤ ({LEAN_MULT} ρ : ℝ) * {sp_.shape})\n"
        f"    (ρ : ℂ) :\n"
        f"    ‖f ρ‖ ≤ {LEAN_BOUND} {sp_.centre_arg} {sp_.h} {sp_.const} b ρ := by\n"
        + "\n".join(body) + "\n"
    )


def _summable_theorem(cert: ZeroSumMajorantCert, nm: str) -> str:
    sp_ = _Spell(cert)
    kb = " {K : ℝ} (hK : 0 ≤ K)" if cert.prefactor else ""
    ka = " hK" if cert.prefactor else ""
    doc = _doc(
        f"`{nm}_summable` -- `Summable f` from `{nm}_le` with `b := ‖f‖` on the window (finite by "
        f"`zetaSeam.finite_window`) and the tail summed by `summable_mult_div_one_add_normSq` "
        f"(`RvMBridgeXi.summable_zeroBoundAt`).  conjecture1_proved = False.")
    return (
        doc +
        f"theorem {nm}_summable{sp_.binders} {{f : ℂ → ℂ}}{kb}\n"
        f"    (hzero : ∀ ρ, ¬ {LEAN_IS_ZERO} ρ → f ρ = 0)\n"
        f"    (hshape : ∀ ρ, {LEAN_IS_ZERO} ρ → ({sp_.h} : ℝ) ≤ {sp_.ord_abs} →\n"
        f"      ‖f ρ‖ ≤ ({LEAN_MULT} ρ : ℝ) * {sp_.shape}) :\n"
        f"    Summable f :=\n"
        f"  Summable.of_norm_bounded\n"
        f"    ({LEAN_SUMMABLE} {sp_.centre_arg} {sp_.h} {sp_.const} (fun ρ => ‖f ρ‖))\n"
        f"    ({nm}_le{sp_.args} (b := fun ρ => ‖f ρ‖){ka} hzero (fun _ _ _ => le_rfl) hshape)\n"
    )


def _envelope_theorem(cert: ZeroSumMajorantCert, nm: str) -> str:
    if cert.envelope_symbolic:
        E, eb, he = "E", " {E : ℝ} (hE : 0 ≤ E)", ""
        what = "a symbolic `E` with `0 <= E` as a hypothesis (the prelude's own statement)"
    else:
        E = rat_lean(cert.envelope_E)
        eb, he = "", f"  have hE : (0 : ℝ) ≤ {E} := by norm_num\n"
        what = f"the rational `E = {E}`, its sign re-checked by `norm_num`"
    doc = _doc(
        f"`{nm}_envelope` -- the tail-envelope face (audit B N5): a family bounded on `S` by `E` "
        f"times a nonnegative summable weight has its subtype sum bounded by `E` times the WHOLE "
        f"weight sum; {what}.  The audit's skeleton `norm_tsum_le_tsum_norm` + `tsum_le_tsum` + "
        f"`tsum_subtype_le` + `tsum_mul_left`, Mathlib only.  conjecture1_proved = False.")
    return (
        doc +
        f"theorem {nm}_envelope {{ι : Type*}} {{f : ι → ℂ}} {{w : ι → ℝ}} (S : Set ι){eb}\n"
        f"    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ {E} * w x) :\n"
        f"    ‖∑' x : S, f x‖ ≤ {E} * ∑' x : ι, w x := by\n"
        + he +
        f"  have hM : Summable (fun x => {E} * w x) := hw.mul_left {E}\n"
        f"  have hM0 : ∀ x, 0 ≤ {E} * w x := fun x => mul_nonneg hE (hw0 x)\n"
        f"  have hsumM : Summable (fun x : S => {E} * w x) := hM.subtype S\n"
        f"  have hsumN : Summable (fun x : S => ‖f x‖) :=\n"
        f"    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsumM\n"
        f"  calc ‖∑' x : S, f x‖\n"
        f"      ≤ ∑' x : S, ‖f x‖ := norm_tsum_le_tsum_norm hsumN\n"
        f"    _ ≤ ∑' x : S, {E} * w x := hsumN.tsum_le_tsum hle hsumM\n"
        f"    _ ≤ ∑' x : ι, {E} * w x := hM.tsum_subtype_le _ _ hM0\n"
        f"    _ = {E} * ∑' x : ι, w x := tsum_mul_left\n"
    )


def _rate_theorem(cert: ZeroSumMajorantCert, nm: str) -> str:
    P = rat_lean(cert.rate_P)
    doc = _doc(
        f"`{nm}_rate` -- the rate-splitting companion at the rational `P = {P} < 0`: for "
        f"`1 <= lam` and `phi <= P` the lam-dependence decouples from the summand, AND the envelope "
        f"factor `exp (2 (lam - 1) P)` is at most 1 (what `P < 0` buys; FALSE for every `P > 0` at "
        f"lam = 2, so a forged sign cannot compile).  conjecture1_proved = False.")
    return (
        doc +
        f"theorem {nm}_rate {{lam φ : ℝ}} (hlam : 1 ≤ lam) (hφ : φ ≤ {P}) :\n"
        f"    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * {P}) * Real.exp (2 * φ)\n"
        f"      ∧ Real.exp (2 * (lam - 1) * {P}) ≤ 1 := by\n"
        f"  have hl : (0 : ℝ) ≤ lam - 1 := sub_nonneg.mpr hlam\n"
        f"  refine ⟨?_, ?_⟩\n"
        f"  · rw [← Real.exp_add]\n"
        f"    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hφ hl])\n"
        f"  · rw [Real.exp_le_one_iff]\n"
        f"    have hP : ({P} : ℝ) ≤ 0 := by norm_num\n"
        f"    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hl) hP\n"
    )


@dataclass
class ZeroSumMajorantEmitter(Emitter):
    """Emit the zero-sum majorant shape: the certified strip inequality, the `zeroBoundAt`
    composite and the `Summable` corollary (and, in `tail_envelope` mode, the consumer envelope
    and the rate-splitting companion).  No search beyond `linarith only` over the emitted
    certificate facts, no `decide`; the Lean kernel is the arbiter.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "zero_sum_majorant"
        # The window / local-count atom lives ONCE on the island (the P1 prelude); the emitted
        # Lean calls it and must not silently ship without an import that could carry it.
        self.requires_prelude = (LEAN_BOUND,)

    def _emit_strip(self, cert: ZeroSumMajorantCert, name: str) -> str:
        """The strip face alone, under EXACTLY `name` (the negative-control private route)."""
        if cert.mode != "zero_window":
            raise ValueError("_emit_strip needs a zero_window certificate")
        return _strip_doc(cert, name, _Spell(cert)) + _strip_theorem(cert, name)

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        blocks: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ZeroSumMajorantCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            parts: list[str] = []
            if cert.mode == "tail_envelope":
                if "envelope" in cert.faces:
                    parts.append(_envelope_theorem(cert, nm))
                if "rate" in cert.faces:
                    parts.append(_rate_theorem(cert, nm))
            else:
                if "strip" in cert.faces:
                    parts.append(self._emit_strip(cert, f"{nm}_strip"))
                if "majorant" in cert.faces:
                    parts.append(_le_theorem(cert, nm))
                if "summable" in cert.faces:
                    parts.append(_summable_theorem(cert, nm))
            n_thm += len(parts)
            blocks.append("\n".join(parts))
        return "\n".join(blocks), n_thm


def zero_sum_majorant_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a zero-sum majorant family (kind ``zero_sum_majorant``).

    ``spec: pt -> dict`` -- the keyword arguments of :func:`zero_sum_majorant_certificate`
    (the centre, near radius, far constant, numerator, denominator shape, prefactor flag,
    parameters / binders, optional squares and term list; or the tail-envelope data)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("zero_sum_majorant", spec),
        constants=dict(constants or {}),
    )


def with_terms(cert: ZeroSumMajorantCert, terms) -> ZeroSumMajorantCert:
    """A copy of `cert` carrying `terms` WITHOUT re-checking (test / negative-control helper:
    the kernel, not this function, must reject a forged term list)."""
    return replace(cert, terms=tuple((tuple(e), sp.Rational(c)) for e, c in terms))


if __name__ == "__main__":  # pragma: no cover -- manual smoke run
    c = zero_sum_majorant_certificate(centre=0, h=1, c_far="9/4", num=1, den_kind="normSq")
    print("9/4 strip terms:", c.terms)
    try:
        zero_sum_majorant_certificate(centre=0, h=0, c_far="9/4", den_kind="normSq")
        raise SystemExit("FAIL: h = 0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
