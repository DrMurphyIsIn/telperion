"""complex_re_im_split emitter -- kernel-checked REAL / IMAGINARY-PART SPLITS of a complex
polynomial expression, plus the two norm faces they feed and the cast face of a real-valued one.

WHY THIS EMITTER EXISTS
-----------------------
The 48-hour shapes audit (`docs/SHAPES_AUDIT_48H_2026-09-22.md`, section 2, rank 4; sources
B N3, B D7, C 2.10, D 2.2) found the SAME hand-written `have` in seventeen places across the
Weil-wall and Li-face islands: "the real part of this complex polynomial in `z` is that real
polynomial in `z.re`, `z.im`", closed every time by the same

    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, ..., Complex.I_re, Complex.I_im,
               pow_succ, pow_zero, one_mul]
    ring

skeleton (`E6Bridge7.lean:76-86, 103-118`, `E6Bridge28.lean:755-807`, `E6Bridge6.lean:408-421`,
...).  B N3 calls it "the smallest and most frequent shape in the cluster".  This emitter is
that shape as a certificate: sympy computes the split, an independent exact engine re-checks
it, and the kernel re-derives it from Mathlib's component lemmas.

STATEMENT FAMILY
----------------
For a polynomial `p` over `C` in an optional complex variable `z`, real parameters
`c_1, ..., c_k` (Lean binders `(c_1 ... c_k : R)`, cast `(c_i : C)` inside `p`), the imaginary
unit `Complex.I` and rational constants, with `P_re(x, y; c) + i P_im(x, y; c) = p(x + i y)`:

  * mode `re`       : `(p : C).re = P`                       with `P = P_re`
  * mode `im`       : `(p : C).im = P`                       with `P = P_im`
  * mode `norm_sq`  : `||p|| ^ 2 = P`                        with `P = P_re^2 + P_im^2`
  * mode `norm_exp` : `||Complex.exp p|| = Real.exp P`      with `P = P_re`
  * mode `cast`     : `(p : C) = ((P : R) : C)`              with `P = P_re`  (THE CAST FACE)
  * mode `cast_re`  : `(p : C).re = P`, proved THROUGH the cast identity (B D7's skeleton)

`x`, `y` are rendered as `z.re`, `z.im`; when `p` has no complex variable (the Li-face
instances `Re (a + b i)^N`) the statement is purely in the real parameters.  The claim `P` is
the statement's right-hand side: any real polynomial that is RING-EQUAL to the target; the
emitter never rewrites the claim into a canonical form, it CHECKS it and renders it.

THE CAST FACE (B D7, "this complex expression is the cast of that real expression, so its
`.re` is that real"): `p` is a real-valued expression -- no complex variable, no `I` -- of
real atoms and rational constants, and the statement is the complex-valued identity
`(p : C) = ((P : R) : C)` (the hand proofs' `hcast`), or its `.re` consequence (`cast_re`).
Every B D7 site casts a NATURAL number into `C` (`(zeroMult rho : C)`), so a parameter may be
declared a natural-number atom (`nat_params`): Lean binder `(m : N)`, rendered `(m : C)`
(`Nat.cast`) on the complex side and `(m : R)` on the real side.  The same atoms serve the
`re` / `im` / norm modes, whose simp set then uses `Complex.natCast_re` / `natCast_im`.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
-----------------------------------------------------------
A finite polynomial identity between the components of a complex expression and two real
polynomials.  Nothing about zeta, its zeros, or RH: the identities are bookkeeping steps the
islands' analytic proofs consume.  conjecture1_proved = False.

THE CERTIFICATE AND ITS RE-VERIFICATION
---------------------------------------
`complex_re_im_split_certificate` computes `P_re`, `P_im` with sympy's `re`/`im` at
`z = x + i y` (all symbols real) and then re-verifies them THREE independent ways before the
claim is even looked at:

  1. the symbolic identity `expand(P_re + i P_im - p(x + i y)) == 0`;
  2. sympy's second route `p(x + i y).as_real_imag()` agrees with route 1;
  3. an INDEPENDENT exact evaluator over pairs of Python `Fraction`s (complex arithmetic
     written out by hand on the expression tree) agrees with `(P_re, P_im)` at seeded
     rational points (the faithfulness / dual-engine discipline of HONESTY_PATTERNS #1).

Then the claim: `expand(claim - target) == 0`, exactly.  Finally the load-bearing check
`nonvacuity.assert_certificate_sensitive`: the emitted identity must vanish for the true claim
and be BROKEN by a corrupted one, so the theorem cannot collapse into a tautology.

ANTI-PHANTOM REFUSALS (the forge face)
--------------------------------------
The two phantoms the audit names (B N3) and the ones the shape implies.  Every refusal
raises `ValueError("complex_re_im_split REFUSED: ...")` with the reason; nothing is widened
or repaired silently:

  * non-polynomial `p`  -- a division (`1/z`, `(z - c)^(-1)`, a rational function), a
                           transcendental function, `conjugate`, `re`/`im`, `Abs`, or a
                           power that is not a positive integer literal (symbolic `N`,
                           fractional).  A nonzero-denominator face is a documented
                           follow-on, NOT applied silently (B N3 phantom 1);
  * a supplied claim that disagrees with the computed split (`claim - target` does not
                           expand to 0) -- THE FORGE CASE (B N3 phantom 2);
  * a symbol in `p` that is neither `z`, a declared parameter, nor `I`;
  * a parameter not declared `real=True` (its `re`/`im` would not be what the Lean binder
                           `(c : R)` says), or a complex variable declared real;
  * a natural-number atom that is not a declared parameter, or not declared
                           `integer=True, nonnegative=True` (the binder `(m : N)` would lie);
  * the cast face on an expression that is not real-valued by construction: a complex
                           variable (`z` is not real) or the imaginary unit (`push_cast;
                           ring` cannot use `I^2 = -1`; such an expression is the re/im
                           modes' business);
  * a claim mentioning `z.re`/`z.im` when `p` has no complex variable, or an undeclared
                           symbol, or non-polynomial structure;
  * a float literal anywhere (it would smuggle in a binary expansion);
  * total degree above `max_degree` (default 10): the `pow_succ` expansion and `ring`
                           closure are sized for the island degrees (<= 5 today);
  * a degenerate `p` -- a bare complex variable or a bare constant (nothing to split;
                           `z.re = z.re` is the reflexive class the nonvacuity lint refuses),
                           or a bare atom (`(c : C).re = c` is `Complex.ofReal_re` itself,
                           `(c : C) = ((c : R) : C)` is reflexive): no split to certify;
  * a `tie_to` that is not a (dotted) Lean identifier (it is rendered after `:=`);
  * a binder name that is a Lean keyword, `Complex` / `Real` (the emitted text writes
                           `Complex.I`, `Real.exp`), or a hypothesis the proof binds (`hre`,
                           `hcast`);
  * an unknown mode.

FROZEN TACTIC SKELETON (no search anywhere)
-------------------------------------------
  re / im   :  simp only [SIMP_SET]; all_goals ring
  norm_sq   :  rw [Complex.sq_norm, Complex.normSq_apply]; simp only [SIMP_SET]; all_goals ring
  norm_exp  :  have hre : (p : C).re = P := by simp only [SIMP_SET]; all_goals ring
               rw [Complex.norm_exp, hre]
  cast      :  push_cast; all_goals ring
  cast_re   :  have hcast : (p : C) = ((P : R) : C) := by push_cast; all_goals ring
               rw [hcast, Complex.ofReal_re]

The cast face is the audit's `push_cast; ring` then `Complex.ofReal_re` verbatim (B D7):
`push_cast` is the fixed `norm_cast` simp set (deterministic), and `all_goals ring` again
because `push_cast` closes the goal outright when both sides normalise to the same term.

`SIMP_SET` is the FIXED union of the component lemmas the hand proofs use (component
projections of `+ - * neg`, real and natural casts, `I`, numerals, and
`pow_succ`/`pow_zero`/`one_mul` to unfold literal powers); per instance it is restricted, in
canonical order, to the lemmas `simp` will actually rewrite with (`simp_set_for`: a
simulation of how the `.re`/`.im` projections propagate through the rendered tree, never a
Lean run), so nothing that can fire is ever dropped and Lean's unused-simp-argument linter
stays quiet.  `simp only` is deterministic; `ring` is a decision procedure for
commutative-ring identities.  `all_goals ring` rather than a bare `ring` because `simp only`
closes the goal outright when the claim is syntactically the component projection (e.g.
`(z + 1).re = z.re + 1`), where a bare `ring` would fail with no goals (the
`rational_identity` emitter's `field_simp` footgun, same remedy); in that case Lean's
unusedTactic linter notes that `all_goals ring` does nothing -- a warning, never an error.
A corrupted claim leaves `ring` with a false identity, the proof does not close, and the
kernel rejects the file: that is the negative control
(`negctrl_adapters/adapter_complex_re_im_split.py`).

conjecture1_proved = False.
"""
from __future__ import annotations

import re as _re
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .nonvacuity import assert_certificate_sensitive
from .workflow import Emitter

#: The cast face (B D7): a real-valued `p`, stated as a cast identity or its `.re`.
CAST_MODES = ("cast", "cast_re")
MODES = ("re", "im", "norm_sq", "norm_exp") + CAST_MODES

#: Total degree above this is refused (the `pow_succ` unfolding and the `ring` closure are
#: sized for the island instances, degree <= 5 in `E6Bridge28`).
MAX_DEGREE = 10

#: The default symbols standing for `z.re` and `z.im` in a claim.
RE_SYM = sp.Symbol("x", real=True)
IM_SYM = sp.Symbol("y", real=True)

#: The FROZEN `simp only` set: the union of the component lemmas of the hand proofs
#: (`E6Bridge7.lean:78-121`, `E6Bridge28.lean:790-807`, `E6Bridge6.lean:408-421`, and the
#: natural-cast pair of `E6Bridge12.lean:122-126`).
SIMP_SET = (
    "Complex.add_re", "Complex.add_im", "Complex.sub_re", "Complex.sub_im",
    "Complex.mul_re", "Complex.mul_im", "Complex.neg_re", "Complex.neg_im",
    "Complex.ofReal_re", "Complex.ofReal_im", "Complex.natCast_re", "Complex.natCast_im",
    "Complex.I_re", "Complex.I_im",
    "Complex.re_ofNat", "Complex.im_ofNat", "Complex.one_re", "Complex.one_im",
    "Complex.zero_re", "Complex.zero_im", "pow_succ", "pow_zero", "one_mul",
)


def simp_call(lemmas: Sequence[str], indent: int = 2, width: int = 100) -> str:
    """`simp only [lemmas]` wrapped at `width` columns (continuation lines indented two deeper
    than the tactic, the hand proofs' layout) followed by `all_goals ring`; only line-broken,
    never reordered.  `all_goals ring` rather than a bare `ring` because `simp only` closes
    the goal outright when the claim is syntactically the component projection (then a bare
    `ring` would fail with no goals) -- the `rational_identity` emitter's `field_simp` footgun
    of 2026-08-20, same remedy."""
    lemmas = tuple(lemmas)
    head = " " * indent + "simp only ["
    cont = " " * (indent + 2)
    lines: list[str] = []
    cur = head
    for i, lem in enumerate(lemmas):
        piece = lem + ("," if i < len(lemmas) - 1 else "]")
        if len(cur) + 1 + len(piece) > width and cur.strip() != "simp only [":
            lines.append(cur.rstrip())
            cur = cont + piece
        else:
            cur = cur + ("" if cur.endswith("[") else " ") + piece
    lines.append(cur.rstrip())
    lines.append(" " * indent + "all_goals ring")
    return "\n".join(lines) + "\n"


_IDENT = _re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_PREFIX = "complex_re_im_split REFUSED"

#: Names a binder may not take: Lean keywords (not identifiers at all), the namespaces the
#: emitted text writes qualified (kernel-checked 2026-09-22: under a binder `(Complex : ℝ)`,
#: `Complex.I` elaborates as field access on that real and fails), and the hypotheses the
#: emitted proofs bind (`hre`, `hcast`: legal Lean, the `have` shadows the binder only after
#: its own statement, but refused so the emitted proof reads unambiguously).  The two
#: incomplete-proof keywords need no entry: the emit pipeline's lint already rejects them.
_RESERVED_NAMES = frozenset({
    "fun", "let", "have", "show", "from", "by", "at", "in", "if", "then", "else", "do",
    "match", "with", "return", "for", "try", "catch", "finally", "theorem", "lemma", "def",
    "example", "abbrev", "instance", "structure", "class", "inductive", "where", "deriving",
    "namespace", "section", "end", "open", "variable", "universe", "import", "axiom",
    "opaque", "noncomputable", "private", "protected", "partial", "unsafe", "calc",
    "suffices", "obtain", "forall", "exists", "Type", "Prop", "Sort",
    "Complex", "Real", "hre", "hcast",
})


def _refuse(msg: str) -> ValueError:
    return ValueError(f"{_PREFIX}: {msg}")


# --- the polynomial contract ------------------------------------------------

def _check_polynomial(e, allowed: set, what: str, *, allow_I: bool) -> int:
    """Walk the tree; refuse anything outside `{Add, Mul, Pow^(positive int), Symbol in
    allowed, Rational, I}`.  Returns the number of arithmetic nodes seen."""
    nodes = 0
    for sub in sp.preorder_traversal(e):
        if sub is sp.I:
            if not allow_I:
                raise _refuse(f"{what} contains the imaginary unit I (a real claim must not)")
            continue
        if isinstance(sub, sp.Float):
            raise _refuse(f"{what} contains a float literal {sub}; a float carries its binary "
                          "expansion, not the rational you wrote -- use sp.Rational")
        if sub.is_Symbol:
            if sub not in allowed:
                raise _refuse(f"{what} mentions the undeclared symbol {sub} (declare it as the "
                              "complex variable z or as a real parameter)")
            continue
        if sub.is_Rational:
            continue
        if sub.is_Add or sub.is_Mul:
            nodes += 1
            continue
        if sub.is_Pow:
            _base, exp = sub.args
            if not (exp.is_Integer and exp > 0):
                if exp.is_Integer and exp < 0:
                    raise _refuse(
                        f"{what} is not a polynomial: division by {_base} (exponent {exp}). "
                        "A nonzero-denominator face is a documented follow-on, not applied "
                        "silently")
                raise _refuse(f"{what} has the exponent {exp} in {sub}, which is not a positive "
                              "integer literal (a symbolic or fractional power is not a "
                              "polynomial the pow_succ skeleton can unfold)")
            nodes += 1
            continue
        raise _refuse(f"{what} contains the non-polynomial node {type(sub).__name__} ({sub}); "
                      "only + - * and positive integer powers of z, real parameters, I and "
                      "rational constants are certified")
    return nodes


# --- the independent exact engine -------------------------------------------

_F0, _F1 = Fraction(0), Fraction(1)


def _c_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _c_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def eval_complex_exact(e, env: dict) -> tuple[Fraction, Fraction]:
    """Evaluate a polynomial complex expression EXACTLY as a pair of Fractions, by hand on
    the tree (no sympy `re`/`im`): the independent engine of the dual-engine check.
    `env` maps every symbol (the complex variable included) to a `(re, im)` pair."""
    if e is sp.I:
        return (_F0, _F1)
    if e.is_Symbol:
        return env[e]
    if e.is_Rational:
        return (Fraction(int(e.p), int(e.q)), _F0)
    if e.is_Add:
        acc = (_F0, _F0)
        for a in e.args:
            acc = _c_add(acc, eval_complex_exact(a, env))
        return acc
    if e.is_Mul:
        acc = (_F1, _F0)
        for a in e.args:
            acc = _c_mul(acc, eval_complex_exact(a, env))
        return acc
    if e.is_Pow:
        base, exp = e.args
        acc = (_F1, _F0)
        b = eval_complex_exact(base, env)
        for _ in range(int(exp)):
            acc = _c_mul(acc, b)
        return acc
    raise _refuse(f"independent engine: unsupported node {type(e).__name__}")  # pragma: no cover


def _frac_of(q) -> Fraction:
    q = sp.Rational(q)
    return Fraction(int(q.p), int(q.q))


# --- the certificate ----------------------------------------------------------

@dataclass(frozen=True)
class ComplexReImSplitCert:
    """One real/imaginary-part split certificate.

    `p` is the complex polynomial expression (in `z`, the real `params`, `I`); `mode` the
    face; `claim` the CLAIMED real polynomial (the statement's right-hand side, in
    `re_sym`, `im_sym`, `params`); `p_re`, `p_im` sympy's expanded split, re-verified.
    `tie_to` optionally names an existing hand lemma whose statement the emitted theorem is
    kernel-checked to be identical to (`example : <type> := <tie_to>`).  `nat_params` is the
    subset of `params` bound as natural numbers (`(m : N)`, cast `(m : C)` / `(m : R)`).
    """

    p: sp.Expr
    z: sp.Symbol | None
    params: tuple[sp.Symbol, ...]
    re_sym: sp.Symbol
    im_sym: sp.Symbol
    mode: str
    claim: sp.Expr
    p_re: sp.Expr
    p_im: sp.Expr
    tie_to: str | None = None
    nat_params: tuple[sp.Symbol, ...] = ()

    @property
    def target(self) -> sp.Expr:
        """The real polynomial the claim must be ring-equal to (mode-dependent)."""
        if self.mode in ("re", "norm_exp") + CAST_MODES:
            return self.p_re
        if self.mode == "im":
            return self.p_im
        if self.mode == "norm_sq":
            return sp.expand(self.p_re ** 2 + self.p_im ** 2)
        raise _refuse(f"unknown mode {self.mode!r}")  # pragma: no cover


def _claim_residual(cert: ComplexReImSplitCert) -> sp.Expr:
    return sp.expand(cert.claim - cert.target)


_SEED_POINTS = (
    (Fraction(1, 3), Fraction(-2, 5), Fraction(7, 4), Fraction(-3, 2), Fraction(5, 6)),
    (Fraction(-2), Fraction(3, 7), Fraction(-1, 4), Fraction(9, 5), Fraction(-6, 11)),
    (Fraction(5, 2), Fraction(1, 9), Fraction(4, 3), Fraction(-7, 8), Fraction(2, 13)),
)


_DOTTED_IDENT = _re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")


def complex_re_im_split_certificate(
    p, *, mode: str, claim=None, z=None, params: Sequence[sp.Symbol] = (),
    re_sym: sp.Symbol = RE_SYM, im_sym: sp.Symbol = IM_SYM, tie_to: str | None = None,
    max_degree: int = MAX_DEGREE, nat_params: Sequence[sp.Symbol] = (),
) -> tuple[ComplexReImSplitCert, int]:
    """Build (and exactly re-check) a split certificate; returns `(cert, n_checks)`.

    `claim=None` uses the computed target itself as the claim (it is still put through
    every check).  `nat_params` marks which of `params` are natural-number atoms (Lean
    binder `(m : N)`).  See the module docstring for the refusal list.
    """
    if mode not in MODES:
        raise _refuse(f"unknown mode {mode!r} (expected one of {MODES})")
    p = sp.sympify(p)
    params = tuple(params)
    nat_params = tuple(nat_params)
    if tie_to is not None and not (isinstance(tie_to, str) and _DOTTED_IDENT.match(tie_to)):
        raise _refuse(f"tie_to {tie_to!r} is not a (dotted) Lean identifier; the tie gate "
                      "renders it verbatim after `:=`")
    for m in nat_params:
        if m not in params:
            raise _refuse(f"natural-number atom {m!r} is not a declared parameter (list it in "
                          "params, in binder order, and mark it in nat_params)")
        if not (m.is_integer and m.is_nonnegative):
            raise _refuse(f"natural-number atom {m} is not declared integer=True, "
                          "nonnegative=True; the Lean binder (m : N) would not be what sympy "
                          "splits")
    if len(set(nat_params)) != len(nat_params):
        raise _refuse("duplicate natural-number atoms")
    if z is not None and not isinstance(z, sp.Symbol):
        raise _refuse(f"z = {z!r} is not a sympy Symbol")
    if z is not None and z.is_real:
        raise _refuse(f"the complex variable {z} is declared real; it is bound as (z : C)")
    if z is not None and not _IDENT.match(str(z)):
        raise _refuse(f"complex variable name {z!r} is not a Lean identifier")
    if z is not None and str(z) in _RESERVED_NAMES:
        raise _refuse(f"complex variable name {z!r} is reserved (a Lean keyword, a namespace "
                      "the emitted text writes qualified, or a name the proof binds)")
    for c in params:
        if not isinstance(c, sp.Symbol):
            raise _refuse(f"parameter {c!r} is not a sympy Symbol")
        if not c.is_real:
            raise _refuse(f"parameter {c} is not declared real=True; its re/im split would not "
                          "be what the Lean binder (c : R) states")
        if not _IDENT.match(str(c)):
            raise _refuse(f"parameter name {c!r} is not a Lean identifier")
        if str(c) in _RESERVED_NAMES:
            raise _refuse(f"parameter name {c!r} is reserved (a Lean keyword, a namespace the "
                          "emitted text writes qualified, or a name the proof binds)")
        if c == z:
            raise _refuse(f"{c} is both the complex variable and a parameter")
    if len(set(params)) != len(params):
        raise _refuse("duplicate parameter symbols")
    for s in (re_sym, im_sym):
        if not (isinstance(s, sp.Symbol) and s.is_real):
            raise _refuse(f"re_sym/im_sym {s!r} must be a real sympy Symbol")
        if s in params or s == z:
            raise _refuse(f"re_sym/im_sym {s} clashes with a parameter or the complex variable")
    if re_sym == im_sym:
        raise _refuse("re_sym and im_sym must differ")
    if z is None and not params:
        raise _refuse("p has neither a complex variable nor a parameter: a bare constant, "
                      "nothing to split")

    allowed_c = set(params) | ({z} if z is not None else set())
    if re_sym in p.free_symbols or im_sym in p.free_symbols:
        raise _refuse(f"p mentions {re_sym}/{im_sym}, which stand for z.re/z.im in the claim; "
                      "write p in the complex variable z")
    nodes = _check_polynomial(p, allowed_c, "p", allow_I=True)
    if nodes == 0:
        if p == z or p.is_Rational:
            raise _refuse(f"degenerate p = {p}: nothing to split (the reflexive class)")
        raise _refuse(f"degenerate p = {p}: a bare atom, whose components (or cast) are a "
                      "single Mathlib lemma (ofReal_re / natCast_re / I_re / ofReal_natCast), "
                      "not a split")
    if mode in CAST_MODES:
        # The cast face states `p = ((P : R) : C)`: p must be real-valued BY CONSTRUCTION.
        if z is not None:
            raise _refuse(f"the cast face needs a real-valued p, but p has the complex "
                          f"variable {z} (z is not real); use the re / im modes")
        if p.has(sp.I):
            raise _refuse("the cast face needs an I-free p: `push_cast; ring` treats I as an "
                          "atom and cannot use I^2 = -1, so a real-valued expression carrying I "
                          "is the re / im modes' business")
    checks = 1  # polynomial contract

    # the split, route 1
    pz = sp.expand(p.subs(z, re_sym + sp.I * im_sym)) if z is not None else sp.expand(p)
    p_re = sp.expand(sp.re(pz))
    p_im = sp.expand(sp.im(pz))
    real_syms = {re_sym, im_sym} | set(params)
    if not (p_re.free_symbols <= real_syms and p_im.free_symbols <= real_syms):
        raise _refuse("sympy could not split p into real polynomials (a symbol is not "  # pragma: no cover
                      f"real): re = {p_re}, im = {p_im}")
    if sp.expand(p_re + sp.I * p_im - pz) != 0:
        raise _refuse("internal: the computed split does not reproduce p")  # pragma: no cover
    checks += 1
    # route 2
    r2, i2 = pz.as_real_imag()
    if sp.expand(r2 - p_re) != 0 or sp.expand(i2 - p_im) != 0:
        raise _refuse("internal: as_real_imag disagrees with re/im")  # pragma: no cover
    checks += 1
    # route 3: the independent exact engine at seeded rational points
    ordered = [re_sym, im_sym, *params]
    for pt in _SEED_POINTS:
        vals = {s: pt[i % len(pt)] for i, s in enumerate(ordered)}
        env = {c: (vals[c], _F0) for c in params}
        if z is not None:
            env[z] = (vals[re_sym], vals[im_sym])
        got = eval_complex_exact(p, env)
        subs = {s: sp.Rational(v.numerator, v.denominator) for s, v in vals.items()}
        want = (_frac_of(p_re.subs(subs)), _frac_of(p_im.subs(subs)))
        if got != want:
            raise _refuse(f"dual-engine disagreement at {vals}: hand evaluator {got}, "  # pragma: no cover
                          f"sympy split {want}")
        checks += 1

    # degree cap
    deg = max(sp.Poly(q, *ordered).total_degree() if q != 0 else 0 for q in (p_re, p_im))
    if deg > max_degree:
        raise _refuse(f"total degree {deg} exceeds the cap {max_degree} (the pow_succ/ring "
                      "skeleton is sized for the island degrees); raise max_degree explicitly")
    checks += 1

    # the claim
    if mode in CAST_MODES and p_im != 0:
        # unreachable for an I-free, z-free p over real atoms; kept as the exact check that
        # the cast identity is TRUE (a nonzero imaginary part would make it false)
        raise _refuse(f"p is not real-valued: im = {p_im}")  # pragma: no cover
    if mode in ("re", "norm_exp") + CAST_MODES:
        target = p_re
    elif mode == "im":
        target = p_im
    else:
        target = sp.expand(p_re ** 2 + p_im ** 2)
    claim = target if claim is None else sp.sympify(claim)
    allowed_r = set(params) | ({re_sym, im_sym} if z is not None else set())
    if z is None and (re_sym in claim.free_symbols or im_sym in claim.free_symbols):
        raise _refuse(f"the claim mentions {re_sym}/{im_sym} but p has no complex variable")
    _check_polynomial(claim, allowed_r, "claim", allow_I=False)
    residual = sp.expand(claim - target)
    if residual != 0:
        raise _refuse(
            f"the supplied claim disagrees with the computed split (mode {mode}): "
            f"claim - target = {residual}; sympy gives target = {target}.  The emitter "
            "refuses rather than replacing your claim")
    checks += 1

    cert = ComplexReImSplitCert(
        p=p, z=z, params=params, re_sym=re_sym, im_sym=im_sym, mode=mode, claim=claim,
        p_re=p_re, p_im=p_im, tie_to=tie_to, nat_params=nat_params,
    )

    # load-bearing check: the identity must depend on the claim
    def _shift_by_symbol(c):
        s = c.re_sym if c.z is not None else c.params[0]
        return replace(c, claim=c.claim - s)

    assert_certificate_sensitive(
        _claim_residual, cert,
        [lambda c: replace(c, claim=c.claim + 1), _shift_by_symbol],
        label=f"complex_re_im_split ({mode})",
    )
    checks += 1
    return cert, checks


def certify_complex_re_im_split_point(family, pt, name):
    """Certify one split instance: ``(CertifiedInstance, n_checks)``.

    Reads the spec dict from ``family.special[1](pt)`` -- keys ``p``, ``mode`` and the
    optional ``claim`` / ``z`` / ``params`` / ``nat_params`` / ``re_sym`` / ``im_sym`` /
    ``tie_to`` / ``max_degree`` -- and builds the certificate through
    :func:`complex_re_im_split_certificate` (which raises on every dishonest instance)."""
    spec = family.special[1](pt)
    kw = {}
    for k in ("claim", "z", "params", "nat_params", "re_sym", "im_sym", "tie_to",
              "max_degree"):
        if k in spec and spec[k] is not None:
            kw[k] = spec[k]
    cert, checks = complex_re_im_split_certificate(spec["p"], mode=spec["mode"], **kw)
    return CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert), checks


# --- Lean rendering ---------------------------------------------------------

def _lead_key(term, gens):
    """Descending-lex ordering key of a term: the leading monomial of its expansion over
    `gens` (higher first).  Falls back to a stable zero key when `Poly` cannot see it."""
    try:
        e = sp.expand(term)
        if e == 0:
            return tuple([0] * len(gens))
        poly = sp.Poly(e, *gens)
        return tuple(poly.monoms(order="lex")[0])
    except Exception:  # pragma: no cover -- defensive; the contract check precedes rendering
        return tuple([0] * len(gens))


def _is_negative_term(t) -> bool:
    if t.is_Rational:
        return t < 0
    if t.is_Mul:
        coeff, _rest = t.as_coeff_Mul()
        return coeff.is_Rational and coeff < 0
    return False


class _Renderer:
    """Structure-preserving, deterministically ordered Lean renderer.

    Terms of a sum and the atomic factors of a product are ordered by descending lex degree
    over `gens` (the complex variable / `z.re`, `z.im` first, then the parameters in their
    declared order); compound factors follow the atomic ones and `I` comes last.  Negative
    terms render as subtractions.  The rendering is what the theorem STATES; `ring` does not
    care about the arrangement, so no canonicalization is applied.  A natural-number atom
    `m` renders `(m : ℂ)` (`Nat.cast`) on the complex side and `(m : ℝ)` on the real side.
    """

    def __init__(self, *, complex_side: bool, z, params, re_sym, im_sym, nat=()):
        self.complex_side = complex_side
        self.z = z
        self.params = tuple(params)
        self.nat = frozenset(nat)
        self.re_sym, self.im_sym = re_sym, im_sym
        if complex_side:
            self.gens = ([z] if z is not None else []) + list(self.params)
        else:
            self.gens = ([re_sym, im_sym] if z is not None else []) + list(self.params)

    # atoms
    def _symbol(self, s) -> str:
        if self.complex_side:
            if s == self.z:
                return str(s)
            return f"({s} : ℂ)"
        if s == self.re_sym:
            return f"{self.z}.re"
        if s == self.im_sym:
            return f"{self.z}.im"
        if s in self.nat:
            return f"({s} : ℝ)"
        return str(s)

    def _number(self, q) -> str:
        q = sp.Rational(q)
        if q.is_Integer:
            return str(q) if q >= 0 else f"(-{-q})"
        if self.complex_side:
            return f"(({rat_lean(q)} : ℝ) : ℂ)"
        return rat_lean(q)

    def _order_terms(self, terms):
        return sorted(terms, key=lambda t: _lead_key(t, self.gens), reverse=True)

    def _order_factors(self, factors):
        atoms, compound, unit = [], [], []
        for f in factors:
            if f is sp.I:
                unit.append(f)
            elif f.is_Symbol or (f.is_Pow and f.args[0].is_Symbol):
                atoms.append(f)
            else:
                compound.append(f)
        atoms.sort(key=lambda f: _lead_key(f, self.gens), reverse=True)
        compound.sort(key=lambda f: _lead_key(f, self.gens), reverse=True)
        return atoms + compound + unit

    def render(self, e, prec: int = 0) -> str:
        """prec 0 = sum level, 1 = product level, 2 = atom level (parenthesize compounds)."""
        if e is sp.I:
            return "Complex.I"
        if e.is_Symbol:
            return self._symbol(e)
        if e.is_Rational:
            return self._number(e)
        if e.is_Add:
            terms = self._order_terms(list(e.args))
            out = ""
            for i, t in enumerate(terms):
                if _is_negative_term(t):
                    body = self.render(-t, 1)
                    out += (f"-({body})" if i == 0 else f" - {body}")
                else:
                    body = self.render(t, 1)
                    out += (body if i == 0 else f" + {body}")
            return f"({out})" if prec >= 1 else out
        if e.is_Mul:
            coeff, rest = e.as_coeff_Mul()
            neg = coeff.is_Rational and coeff < 0
            if neg:
                coeff = -coeff
            factors = list(rest.args) if rest.is_Mul else ([rest] if rest != 1 else [])
            parts = ([self._number(coeff)] if coeff != 1 else []) + [
                self.render(f, 2) for f in self._order_factors(factors)]
            if not parts:
                parts = [self._number(sp.Integer(1))]
            body = " * ".join(parts)
            if neg:
                return f"-({body})"
            return f"({body})" if prec >= 2 and len(parts) > 1 else body
        if e.is_Pow:
            base, exp = e.args
            return f"{self.render(base, 2)} ^ {int(exp)}"
        raise ValueError(f"complex_re_im_split renderer: unsupported node {type(e).__name__}")


def _binders(cert: ComplexReImSplitCert) -> str:
    """The theorem's binders: the parameters in declared order, consecutive atoms of one
    type grouped (`(c lam : ℝ)`, `(m : ℕ) (u : ℝ)`), then the complex variable."""
    groups = []
    nat = set(cert.nat_params)
    run: list[str] = []
    run_ty = None
    for c in cert.params:
        ty = "ℕ" if c in nat else "ℝ"
        if run and ty != run_ty:
            groups.append("(" + " ".join(run) + f" : {run_ty})")
            run = []
        run.append(str(c))
        run_ty = ty
    if run:
        groups.append("(" + " ".join(run) + f" : {run_ty})")
    if cert.z is not None:
        groups.append(f"({cert.z} : ℂ)")
    return " ".join(groups)


def _forall_prefix(cert: ComplexReImSplitCert) -> str:
    return "∀ " + _binders(cert) + ", "


def _renderers(cert: ComplexReImSplitCert) -> tuple[_Renderer, _Renderer]:
    kw = dict(z=cert.z, params=cert.params, re_sym=cert.re_sym, im_sym=cert.im_sym,
              nat=cert.nat_params)
    return _Renderer(complex_side=True, **kw), _Renderer(complex_side=False, **kw)


def render_statement(cert: ComplexReImSplitCert) -> tuple[str, str, str]:
    """`(p_lean, claim_lean, proposition)` for one certificate; `proposition` is the
    binder-free Lean proposition the theorem states (the single source the gate reuses)."""
    rc, rr = _renderers(cert)
    p_lean = rc.render(cert.p, 0)
    claim_lean = rr.render(cert.claim, 0)
    if cert.mode in ("re", "cast_re"):
        prop = f"({p_lean} : ℂ).re = {claim_lean}"
    elif cert.mode == "im":
        prop = f"({p_lean} : ℂ).im = {claim_lean}"
    elif cert.mode == "norm_sq":
        prop = f"‖({p_lean} : ℂ)‖ ^ 2 = {claim_lean}"
    elif cert.mode == "norm_exp":
        prop = f"‖Complex.exp ({p_lean} : ℂ)‖ = Real.exp ({claim_lean})"
    else:  # cast
        prop = f"({p_lean} : ℂ) = (({claim_lean} : ℝ) : ℂ)"
    return p_lean, claim_lean, prop


_BOTH = frozenset({"re", "im"})


def _projection_needs(e, projs: frozenset, z, gens, out: set, nat=frozenset()) -> None:
    """Simulate how `simp only` propagates the projections `projs` (a subset of
    `{re, im}`) through the RENDERED tree of `e`, collecting the component lemmas it will
    rewrite with.  Mirrors `_Renderer.render` shape for shape (same term ordering, products
    left-associated):

      * a sum `t_1 + t_2 - t_3` is `(t_1 + t_2) - t_3`: `add_p`/`sub_p` per later term and
        `neg_p` for a leading negative term, every term projected as `p`;
      * a product `u * v` needs `mul_p` and BOTH projections of `u` and `v`; a chain
        `u * v * w` is `(u * v) * w`, so the inner product is projected both ways (both
        `mul_re` and `mul_im`); a literal power `u ^ n` unfolds to an `n`-fold product;
      * a real cast needs `ofReal_p`, a natural cast `natCast_p`, `I` needs `I_p`, a numeral
        `re/im_ofNat`, `one_p` or `zero_p`, a negative numeral additionally `neg_p`.
    """
    if e is sp.I:
        out.update(f"Complex.I_{p}" for p in projs)
        return
    if e.is_Symbol:
        if e in nat:
            out.update(f"Complex.natCast_{p}" for p in projs)
        elif e != z:
            out.update(f"Complex.ofReal_{p}" for p in projs)
        return
    if e.is_Rational:
        if e < 0:
            out.update(f"Complex.neg_{p}" for p in projs)
            e = -e
        if e.is_Integer:
            if e >= 2:
                out.update(("Complex.re_ofNat" if p == "re" else "Complex.im_ofNat")
                           for p in projs)
            elif e == 1:
                out.update(f"Complex.one_{p}" for p in projs)
            else:
                out.update(f"Complex.zero_{p}" for p in projs)
        else:
            out.update(f"Complex.ofReal_{p}" for p in projs)
        return
    if e.is_Add:
        terms = sorted(e.args, key=lambda t: _lead_key(t, gens), reverse=True)
        for i, t in enumerate(terms):
            if _is_negative_term(t):
                out.update((f"Complex.neg_{p}" if i == 0 else f"Complex.sub_{p}")
                           for p in projs)
                _projection_needs(-t, projs, z, gens, out, nat)
            else:
                if i > 0:
                    out.update(f"Complex.add_{p}" for p in projs)
                _projection_needs(t, projs, z, gens, out, nat)
        return
    if e.is_Mul:
        coeff, rest = e.as_coeff_Mul()
        if coeff.is_Rational and coeff < 0:
            out.update(f"Complex.neg_{p}" for p in projs)
            coeff = -coeff
        factors = list(rest.args) if rest.is_Mul else ([rest] if rest != 1 else [])
        parts = ([coeff] if coeff != 1 else []) + factors
        if len(parts) >= 2:
            out.update(f"Complex.mul_{p}" for p in projs)
            if len(parts) >= 3:  # `(a * b) * c`: the inner product is projected both ways
                out.update(f"Complex.mul_{p}" for p in _BOTH)
            for part in parts:
                _projection_needs(part, _BOTH, z, gens, out, nat)
        else:
            _projection_needs(parts[0], projs, z, gens, out, nat)
        return
    if e.is_Pow:
        base, n = e.args
        out.update(f"Complex.mul_{p}" for p in projs)
        if int(n) >= 3:
            out.update(f"Complex.mul_{p}" for p in _BOTH)
        _projection_needs(base, _BOTH, z, gens, out, nat)
        return
    raise ValueError(f"complex_re_im_split: unsupported node {type(e).__name__}")  # pragma: no cover


def simp_set_for(cert: ComplexReImSplitCert) -> tuple[str, ...]:
    """The `simp only` lemmas for one certificate: the canonical `SIMP_SET` restricted, in
    canonical order, to the component lemmas `simp` will actually rewrite with.

    Computed by `_projection_needs`, a simulation of the projection propagation through the
    rendered tree (never a Lean run): the top projection is `re` for the `re`/`norm_exp`
    faces, `im` for `im`, both for `norm_sq` (`normSq_apply` exposes `p.re` and `p.im`).  The
    power unfolders `pow_succ`/`pow_zero`/`one_mul` are kept whenever a literal power occurs
    on either side (simp rewrites both sides).  The selection never drops a lemma that can
    fire, so the closure is unchanged; the point is a warning-free emitted file.  The cast
    face does not use the component set (its skeleton is `push_cast`): empty tuple."""
    if cert.mode in CAST_MODES:
        return ()
    top = {"re": frozenset({"re"}), "norm_exp": frozenset({"re"}),
           "im": frozenset({"im"}), "norm_sq": _BOTH}[cert.mode]
    gens = ([cert.z] if cert.z is not None else []) + list(cert.params)
    needs: set[str] = set()
    _projection_needs(cert.p, top, cert.z, gens, needs, frozenset(cert.nat_params))
    if cert.p.atoms(sp.Pow) or cert.claim.atoms(sp.Pow):
        needs.update(("pow_succ", "pow_zero", "one_mul"))
    return tuple(lem for lem in SIMP_SET if lem in needs)


def _cast_call(indent: int) -> str:
    """The cast face's frozen closer: `push_cast` (the fixed norm_cast simp set) then
    `all_goals ring` (push_cast closes the goal itself when both sides normalise alike)."""
    pad = " " * indent
    return f"{pad}push_cast\n{pad}all_goals ring\n"


def _proof(cert: ComplexReImSplitCert, p_lean: str, claim_lean: str) -> str:
    if cert.mode == "cast":
        return _cast_call(2)
    if cert.mode == "cast_re":
        return (f"  have hcast : ({p_lean} : ℂ) = (({claim_lean} : ℝ) : ℂ) := by\n"
                + _cast_call(4)
                + "  rw [hcast, Complex.ofReal_re]\n")
    lemmas = simp_set_for(cert)
    if cert.mode in ("re", "im"):
        return simp_call(lemmas, 2)
    if cert.mode == "norm_sq":
        return "  rw [Complex.sq_norm, Complex.normSq_apply]\n" + simp_call(lemmas, 2)
    return (f"  have hre : ({p_lean} : ℂ).re = {claim_lean} := by\n"
            + simp_call(lemmas, 4)
            + "  rw [Complex.norm_exp, hre]\n")


_MODE_WORDS = {
    "re": "the REAL PART",
    "im": "the IMAGINARY PART",
    "norm_sq": "the SQUARED NORM",
    "norm_exp": "the norm of the complex exponential",
    "cast": "the REAL CAST IDENTITY",
    "cast_re": "the REAL PART, through the cast identity,",
}

_SKELETON_WORDS = {
    "cast": "push_cast; all_goals ring.",
    "cast_re": "have hcast := by push_cast; all_goals ring;\n    rw [hcast, Complex.ofReal_re].",
}


@dataclass
class ComplexReImSplitEmitter(Emitter):
    """Emit real/imaginary-part splits (and the `norm_sq` / `norm_exp` faces) of complex
    polynomial expressions, each proved by the frozen `simp only [components]; all_goals ring`
    skeleton of the hand proofs it regenerates, and the cast face of real-valued expressions
    (`p = ((P : R) : C)` and its `.re`) by the frozen `push_cast; all_goals ring` then
    `Complex.ofReal_re`.  No `decide`, no `sorry`; the claimed real polynomial IS the
    statement and `complex_re_im_split_certificate` refuses any claim that is not ring-equal
    to the exactly re-verified split.  conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "complex_re_im_split"

    def _header(self, cert: ComplexReImSplitCert, nm: str) -> str:
        rc, rr = _renderers(cert)
        pre, pim = rr.render(cert.p_re, 0), rr.render(cert.p_im, 0)
        zline = (f"    complex variable `{cert.z}` (split at `{cert.z} = {cert.re_sym} + I "
                 f"{cert.im_sym}`),\n" if cert.z is not None
                 else "    no complex variable (a parameter-only expression),\n")
        nat = set(cert.nat_params)
        reals = [str(c) for c in cert.params if c not in nat]
        if nat:
            atoms = (f"    real parameters {reals},\n"
                     f"    natural-number atoms {[str(c) for c in cert.nat_params]}.\n")
        else:
            atoms = f"    real parameters {reals}.\n"
        skeleton = _SKELETON_WORDS.get(cert.mode, "simp only [component lemmas]; all_goals ring.")
        tie = (f"    Tie gate: the statement is kernel-checked identical to `{cert.tie_to}`.\n"
               if cert.tie_to else "")
        return (
            f"/-- `{nm}` -- {_MODE_WORDS[cert.mode]} of `{rc.render(cert.p, 0)}` "
            f"(mode `{cert.mode}`),\n"
            + zline
            + atoms
            + f"    Split computed by sympy re/im and re-verified by a symbolic identity, by\n"
            f"    as_real_imag, and by an independent exact Fraction evaluator at seeded\n"
            f"    rational points:\n"
            f"      re = {pre},\n"
            f"      im = {pim}.\n"
            f"    The claimed right-hand side is ring-equal to the split (residual 0) and the\n"
            f"    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:\n"
            f"    {skeleton}  A finite polynomial identity;\n"
            f"    nothing about RH.  conjecture1_proved = False.\n"
            + tie
            + "-/\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: ComplexReImSplitCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            p_lean, claim_lean, prop = render_statement(cert)
            binders = _binders(cert)
            head = f"theorem {nm} {binders} :\n    {prop} := by\n"
            lines.append(self._header(cert, nm) + head + _proof(cert, p_lean, claim_lean))
            n_thm += 1
            gate = self.emit_gate(nm, _forall_prefix(cert) + prop)
            if gate:
                lines.append(gate)
            if cert.tie_to:
                lines.append(
                    f"-- tie gate: the regenerated statement IS the hand lemma's statement\n"
                    f"example : {_forall_prefix(cert)}{prop} := {cert.tie_to}\n")
        return "\n".join(lines), n_thm


def complex_re_im_split_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a complex-split family (kind ``complex_re_im_split``).

    ``spec: pt -> {"p", "mode", optional "claim" / "z" / "params" / "nat_params" / "re_sym" /
    "im_sym" / "tie_to" / "max_degree"}`` -- the complex polynomial, the face and the CLAIMED
    real polynomial; everything is re-derived and checked at certify time."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("complex_re_im_split", spec),
        constants=dict(constants or {}),
    )
