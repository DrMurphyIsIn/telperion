"""Rational-function identity emitter — `lhs = rhs` over ℚ on a ray.

Crystallizes the shape hand-rolled by the knapsack_sos Gram-bridge generator
(2026-08-20): identities between rational functions of one variable whose
denominators factor into rational-rooted linear factors, valid on a ray
`c0 < n` that keeps every factor nonzero.  The certificate is exact sympy
cancellation (`lhs − rhs = 0` as a rational function) plus the root audit
(every denominator root ≤ c0); the emitted Lean is the field_simp spine:

    theorem <name> : ∀ n : ℚ, (c0 : ℚ) < n → lhs = rhs := by
      intro n hn
      have h_i : n - a_i ≠ 0 := ne_of_gt (by linarith)   -- per root a_i
      field_simp
      all_goals ring

(`all_goals ring` because field_simp closes trivial instances outright —
the 2026-08-20 footgun.)  REFUSALS: a non-identity (nonzero cancellation);
a denominator root above the ray bound; a non-linear or irrational-rooted
denominator factor (outside this emitter's contract).

EXTENSION (2026-10-01): a spec returning a ``dict`` selects the MULTIVARIATE mode
(``∀ x y : ℚ, c_x < x → c_y < y → lhs = rhs`` by `field_simp; ring`, every denominator
atom certified positive on the box) or the MINIMAL-POLYNOMIAL mode (``∀ t : ℝ, m t = 0 →
lhs = rhs`` by `linear_combination q * h`, m monic irreducible over ℚ, plus the instance at
the real root of a quadratic m); see the section at the end of this module and
docs/EMITTER_EXTENSIONS_BUNDLE_DESIGN_2026-10-01.md.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean


def _render(expr) -> str:
    """Structure-preserving Lean renderer: canonicalization is the PROOF's
    job (field_simp/ring); the STATEMENT must keep the user's two shapes
    distinct (the nonvacuity gate rejects the canonicalized X = X collapse)."""
    if isinstance(expr, sp.Symbol):
        return str(expr)
    if isinstance(expr, sp.Integer):
        return str(expr) if expr >= 0 else f"(-{-expr})"
    if isinstance(expr, sp.Rational):
        return f"({_render(sp.Integer(expr.p))} / {_render(sp.Integer(expr.q))})"
    if isinstance(expr, sp.Add):
        return "(" + " + ".join(_render(a) for a in expr.args) + ")"
    if isinstance(expr, sp.Pow):
        base, exp = expr.args
        if exp == -1:
            return f"(1 / {_render(base)})"
        if isinstance(exp, sp.Integer) and exp < -1:
            return f"(1 / {_render(base)} ^ {-int(exp)})"
        if isinstance(exp, sp.Integer) and exp > 0:
            return f"{_render(base)} ^ {int(exp)}"
        raise ValueError(f"unsupported exponent {exp} in {expr}")
    if isinstance(expr, sp.Mul):
        num, den = [], []
        for a in expr.args:
            if isinstance(a, sp.Pow) and isinstance(a.args[1], sp.Integer) \
                    and a.args[1] < 0:
                den.append(a.args[0] if a.args[1] == -1
                           else sp.Pow(a.args[0], -a.args[1]))
            elif isinstance(a, sp.Rational) and not isinstance(a, sp.Integer):
                num.append(sp.Integer(a.p))
                den.append(sp.Integer(a.q))
            else:
                num.append(a)
        num_s = " * ".join(_render(a) for a in num) if num else "1"
        if not den:
            return f"({num_s})"
        den_s = " * ".join(_render(a) for a in den)
        return f"(({num_s}) / ({den_s}))"
    raise ValueError(f"unsupported node {type(expr).__name__} in {expr}")


def _split_frac(expr):
    """Top-level (numerator-args, denominator-atoms) decomposition mirroring
    the renderer's Mul flattening.  Denominator atoms are the bases of
    negative powers (with multiplicity via repeated listing for powers)."""
    num, den = [], []
    args = expr.args if isinstance(expr, sp.Mul) else (expr,)
    for a in args:
        if isinstance(a, sp.Pow) and isinstance(a.args[1], sp.Integer) \
                and a.args[1] < 0:
            den.extend([a.args[0]] * int(-a.args[1]))
        elif isinstance(a, sp.Rational) and not isinstance(a, sp.Integer):
            num.append(sp.Integer(a.p))
            den.append(sp.Integer(a.q))
        else:
            num.append(a)
    return num, den


def _assert_no_variable_division(parts, name):
    """Refuse variable denominators hiding below the top level (outside the
    cross-multiplication contract)."""
    for part in parts:
        for sub in sp.preorder_traversal(part):
            if isinstance(sub, sp.Pow) and isinstance(sub.args[1], sp.Integer) \
                    and sub.args[1] < 0 and sub.args[0].free_symbols:
                raise ValueError(
                    f"rational_identity instance '{name}' REFUSED: variable "
                    f"denominator {sub.args[0]} below the top level — outside "
                    "the cross-multiplication contract (restructure as a "
                    "single top-level fraction)")


def _den_atoms(expr, out):
    """Collect non-numeric denominator atom subexpressions (renderer-aligned):
    the exact objects whose ne-zero facts field_simp will need."""
    if isinstance(expr, sp.Pow) and isinstance(expr.args[1], sp.Integer) \
            and expr.args[1] < 0:
        base = expr.args[0]
        if base.free_symbols:
            out.append(base)
        _den_atoms(base, out)
        return
    if isinstance(expr, (sp.Add, sp.Mul, sp.Pow)):
        for a in expr.args:
            _den_atoms(a, out)


from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _denominator_roots(expr, sym):
    """Rational roots of the linear factors of expr's denominator; refuse rest."""
    _num, den = sp.fraction(sp.together(expr))
    roots = []
    for factor, _mult in sp.factor_list(den)[1]:
        poly = sp.Poly(factor, sym)
        if poly.total_degree() == 0:
            continue
        if poly.total_degree() != 1:
            raise ValueError(
                f"denominator factor {factor} is not linear in {sym}")
        a, b = poly.all_coeffs()
        root = sp.Rational(-b, a) if a != 0 else None
        if root is None:
            raise ValueError(f"degenerate denominator factor {factor}")
        roots.append(sp.nsimplify(root))
    return roots


def certify_rational_identity_point(family, pt, name):
    """Certify one rational identity: (CertifiedInstance, n_checks).

    A spec returning a ``dict`` selects an extension mode (2026-10-01): multivariate
    (``{"lhs", "rhs", "domain"}``) or modulo a minimal polynomial (``{"lhs", "rhs",
    "modulus"}``); the original ``(lhs, rhs, c0)`` tuple keeps the univariate ray path."""
    raw = family.special[1](pt)
    if isinstance(raw, dict):
        raw = dict(raw)
        syms = tuple(raw.pop("symbols", family.symbols))
        cert = extended_identity_certificate(symbols=syms, **raw)
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
        return inst, cert.n_checks
    lhs, rhs, c0 = raw
    lhs, rhs = sp.sympify(lhs), sp.sympify(rhs)
    c0 = sp.Rational(sp.sympify(c0))
    syms = tuple(family.symbols)
    if len(syms) != 1:
        raise ValueError("rational_identity families are univariate (one symbol)")
    sym = syms[0]

    diff = sp.cancel(sp.together(lhs - rhs))
    if diff != 0:
        raise ValueError(
            f"rational_identity instance '{name}' REFUSED: lhs − rhs does not "
            f"cancel to 0 (got {diff}) — not an identity")
    checks = 1

    roots = sorted(set(_denominator_roots(lhs, sym) + _denominator_roots(rhs, sym)))
    for a in roots:
        if not a.is_rational:
            raise ValueError(
                f"rational_identity instance '{name}' REFUSED: irrational "
                f"denominator root {a}")
        if a > c0:
            raise ValueError(
                f"rational_identity instance '{name}' REFUSED: denominator root "
                f"{a} exceeds the ray bound {c0} — the identity's domain does "
                "not contain the claimed ray")
        checks += 1

    for side in (lhs, rhs):
        num, _den = _split_frac(side)
        _assert_no_variable_division(num, name)
        checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(lhs, rhs, c0, roots),
    )
    return inst, checks


@dataclass
class RationalIdentityEmitter(Emitter):
    """Emit `∀ n : ℚ, c0 < n → lhs = rhs` via ne-zero haves + field_simp + ring."""

    def __post_init__(self):
        self.kind = "rational_identity"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        syms = tuple(fam.family.symbols)
        sym = syms[0] if syms else None
        lines: list[str] = []
        n_thm = 0
        root_emitted: set = set()
        for inst in fam.instances:
            if isinstance(inst.payload, ExtendedIdentityCert):
                text, k = _emit_extended(inst.payload, inst.lean_name, root_emitted)
                lines.append(text)
                n_thm += k
                continue
            lhs, rhs, c0, roots = inst.payload  # type: ignore[misc]
            lhs_s = _render(lhs)
            rhs_s = _render(rhs)
            c0_s = expr_lean(sp.Rational(c0), (sym,))
            haves = []
            chains = []
            for tag, side in (("L", lhs), ("R", rhs)):
                _num, den = _split_frac(side)
                var_atoms = [a for a in den if a.free_symbols]
                for i, a in enumerate(var_atoms):
                    haves.append(
                        f"  have h{tag}{i} : ({_render(a)} : ℚ) ≠ 0 := "
                        f"ne_of_gt (by linarith)\n")
                if not den:
                    chains.append(None)
                else:
                    chain = None
                    j = 0
                    for a in den:
                        piece = (f"h{tag}{j}" if a.free_symbols
                                 else f"(by norm_num : ({_render(a)} : ℚ) ≠ 0)")
                        if a.free_symbols:
                            j += 1
                        chain = piece if chain is None \
                            else f"(mul_ne_zero {chain} {piece})"
                    chains.append(chain)
            hL, hR = chains
            if hL and hR:
                spine = f"  rw [div_eq_div_iff {hL} {hR}]\n  ring\n"
            elif hL:
                spine = f"  rw [div_eq_iff {hL}]\n  ring\n"
            elif hR:
                spine = f"  rw [eq_div_iff {hR}]\n  ring\n"
            else:
                spine = "  ring\n"
            lines.append(
                f"-- {inst.lean_name}: rational-function identity on the ray "
                f"{c0} < {sym} (denominator roots {[str(a) for a in roots]}).\n"
                f"theorem {inst.lean_name} : ∀ {sym} : ℚ, ({c0_s} : ℚ) < {sym} → "
                f"{lhs_s} = {rhs_s} := by\n"
                f"  intro {sym} hn\n"
                f"{''.join(haves)}"
                f"{spine}")
            n_thm += 1
        return "\n".join(lines), n_thm


def rational_identity_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a rational-identity family (kind='rational_identity').

    spec: ``pt -> (lhs, rhs, c0)`` — the claimed identity ``lhs = rhs`` of
    rational functions of the single family symbol, on the ray ``c0 < n``;
    or (extension, 2026-10-01) ``pt -> dict`` for the multivariate mode
    ``{"lhs", "rhs", "domain": {sym: c}}`` (rays ``c < sym`` per symbol) or the
    minimal-polynomial mode ``{"lhs", "rhs", "modulus": m}`` (``m`` an irreducible
    monic polynomial in the FIRST family symbol; the identity holds modulo ``m``).
    A dict may carry ``"symbols"`` to override the family symbols per instance.
    """
    if len(tuple(symbols)) < 1:
        raise ValueError("rational_identity families require at least one symbol "
                         "(exactly one for the univariate ray form)")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("rational_identity", spec),
        constants=constants or {},
    )


# ---------------------------------------------------------------------------
# Extension (2026-10-01): multivariate identities and identities modulo a
# minimal polynomial.
# ---------------------------------------------------------------------------
#
# MULTIVARIATE.  ``lhs = rhs`` of rational functions in several symbols, on the open box
# of rays ``c_v < v``.  Certificate: exact cancellation ``lhs - rhs = 0`` plus, for every
# denominator atom (the renderer's own subterms, so `field_simp` matches its `≠ 0`
# hypotheses syntactically), a positivity audit on the box: the atom is AFFINE with every
# coefficient of ``D(c + t)`` nonnegative and not all zero (then `linarith` proves
# ``0 < D`` from the rays), or POSITIVITY-EVIDENT (a positive constant plus positive
# multiples of even-power monomials; `positivity` proves it).  Anything else is refused.
# Lean: ``∀ x y : ℚ, c_x < x → c_y < y → lhs = rhs`` by the `≠ 0` haves, `field_simp`,
# `ring`.
#
# MODULO A MINIMAL POLYNOMIAL.  ``lhs ≡ rhs (mod m)`` where ``m`` is a monic polynomial in
# the first family symbol, irreducible over ℚ (so ℚ[t]/(m) is the number field).  lhs/rhs
# are polynomials (any other family symbols are free parameters).  Certificate: exact
# division ``lhs - rhs = q · m`` with zero remainder.  Lean: ``∀ t : ℝ, m(t) = 0 → lhs =
# rhs`` (hence for EVERY root of m in ℝ), closed by ``linear_combination q * h``; for a
# quadratic m with non-square discriminant d the statement is also instantiated at the
# real root ``(-b + √d)/2`` (one root lemma per modulus, by ``Real.sq_sqrt``).  Example:
# in ℚ[x]/(x² − x − 1) = ℚ(√5), ``x^n = F_n x + F_{n-1}``.



@dataclass(frozen=True)
class ExtendedIdentityCert:
    """A verified extension-mode identity (all fields exact).

    ``mode`` is "multivariate" or "modular".  ``symbols`` the bound symbols in order;
    ``domain`` (multivariate) the per-symbol ray bounds; ``atoms`` the denominator atoms
    with their positivity route ("linarith" / "positivity"); ``modulus`` (modular) the
    minimal polynomial and ``quotient`` the exact cofactor ``(lhs - rhs) / modulus``.
    ``checked`` is False only for hand-forged negative controls."""

    mode: str
    lhs: object
    rhs: object
    symbols: tuple
    domain: tuple = ()          # ((sym, c), ...)
    atoms: tuple = ()           # ((atom_expr, route), ...)
    modulus: object = None
    quotient: object = None
    n_checks: int = 1
    checked: bool = True


def _atom_route(D, syms, dom):
    """How to prove ``0 < D`` on the open box ``c_v < v``: "linarith", "positivity", or
    None (refused)."""
    P = sp.Poly(sp.expand(D), *syms)
    if P.total_degree() <= 1:
        shifted = sp.Poly(sp.expand(D.subs({v: v + dom[v] for v in syms},
                                              simultaneous=True)), *syms)
        cs = [sp.Rational(c) for c in shifted.coeffs()]
        if cs and all(c >= 0 for c in cs) and any(c > 0 for c in cs):
            return "linarith"
        return None
    const = P.coeff_monomial(1)
    ok = const > 0
    for mon, c in zip(P.monoms(), P.coeffs()):
        if all(e == 0 for e in mon):
            continue
        if not (c > 0 and all(e % 2 == 0 for e in mon)):
            ok = False
    return "positivity" if ok else None


def extended_identity_certificate(*, symbols, lhs, rhs, domain=None, modulus=None,
                                  check: bool = True) -> ExtendedIdentityCert:
    """Build and EXACTLY verify an extension-mode identity (see the section comment).

    ``check=False`` is for hand-forged negative controls ONLY: the identity / remainder /
    irreducibility checks are skipped (the cofactor is still the exact polynomial quotient,
    so a false identity leaves a nonzero remainder the kernel's `ring` cannot close)."""
    syms = tuple(symbols)
    if not syms:
        raise ValueError("REFUSED: the extension modes need at least one symbol")
    L = sp.sympify(lhs)
    R = sp.sympify(rhs)
    for side in (L, R):
        if side.atoms(sp.Float):
            raise ValueError(f"REFUSED: {side} contains a float")
        extra = side.free_symbols - set(syms)
        if extra:
            raise ValueError(f"REFUSED: {side} uses symbols {sorted(map(str, extra))} not "
                             f"declared by the family")
    if (domain is None) == (modulus is None):
        raise ValueError("REFUSED: give exactly one of domain= (multivariate) or "
                         "modulus= (minimal polynomial)")
    if modulus is not None:
        t = syms[0]
        m = sp.Poly(sp.sympify(modulus), t, domain="QQ")
        if m.degree() < 1 or m.LC() != 1:
            raise ValueError(f"REFUSED: modulus {m.as_expr()} must be monic of degree >= 1 "
                             f"in {t}")
        if check and not m.is_irreducible:
            raise ValueError(f"REFUSED: modulus {m.as_expr()} is reducible over Q (not a "
                             f"minimal polynomial)")
        for side in (L, R):
            if sp.fraction(sp.together(side))[1].free_symbols:
                raise ValueError(f"REFUSED: {side} has a variable denominator (the modular "
                                 f"mode takes polynomials)")
        diff = sp.Poly(sp.expand(L - R), *syms, domain="QQ")
        q, r = sp.div(diff, sp.Poly(m.as_expr(), *syms, domain="QQ"))
        if check and not r.is_zero:
            raise ValueError(f"REFUSED: lhs - rhs is not divisible by the modulus "
                             f"{m.as_expr()} (remainder {r.as_expr()}) -- not an identity "
                             f"in Q[{t}]/({m.as_expr()})")
        return ExtendedIdentityCert(mode="modular", lhs=L, rhs=R, symbols=syms,
                                    modulus=m.as_expr(), quotient=q.as_expr(), n_checks=3,
                                    checked=check)
    # multivariate
    dom = {}
    for v in syms:
        if v not in domain and str(v) not in domain:
            raise ValueError(f"REFUSED: no ray bound for symbol {v}")
        c = domain[v] if v in domain else domain[str(v)]
        if isinstance(c, float):
            raise ValueError(f"REFUSED: ray bound {c!r} is a float")
        dom[v] = sp.Rational(sp.sympify(c))
    if check:
        diff = sp.cancel(sp.together(L - R))
        if diff != 0:
            raise ValueError(f"REFUSED: lhs - rhs does not cancel to 0 (got {diff}) -- not "
                             f"an identity")
    raw: list = []
    for side in (L, R):
        _den_atoms(side, raw)
    atoms = []
    seen = set()
    for a in raw:
        key = _render(a)
        if key in seen:
            continue
        seen.add(key)
        route = _atom_route(a, syms, dom)
        if route is None:
            raise ValueError(f"REFUSED: cannot certify the denominator {a} positive on the "
                             f"box {{{', '.join(f'{dom[v]} < {v}' for v in syms)}}} (affine "
                             f"with nonnegative shifted coefficients, or a positive constant "
                             f"plus even-power monomials, are supported)")
        atoms.append((a, route))
    return ExtendedIdentityCert(mode="multivariate", lhs=L, rhs=R, symbols=syms,
                                domain=tuple((v, dom[v]) for v in syms), atoms=tuple(atoms),
                                n_checks=1 + len(atoms), checked=check)


def _rq(q) -> str:
    q = sp.Rational(q)
    return f"({q.p} : ℝ)" if q.q == 1 else f"({q.p} / {q.q} : ℝ)"


def _rqq(q) -> str:
    q = sp.Rational(q)
    return f"{q.p}" if q.q == 1 else f"{q.p} / {q.q}"


def _poly_real(e, syms, names=None) -> str:
    """A polynomial with rational coefficients as Lean ℝ text, deterministic order (total
    degree, then exponent tuple).  ``names`` maps a symbol to the Lean text standing for it
    (default: its name), so a root can be substituted without string surgery."""
    names = dict(names or {})
    P = sp.Poly(sp.expand(e), *syms, domain="QQ")
    terms = []
    for mon, c in sorted(zip(P.monoms(), P.coeffs()), key=lambda t: (sum(t[0]), t[0])):
        parts = []
        for v, k in zip(syms, mon):
            if k:
                base = names.get(v, str(v))
                parts.append(base if k == 1 else f"{base} ^ {k}")
        if c != 1 or not parts:
            parts.insert(0, _rq(c))
        terms.append(" * ".join(parts))
    return "(" + (" + ".join(terms) if terms else "(0 : ℝ)") + ")"


def _root_name(m, t) -> str:
    P = sp.Poly(m, t)
    tag = "_".join(str(c).replace("-", "m").replace("/", "d") for c in P.all_coeffs())
    return f"minpoly_root_{tag}"


def _emit_extended(c: ExtendedIdentityCert, nm: str, root_emitted: set) -> tuple[str, int]:
    syms = c.symbols
    if c.mode == "multivariate":
        binders = " ".join(str(v) for v in syms)
        hyps = " → ".join(f"({_rqq(cv)} : ℚ) < {v}" for v, cv in c.domain)
        names = " ".join(f"h{v}" for v in syms)
        haves = []
        for i, (a, route) in enumerate(c.atoms):
            tac = "linarith" if route == "linarith" else "positivity"
            haves.append(f"  have hD{i} : ({_render(a)} : ℚ) ≠ 0 := ne_of_gt (by {tac})\n")
        text = (f"-- {nm}: rational identity on a box (multivariate extension, 2026-10-01): "
                f"{', '.join(f'{cv} < {v}' for v, cv in c.domain)}\n"
                f"-- ({len(c.atoms)} denominator atoms certified positive there).\n"
                f"theorem {nm} : ∀ {binders} : ℚ, {hyps} →\n"
                f"    {_render(c.lhs)} = {_render(c.rhs)} := by\n"
                f"  intro {binders} {names}\n"
                f"{''.join(haves)}"
                f"  field_simp\n"
                f"  ring\n")
        return text, 1
    # modular
    t = syms[0]
    others = syms[1:]
    m_l = _poly_real(c.modulus, (t,))
    q_l = _poly_real(c.quotient, syms)
    lhs_l = _poly_real(c.lhs, syms)
    rhs_l = _poly_real(c.rhs, syms)
    binders = " ".join(str(v) for v in syms)
    out = []
    n = 1
    out.append(f"-- {nm}: identity modulo the minimal polynomial {sp.sstr(c.modulus)} "
               f"(extension, 2026-10-01):\n"
               f"-- lhs - rhs = q * m exactly, so lhs = rhs at every root of m.\n"
               f"theorem {nm} : ∀ {binders} : ℝ, {m_l} = 0 →\n"
               f"    {lhs_l} = {rhs_l} := by\n"
               f"  intro {binders} h\n"
               f"  linear_combination {q_l} * h\n")
    P = sp.Poly(c.modulus, t)
    if P.degree() == 2 and not others:
        _, b, cc = (sp.Rational(x) for x in P.all_coeffs())
        d = b * b - 4 * cc
        rn = _root_name(c.modulus, t)
        root = f"(({_rq(-b)} + Real.sqrt {_rq(d)}) / 2)"
        if rn not in root_emitted:
            root_emitted.add(rn)
            out.insert(0, f"/-- The real root `(-b + √d)/2` of {sp.sstr(c.modulus)} "
                          f"(d = {d}). -/\n"
                          f"theorem {rn} : {_poly_real(c.modulus, (t,), {t: root})}"
                          f" = 0 := by\n"
                          f"  have hs : Real.sqrt {_rq(d)} ^ 2 = {_rq(d)} := "
                          f"Real.sq_sqrt (by norm_num)\n"
                          f"  linear_combination (1 / 4 : ℝ) * hs\n")
            n += 1
        out.append(f"/-- `{nm}` at the real root `(-b + √d)/2`. -/\n"
                   f"theorem {nm}_at_root :\n"
                   f"    {_poly_real(c.lhs, syms, {t: root})} = "
                   f"{_poly_real(c.rhs, syms, {t: root})} :=\n"
                   f"  {nm} _ {rn}\n")
        n += 1
    return "\n".join(out), n
