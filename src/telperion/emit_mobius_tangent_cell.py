"""mobius_tangent_cell emitter -- a search-free TWO-EVALUATION certificate for one-variable
inequalities "linear + concave logs + one Mobius term <= 0" on a rational interval.

conjecture1_proved = False.  Nothing in this module bears on the Riemann Hypothesis or on
the Brualdi-Goldwasser conjecture: it certifies elementary one-variable real inequalities
with rational data.  Downstream consumers state their own scope.

Acknowledgement: the tangent-line cell technique (concave witnesses, a Mobius term, a convex
majorant checked at the two cell endpoints) is taken from a draft communicated by Professor
John L. Goldwasser ("The maximum Laplacian ratio of a tree for all n >= 303: concave
witnesses and one-variable certificates", 28 Sep 2026, Lemma 3.3; author: his London
colleague, name to be added).  Nothing from the draft's data is reproduced here.

THE SHAPE
---------
    F(x) = a + b x + sum_i kappa_i log(alpha_i + beta_i x) + sigma / (B + A x)  <=  0
    for all x in [P, Q],

with every coefficient rational, kappa_i > 0, and alpha_i + beta_i x > 0, B + A x > 0 on the
whole interval (both are affine, so the two endpoints decide it).  The problem can also be
given as two sides `lhs <= rhs` (sympy expressions in one symbol); `F = lhs - rhs` is then
split EXACTLY into the shape above (`sp.apart`), and a refusal is raised when it does not
fit (a log with a negative coefficient, a non-affine log argument, a rational part that is
not "affine + one simple pole").

THE METHOD (Lemma 3.3 of the source), per cell [p, q] with a rational tangent point t
------------------------------------------------------------------------------------
* each log is concave, so with u_i = alpha_i + beta_i t and any rational H_i >= log u_i,
      kappa_i log(alpha_i + beta_i x) <= kappa_i (H_i + (alpha_i + beta_i x - u_i) / u_i)
  (Mathlib: `Real.log_le_sub_one_of_pos` at y/u, plus `Real.log_div`);
* the Mobius term s/w, w = B + A x > 0, is CONVEX when sigma >= 0 and is left alone; when
  sigma < 0 it is CONCAVE and is replaced by its tangent at c = B + A t:
      sigma / w <= sigma / c - sigma (w - c) / c^2
  (exactly: the difference is -sigma (w - c)^2 / (w c^2) >= 0);
* the resulting majorant Psi_t(x) = m + k x [+ sigma/(B + A x) when sigma >= 0] is convex on
  the cell, so Psi_t(p) <= 0 and Psi_t(q) <= 0 give F <= Psi_t <= 0 on all of [p, q].  The
  convex endpoint lemma is proved from the Cauchy-Schwarz form of the convexity of 1/w
  along the chord: (u + v)^2 wp wq <= (u wq + v wp)(u wp + v wq), u = q - x, v = x - p.

log u_i is bounded by an exact rational H_i: u_i = 2^n v with v in [2/3, 4/3), and
    log u_i = n log 2 + log v <= n * 0.6931471808 + (-S + r)       (n >= 0)
(`Real.log_two_lt_d9`; for n < 0 the lower Mathlib bound `Real.log_two_gt_d9` is used),
with (S, r) the exact order-N Taylor box of `Real.abs_log_sub_add_sum_range_le` at
x = 1 - v, |x| <= 1/3 -- the enclosure_tree log route.  The emitter picks the LEAST order
N whose H makes the two endpoint checks pass.  u = 1 is `Real.log_one` (H = 0).

Everything the kernel then checks is exact rational arithmetic (`norm_num`) plus one
`linarith` per cell.  The untrusted generator bisects [P, Q] into cells (tangent point
candidates: midpoint, then the quarter points, then the endpoints) until every cell passes,
and emits one theorem per cell plus a union theorem over [P, Q] by a `le_or_lt` chain at the
shared breakpoints (the cells tile [P, Q] with no gap: certify checks q_j = p_(j+1)).

HONEST SCOPE AND LIMITS
-----------------------
* Only `<= 0` (non-strict) is stated.
* The majorant loses a (x - t)^2 term per log, so an inequality that is TIGHT to order >= 2
  at a point (e.g. a Pade bound at its expansion point) cannot be certified on any cell
  containing that point: bisection there never terminates and the generator REFUSES at the
  depth cap.  Stay a positive distance away from such points (the dogfood does, and says so).
* kappa_i < 0 (a convex log) does not fit the template and is REFUSED, as is a sign change
  of B + A x or of a log argument on the interval, and a Mobius pole inside the interval.
* One Mobius term (the `sp.apart` split must produce at most one simple pole).

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily  # noqa: F401
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


#: Mathlib's `Real.log_two_gt_d9` / `Real.log_two_lt_d9` (both strict).
LOG2_LO = Fraction(6931471803, 10 ** 10)
LOG2_HI = Fraction(6931471808, 10 ** 10)
#: Taylor orders for the `log u <= H` constant bound.
MAX_LOG_ORDER = 40
#: `H` is rounded UP to a multiple of 10^-H_DIGITS (short literals; sound since H only grows).
H_DIGITS = 15
#: bisection limits of the untrusted generator.
DEFAULT_MAX_DEPTH = 14
DEFAULT_MAX_CELLS = 256


class MobiusTangentRefusal(ValueError):
    """A hypothesis of the template fails, or no certificate was found; message starts REFUSED."""


def _refuse(msg: str) -> MobiusTangentRefusal:
    return MobiusTangentRefusal(f"REFUSED: {msg}")


def _Q(v, what: str) -> Fraction:
    """An exact rational, refusing floats (a float is not the rational it prints as)."""
    if isinstance(v, bool):
        raise _refuse(f"{what} must be rational, got a bool")
    if isinstance(v, float):
        raise _refuse(f"{what} = {v!r} is a float; pass an exact rational (int, Fraction, "
                      "sympy Rational or 'n/d' string)")
    if isinstance(v, Fraction):
        return v
    if isinstance(v, int):
        return Fraction(v)
    if isinstance(v, str):
        try:
            return Fraction(v)
        except ValueError as e:
            raise _refuse(f"{what} = {v!r} is not a rational literal") from e
    s = sp.sympify(v)
    if not s.is_Rational:
        raise _refuse(f"{what} = {v!r} is not an exact rational")
    return Fraction(int(s.p), int(s.q))


def _S(f: Fraction) -> sp.Rational:
    return sp.Rational(f.numerator, f.denominator)


# --- the problem --------------------------------------------------------------------

@dataclass(frozen=True)
class LogTerm:
    """`kappa * log(alpha + beta x)`, kappa > 0."""
    kappa: Fraction
    alpha: Fraction
    beta: Fraction


@dataclass(frozen=True)
class MobiusTangentProblem:
    """`F(x) = a + b x + sum kappa_i log(alpha_i + beta_i x) + sigma / (B + A x) <= 0` on
    `[p, q]`.  `sigma = 0` means no Mobius term (then `A`, `B` are ignored and must be 0, 1).
    `sides` optionally records the two sympy sides `(lhs, rhs, var)` with `F = lhs - rhs`."""
    a: Fraction
    b: Fraction
    logs: tuple
    sigma: Fraction
    B: Fraction
    A: Fraction
    p: Fraction
    q: Fraction
    sides: tuple | None = field(default=None, compare=False)

    def value(self, x: Fraction, log=None) -> float:
        """Float evaluation (generator diagnostics only; never used to certify)."""
        import math
        log = log or math.log
        v = float(self.a + self.b * x)
        for lt in self.logs:
            v += float(lt.kappa) * log(float(lt.alpha + lt.beta * x))
        if self.sigma != 0:
            v += float(self.sigma / (self.B + self.A * x))
        return v


def mobius_tangent_problem(*, a=0, b=0, logs=(), sigma=0, B=1, A=0, p, q,
                           sides=None) -> MobiusTangentProblem:
    """Validate the template's hypotheses EXACTLY and build the problem.  Refuses: floats,
    `p >= q`, no log term, `kappa <= 0`, a log argument or `B + A x` not positive at both
    endpoints (they are affine, so this is positivity on the whole interval)."""
    a, b = _Q(a, "a"), _Q(b, "b")
    p, q = _Q(p, "p"), _Q(q, "q")
    sigma, B, A = _Q(sigma, "sigma"), _Q(B, "B"), _Q(A, "A")
    if not p < q:
        raise _refuse(f"degenerate interval [{p}, {q}] (need p < q)")
    terms = []
    for i, lt in enumerate(logs):
        if isinstance(lt, LogTerm):
            kappa, alpha, beta = lt.kappa, lt.alpha, lt.beta
        else:
            kappa, alpha, beta = lt
        kappa = _Q(kappa, f"kappa_{i}")
        alpha = _Q(alpha, f"alpha_{i}")
        beta = _Q(beta, f"beta_{i}")
        if kappa < 0:
            raise _refuse(f"kappa_{i} = {kappa} < 0: kappa log(.) is then CONVEX and has no "
                          "tangent majorant (the template needs every log term concave)")
        if kappa == 0:
            raise _refuse(f"kappa_{i} = 0: drop the vacuous log term")
        for end in (p, q):
            if not alpha + beta * end > 0:
                raise _refuse(f"log argument {alpha} + {beta} x = {alpha + beta * end} is not "
                              f"> 0 at x = {end}")
        terms.append(LogTerm(kappa, alpha, beta))
    if not terms:
        raise _refuse("no log term: the shape is then rational; use a rational emitter")
    if sigma == 0:
        B, A = Fraction(1), Fraction(0)
    else:
        for end in (p, q):
            if not B + A * end > 0:
                raise _refuse(f"Mobius denominator {B} + {A} x = {B + A * end} is not > 0 at "
                              f"x = {end} (the sign of B + A x must not change on the cell)")
    return MobiusTangentProblem(a, b, tuple(terms), sigma, B, A, p, q, sides)


def problem_from_sides(lhs, rhs, var, p, q) -> MobiusTangentProblem:
    """See `_problem_from_sides`; sympy polynomial errors become refusals."""
    try:
        return _problem_from_sides(lhs, rhs, var, p, q)
    except (sp.PolynomialError, sp.GeneratorsNeeded) as e:
        raise _refuse(f"lhs - rhs is not of the template shape in {var}: {e}") from e


def _problem_from_sides(lhs, rhs, var, p, q) -> MobiusTangentProblem:
    """Split `lhs - rhs` EXACTLY into the template, or refuse.

    Log atoms must be `c * log(alpha + beta var)` with rational c, alpha, beta (c > 0 after
    moving everything to the left); the remaining rational function must be
    `affine + sigma / (B + A var)` after `sp.apart` (one simple pole at most)."""
    x = var
    F = sp.expand(sp.sympify(lhs) - sp.sympify(rhs))
    logs, rest = [], sp.Integer(0)
    for term in sp.Add.make_args(F):
        if not term.has(sp.log):
            rest += term
            continue
        coeff, atoms = sp.Integer(1), []
        for fac in sp.Mul.make_args(term):
            if fac.has(sp.log):
                atoms.append(fac)
            else:
                coeff *= fac
        if len(atoms) != 1 or not isinstance(atoms[0], sp.log) or not coeff.is_Rational:
            raise _refuse(f"log term {term} is not (rational) * log(affine)")
        arg = sp.expand(atoms[0].args[0])
        pa = sp.Poly(arg, x)
        if pa.degree() > 1 or not all(c.is_Rational for c in pa.all_coeffs()):
            raise _refuse(f"log argument {arg} is not affine in {x} with rational coefficients")
        beta, alpha = (pa.all_coeffs() if pa.degree() == 1 else [sp.Integer(0),
                                                                  pa.all_coeffs()[0]])
        logs.append((coeff, alpha, beta))
    rest = sp.apart(sp.together(rest), x) if rest != 0 else rest
    a = b = sigma = sp.Integer(0)
    B, A = sp.Integer(1), sp.Integer(0)
    n_poles = 0
    for term in sp.Add.make_args(rest):
        if term == 0:
            continue
        num, den = sp.fraction(sp.together(term))
        pd, pn = sp.Poly(den, x), sp.Poly(num, x)
        if pd.degree() == 0:
            if pn.degree() > 1:
                raise _refuse(f"polynomial part {term} has degree > 1 in {x}")
            cs = [c / pd.LC() for c in pn.all_coeffs()]
            if not all(c.is_Rational for c in cs):
                raise _refuse(f"non-rational coefficient in {term}")
            if len(cs) == 2:
                b += cs[0]
                a += cs[1]
            else:
                a += cs[0]
            continue
        if pd.degree() != 1 or pn.degree() != 0:
            raise _refuse(f"rational part {term} is not a single simple pole sigma/(B + A x)")
        n_poles += 1
        if n_poles > 1:
            raise _refuse("more than one Mobius term (the template supports one simple pole)")
        d1, d0 = pd.all_coeffs()
        s = pn.all_coeffs()[0]
        sigma, B, A = s, d0, d1
    pF, qF = _Q(p, "p"), _Q(q, "q")
    # normalise so the denominator is POSITIVE on the interval (its sign moves to sigma)
    if sigma != 0:
        if B + A * _S(pF) < 0 and B + A * _S(qF) < 0:
            sigma, B, A = -sigma, -B, -A
    return mobius_tangent_problem(a=a, b=b, logs=logs, sigma=sigma, B=B, A=A, p=pF, q=qF,
                                  sides=(sp.sympify(lhs), sp.sympify(rhs), var))


# --- the certificate ----------------------------------------------------------------

@dataclass(frozen=True)
class LogConstBound:
    """`log u <= H`, u = 2^n v (n may be negative), v in [2/3, 4/3), from the order-`order`
    Taylor box at x = 1 - v and Mathlib's log 2 bound.  `order = 0` with `u = 1` is
    `Real.log_one` (H = 0)."""
    u: Fraction
    n: int
    v: Fraction
    order: int
    H: Fraction


@dataclass(frozen=True)
class MobiusCell:
    """One cell [p, q] with tangent point t; `m + k x` is the linear part of the majorant
    (the Mobius term is kept when `mode == "convex"`, folded into m, k when `"tangent"`,
    absent when `"none"`).  `psi_p`, `psi_q` are the exact majorant endpoint values, both
    <= 0."""
    p: Fraction
    q: Fraction
    t: Fraction
    bounds: tuple      # one LogConstBound per log term
    mode: str
    m: Fraction
    k: Fraction
    psi_p: Fraction
    psi_q: Fraction


@dataclass(frozen=True)
class MobiusTangentCellCert:
    problem: MobiusTangentProblem
    cells: tuple

    @property
    def n_theorems(self) -> int:
        n_h = len({b.u for c in self.cells for b in c.bounds})
        return n_h + len(self.cells) + 1 + (1 if self.problem.sides is not None else 0)


def split_pow2(u: Fraction) -> tuple:
    """`u = 2^n v` with v in [2/3, 4/3)."""
    if u <= 0:
        raise _refuse(f"log argument {u} <= 0")
    n = 0
    v = u
    while v >= Fraction(4, 3):
        v /= 2
        n += 1
    while v < Fraction(2, 3):
        v *= 2
        n -= 1
    return n, v


def log_upper(u: Fraction, order: int) -> LogConstBound:
    """The exact rational `H >= log u` at Taylor order `order` (see the module docstring)."""
    if u == 1:
        return LogConstBound(u, 0, Fraction(1), 0, Fraction(0))
    n, v = split_pow2(u)
    x = 1 - v
    S = sum((x ** (i + 1) / (i + 1) for i in range(order)), Fraction(0))
    r = abs(x) ** (order + 1) / (1 - abs(x))
    H = -S + r + n * (LOG2_HI if n >= 0 else LOG2_LO)
    # round UP onto the 10^-H_DIGITS grid (sound: H only grows) to keep the literals short
    H = Fraction(-((-H.numerator * 10 ** H_DIGITS) // H.denominator), 10 ** H_DIGITS)
    return LogConstBound(u, n, v, order, H)


def cell_majorant(pr: MobiusTangentProblem, p: Fraction, q: Fraction, t: Fraction,
                  bounds) -> MobiusCell:
    """Build the cell's majorant data EXACTLY (no acceptance decision here)."""
    m, k = pr.a, pr.b
    for lt, bd in zip(pr.logs, bounds):
        u = lt.alpha + lt.beta * t
        if bd.u != u:
            raise _refuse(f"log bound is for u = {bd.u}, the tangent point gives u = {u}")
        m += lt.kappa * (bd.H - lt.beta * t / u)
        k += lt.kappa * lt.beta / u
    if pr.sigma == 0:
        mode = "none"
        psi_p, psi_q = m + k * p, m + k * q
    elif pr.sigma > 0:
        mode = "convex"
        psi_p = m + k * p + pr.sigma / (pr.B + pr.A * p)
        psi_q = m + k * q + pr.sigma / (pr.B + pr.A * q)
    else:
        mode = "tangent"
        c = pr.B + pr.A * t
        # sigma/c - sigma (B + A x - c)/c^2  =  [sigma/c - sigma (B - c)/c^2] - sigma A/c^2 x
        m += pr.sigma / c - pr.sigma * (pr.B - c) / c ** 2
        k += -pr.sigma * pr.A / c ** 2
        psi_p, psi_q = m + k * p, m + k * q
    return MobiusCell(p, q, t, tuple(bounds), mode, m, k, psi_p, psi_q)


def check_cell(pr: MobiusTangentProblem, cell: MobiusCell) -> None:
    """The exact acceptance test of ONE cell, re-derived from the problem (a certificate
    whose recorded numbers disagree with the recomputation is refused)."""
    if not (pr.p <= cell.p < cell.q <= pr.q):
        raise _refuse(f"cell [{cell.p}, {cell.q}] is not a nondegenerate sub-interval of "
                      f"[{pr.p}, {pr.q}]")
    if not cell.p <= cell.t <= cell.q:
        raise _refuse(f"tangent point {cell.t} is outside its cell [{cell.p}, {cell.q}]")
    if len(cell.bounds) != len(pr.logs):
        raise _refuse("one log bound per log term is required")
    for lt, bd in zip(pr.logs, cell.bounds):
        u = lt.alpha + lt.beta * cell.t
        if u <= 0:
            raise _refuse(f"tangent argument u = {u} <= 0")
        if not (0 <= bd.order <= MAX_LOG_ORDER):
            raise _refuse(f"log Taylor order {bd.order} outside 0..{MAX_LOG_ORDER}")
        if (bd.order == 0) != (u == 1):
            raise _refuse(f"order 0 (Real.log_one) is for u = 1 exactly, and only then "
                          f"(u = {u}, order {bd.order})")
        if bd != log_upper(u, bd.order):
            raise _refuse(f"log bound for u = {u} does not match its exact recomputation "
                          f"(claimed H = {bd.H})")
    if pr.sigma < 0 and not pr.B + pr.A * cell.t > 0:
        raise _refuse("Mobius tangent point outside the positive region")
    fresh = cell_majorant(pr, cell.p, cell.q, cell.t, cell.bounds)
    if fresh != cell:
        raise _refuse("cell data do not match the exact recomputation of the majorant")
    if cell.psi_p > 0 or cell.psi_q > 0:
        raise _refuse(f"majorant endpoint value > 0 on [{cell.p}, {cell.q}] "
                      f"(Psi(p) = {float(cell.psi_p):.3e}, Psi(q) = {float(cell.psi_q):.3e})")


def check_tiling(pr: MobiusTangentProblem, cells) -> None:
    """The cells cover [P, Q] with NO gap and no overlap: q_j = p_(j+1)."""
    if not cells:
        raise _refuse("no cells")
    if cells[0].p != pr.p or cells[-1].q != pr.q:
        raise _refuse(f"cells span [{cells[0].p}, {cells[-1].q}], not [{pr.p}, {pr.q}]")
    for c0, c1 in zip(cells, cells[1:]):
        if c0.q != c1.p:
            raise _refuse(f"gap or overlap between cells: {c0.q} != {c1.p}")


def _try_cell(pr: MobiusTangentProblem, p: Fraction, q: Fraction):
    """Untrusted search for ONE cell: tangent candidates x least passing Taylor order."""
    for t in (p + (q - p) / 2, p + (q - p) / 4, p + 3 * (q - p) / 4, p, q):
        us = [lt.alpha + lt.beta * t for lt in pr.logs]
        if pr.sigma < 0 and not pr.B + pr.A * t > 0:
            continue
        for order in range(1, MAX_LOG_ORDER + 1):
            bounds = [log_upper(u, order) for u in us]
            cell = cell_majorant(pr, p, q, t, bounds)
            if cell.psi_p <= 0 and cell.psi_q <= 0:
                return cell
            # a higher order only shrinks H by the Taylor remainder; stop once it is negligible
            if all(b.order == 0 for b in bounds):
                break
    return None


def mobius_tangent_cell_certificate(problem: MobiusTangentProblem, *, breakpoints=None,
                                    max_depth: int = DEFAULT_MAX_DEPTH,
                                    max_cells: int = DEFAULT_MAX_CELLS
                                    ) -> MobiusTangentCellCert:
    """Find and EXACTLY verify a cell certificate for `F <= 0` on [P, Q].

    Untrusted generation: bisect from [P, Q] (or start from the given interior
    `breakpoints`) until every cell passes.  Then every cell is re-checked from scratch
    (`check_cell`) and the tiling is checked (`check_tiling`).  Refuses when a cell still
    fails at `max_depth` halvings (typically: F is tight to order >= 2 inside it) or when
    more than `max_cells` cells are needed."""
    pr = problem
    pts = [pr.p] + sorted(_Q(b, "breakpoint") for b in (breakpoints or ())) + [pr.q]
    for u0, u1 in zip(pts, pts[1:]):
        if not u0 < u1:
            raise _refuse(f"breakpoints must be strictly increasing inside ({pr.p}, {pr.q})")
    stack = [(u0, u1, 0) for u0, u1 in zip(pts, pts[1:])][::-1]
    cells = []
    while stack:
        p, q, depth = stack.pop()
        cell = _try_cell(pr, p, q)
        if cell is not None:
            cells.append(cell)
            if len(cells) > max_cells:
                raise _refuse(f"more than {max_cells} cells needed")
            continue
        if depth >= max_depth:
            fp, fq = pr.value(p), pr.value(q)
            why = ("F > 0 there (float evaluation): the claim looks FALSE"
                   if max(fp, fq) > 0 else
                   "F is probably tight to order >= 2 there; the tangent-majorant template "
                   "cannot certify it")
            raise _refuse(f"cell [{p}, {q}] still fails after {max_depth} bisections "
                          f"(F({float(p):.6g}) = {fp:.3e}, F({float(q):.6g}) = {fq:.3e}): {why}")
        mid = p + (q - p) / 2
        stack.append((mid, q, depth + 1))
        stack.append((p, mid, depth + 1))
    cert = MobiusTangentCellCert(pr, tuple(cells))
    verify_certificate(cert)
    return cert


def verify_certificate(cert: MobiusTangentCellCert) -> None:
    """Layer-1 exact re-check of a whole certificate (tiling + every cell + the sides
    identity when present)."""
    pr = cert.problem
    check_tiling(pr, cert.cells)
    for c in cert.cells:
        check_cell(pr, c)
    if pr.sides is not None:
        lhs, rhs, x = pr.sides
        if sp.simplify(sp.expand(lhs - rhs) - F_sympy(pr, x)) != 0:
            raise _refuse("lhs - rhs is not identically the template F")
        _sides_theorem(pr, "_union", "_sides")      # refuses non-affine / sign-changing dens


def F_sympy(pr: MobiusTangentProblem, x) -> sp.Expr:
    e = _S(pr.a) + _S(pr.b) * x
    for lt in pr.logs:
        e += _S(lt.kappa) * sp.log(_S(lt.alpha) + _S(lt.beta) * x)
    if pr.sigma != 0:
        e += _S(pr.sigma) / (_S(pr.B) + _S(pr.A) * x)
    return e


def certify_mobius_tangent_cell_point(family, pt, name):
    """Certify one instance from `family.special[1](pt)`.

    The spec is a dict: either `{"problem": MobiusTangentProblem}` or the template fields
    `{"a", "b", "logs", "sigma", "B", "A", "p", "q"}` or the two sides
    `{"lhs", "rhs", "var", "p", "q"}`; optionally `"breakpoints"`, `"max_depth"`,
    `"max_cells"`.  Unknown keys are refused."""
    spec = family.special[1](pt)
    if not isinstance(spec, dict):
        raise _refuse(f"the family spec must be a dict, got {type(spec).__name__}")
    opts = {k: spec[k] for k in ("breakpoints", "max_depth", "max_cells") if k in spec}
    rest = {k: v for k, v in spec.items() if k not in opts}
    if "problem" in rest:
        if set(rest) != {"problem"}:
            raise _refuse(f"unknown spec key(s) {sorted(set(rest) - {'problem'})}")
        pr = rest["problem"]
    elif "lhs" in rest:
        if set(rest) != {"lhs", "rhs", "var", "p", "q"}:
            raise _refuse(f"a sides spec needs exactly lhs, rhs, var, p, q; got {sorted(rest)}")
        pr = problem_from_sides(rest["lhs"], rest["rhs"], rest["var"], rest["p"], rest["q"])
    else:
        unknown = set(rest) - {"a", "b", "logs", "sigma", "B", "A", "p", "q"}
        if unknown:
            raise _refuse(f"unknown spec key(s) {sorted(unknown)}")
        pr = mobius_tangent_problem(**rest)
    cert = mobius_tangent_cell_certificate(pr, **opts)
    return (CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert),
            cert.n_theorems)


# --- Lean rendering -----------------------------------------------------------------

def lit(q: Fraction) -> str:
    """A rational as a parenthesised Lean real operand: `(3)`, `(-3 / 16)`."""
    q = Fraction(q)
    if q.denominator == 1:
        return f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})"


def affine(c0: Fraction, c1: Fraction, x: str = "x") -> str:
    """`c0 + c1 * x`, both literals kept (the emitted lemmas instantiate to this form)."""
    return f"{lit(c0)} + {lit(c1)} * {x}"


def F_lean(pr: MobiusTangentProblem, x: str = "x") -> str:
    parts = [f"{lit(pr.a)} + {lit(pr.b)} * {x}"]
    for lt in pr.logs:
        parts.append(f"{lit(lt.kappa)} * Real.log ({affine(lt.alpha, lt.beta, x)})")
    if pr.sigma != 0:
        parts.append(f"{lit(pr.sigma)} / ({affine(pr.B, pr.A, x)})")
    return " + ".join(parts)


def sympy_to_lean(e: sp.Expr, x) -> str:
    """Render a sympy expression over {x, rationals, +, *, /, ^n, log} as Lean real text."""
    if e == x:
        return str(x)
    if e.is_Rational:
        return lit(Fraction(int(e.p), int(e.q)))
    if isinstance(e, sp.log):
        return f"Real.log ({sympy_to_lean(e.args[0], x)})"
    if e.is_Add:
        return "(" + " + ".join(sympy_to_lean(a, x) for a in e.args) + ")"
    if e.is_Mul:
        num, den = sp.fraction(e)
        if den != 1:
            return f"({sympy_to_lean(num, x)} / {sympy_to_lean(den, x)})"
        return "(" + " * ".join(sympy_to_lean(a, x) for a in e.args) + ")"
    if e.is_Pow and e.exp.is_Integer:
        if e.exp < 0:
            return f"(1 / {sympy_to_lean(e.base ** (-e.exp), x)})"
        return f"({sympy_to_lean(e.base, x)} ^ {int(e.exp)})"
    raise _refuse(f"cannot render {e} as Lean")


_GENERIC = """\
/-! ### Generic lemmas of the mobius_tangent_cell template (emitted once per family).
Tangent-line cells with a Mobius term and a convex majorant checked at the two endpoints:
Lemma 3.3 of a draft communicated by J. L. Goldwasser (28 Sep 2026).
conjecture1_proved = False. -/

/-- Concavity of `log` as a tangent bound at `u`, with `log u <= H`. -/
theorem {P}_log_tangent (u y H : ℝ) (hu : 0 < u) (hy : 0 < y) (hH : Real.log u ≤ H) :
    Real.log y ≤ H + (y - u) / u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hu)
  rw [Real.log_div hy.ne' hu.ne'] at h
  have e : (y - u) / u = y / u - 1 := by field_simp
  linarith

/-- For `s <= 0` the Mobius term `s / w` is concave in `w > 0`: tangent majorant at `c`. -/
theorem {P}_mobius_tangent (s w c d : ℝ) (hs : s ≤ 0) (hw : 0 < w) (hc : 0 < c)
    (hd : d = c ^ 2) : s / w ≤ s / c - s * (w - c) / d := by
  subst hd
  have e : s / c - s * (w - c) / c ^ 2 - s / w = -s * (w - c) ^ 2 / (w * c ^ 2) := by
    field_simp; ring
  have h : 0 ≤ -s * (w - c) ^ 2 / (w * c ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (sq_nonneg _)
    · positivity
  linarith

/-- For `s >= 0`, `m + k x + s / (B + A x)` is convex on `[p, q]` (where `B + A x > 0`):
nonpositive at both endpoints implies nonpositive throughout. -/
theorem {P}_convex_endpoint (m k s A B p q x : ℝ) (hs : 0 ≤ s) (hpx : p ≤ x) (hxq : x ≤ q)
    (hwp : 0 < B + A * p) (hwq : 0 < B + A * q)
    (hP : m + k * p + s / (B + A * p) ≤ 0) (hQ : m + k * q + s / (B + A * q) ≤ 0) :
    m + k * x + s / (B + A * x) ≤ 0 := by
  rcases eq_or_lt_of_le (le_trans hpx hxq) with hpq | hpq
  · have hx : x = p := le_antisymm (hpq ▸ hxq) hpx
    rw [hx]; exact hP
  set wp := B + A * p with hwp_def
  set wq := B + A * q with hwq_def
  set u := q - x with hu_def
  set v := x - p with hv_def
  have hu : 0 ≤ u := by rw [hu_def]; linarith
  have hv : 0 ≤ v := by rw [hv_def]; linarith
  have hD : 0 < u + v := by rw [hu_def, hv_def]; linarith
  have hwx : B + A * x = (u * wp + v * wq) / (u + v) := by
    rw [eq_div_iff hD.ne', hu_def, hv_def, hwp_def, hwq_def]; ring
  have hwxpos : 0 < u * wp + v * wq := by
    rcases eq_or_lt_of_le hu with h0 | h0
    · rw [← h0]; nlinarith
    · nlinarith
  -- convexity of 1/w along the chord, in Cauchy-Schwarz form
  have hcs : (u + v) ^ 2 * (wp * wq) ≤ (u * wq + v * wp) * (u * wp + v * wq) := by
    nlinarith [mul_nonneg (mul_nonneg hu hv) (sq_nonneg (wp - wq))]
  have hinv : s / (B + A * x) ≤ (u * (s / wp) + v * (s / wq)) / (u + v) := by
    rw [hwx, div_div_eq_mul_div, div_le_div_iff₀ hwxpos hD]
    have e : (u * (s / wp) + v * (s / wq)) = s * (u * wq + v * wp) / (wp * wq) := by
      field_simp
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hwp hwq)]
    have := mul_le_mul_of_nonneg_left hcs hs
    nlinarith [this]
  have hsum : u * (m + k * p + s / wp) + v * (m + k * q + s / wq) ≤ 0 := by
    nlinarith [mul_nonneg hu (by linarith : 0 ≤ -(m + k * p + s / wp)),
               mul_nonneg hv (by linarith : 0 ≤ -(m + k * q + s / wq))]
  have hkey : m + k * x + (u * (s / wp) + v * (s / wq)) / (u + v) ≤ 0 := by
    rw [← sub_nonpos]
    have e : m + k * x + (u * (s / wp) + v * (s / wq)) / (u + v) - 0
        = (u * (m + k * p + s / wp) + v * (m + k * q + s / wq)) / (u + v) := by
      field_simp; rw [hu_def, hv_def]; ring
    rw [e]; exact div_nonpos_of_nonpos_of_nonneg hsum hD.le
  linarith
"""


def _log_bound_theorem(bd: LogConstBound, nm: str) -> str:
    head = (f"/-- `log {bd.u} <= H` ({'Real.log_one' if bd.order == 0 else f'u = 2^{bd.n} * {bd.v}, order-{bd.order} Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_' + ('lt' if bd.n >= 0 else 'gt') + '_d9'}).\n"
            f"    conjecture1_proved = False. -/\n"
            f"theorem {nm} : Real.log {lit(bd.u)} ≤ {lit(bd.H)} := by\n")
    if bd.order == 0:
        return head + "  norm_num\n"
    x = 1 - bd.v
    lines = [f"  have hx : |({lit(x)} : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num\n",
             f"  have h := Real.abs_log_sub_add_sum_range_le hx {bd.order}\n",
             f"  rw [show (1 : ℝ) - {lit(x)} = {lit(bd.v)} by norm_num] at h\n"]
    n = bd.n
    if n == 0:
        lines.append(f"  generalize Real.log {lit(bd.v)} = L at h ⊢\n")
    else:
        # the split is proved BACKWARDS (`rw [<- Real.log_pow, <- Real.log_mul ..]`, then
        # `norm_num` on the argument) so no literal of the goal is ever rewritten
        if n > 0:
            split = (f"  have hs : (({n} : ℕ) : ℝ) * Real.log 2 + Real.log {lit(bd.v)} = "
                     f"Real.log {lit(bd.u)} := by\n"
                     f"    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; "
                     f"norm_num\n")
            l2 = "  have h2 := Real.log_two_lt_d9\n"
        else:
            split = (f"  have hs : Real.log {lit(bd.v)} - (({-n} : ℕ) : ℝ) * Real.log 2 = "
                     f"Real.log {lit(bd.u)} := by\n"
                     f"    rw [← Real.log_pow, ← Real.log_div (by norm_num) (by norm_num)]; "
                     f"norm_num\n")
            l2 = "  have h2 := Real.log_two_gt_d9\n"
        lines += [split, l2, "  rw [← hs]\n",
                  f"  generalize Real.log {lit(bd.v)} = L at h ⊢\n",
                  "  generalize Real.log 2 = T at h2 ⊢\n",
                  "  norm_num at h2 ⊢\n"]
    lines += ["  rw [abs_le] at h\n",
              "  norm_num [Finset.sum_range_succ] at h\n",
              "  linarith [h.1, h.2]\n"]
    return head + "".join(lines)


def _cell_theorem(pr: MobiusTangentProblem, cell: MobiusCell, nm: str, hnames, P: str) -> str:
    Fx = F_lean(pr)
    out = [f"/-- Cell [{cell.p}, {cell.q}], tangent point t = {cell.t}, Mobius mode "
           f"`{cell.mode}`: Psi(p) = {float(cell.psi_p):.4e}, Psi(q) = {float(cell.psi_q):.4e}."
           f"\n    conjecture1_proved = False. -/\n",
           f"theorem {nm} (x : ℝ) (hpx : {lit(cell.p)} ≤ x) (hxq : x ≤ {lit(cell.q)}) :\n"
           f"    {Fx} ≤ 0 := by\n"]
    for i, (lt, bd, hn) in enumerate(zip(pr.logs, cell.bounds, hnames)):
        y = affine(lt.alpha, lt.beta)
        out.append(f"  have hy{i} : (0 : ℝ) < {y} := by linarith\n")
        out.append(f"  have hl{i} := {P}_log_tangent {lit(bd.u)} ({y}) {lit(bd.H)} "
                   f"(by norm_num) hy{i} {hn}\n")
        out.append(f"  have hk{i} := mul_le_mul_of_nonneg_left hl{i} "
                   f"(by norm_num : (0 : ℝ) ≤ {lit(lt.kappa)})\n")
    if cell.mode == "convex":
        out.append(f"  have hM := {P}_convex_endpoint {lit(cell.m)} {lit(cell.k)} "
                   f"{lit(pr.sigma)} {lit(pr.A)} {lit(pr.B)} {lit(cell.p)} {lit(cell.q)} x\n"
                   f"    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) "
                   f"(by norm_num)\n")
    elif cell.mode == "tangent":
        c = pr.B + pr.A * cell.t
        w = affine(pr.B, pr.A)
        out.append(f"  have hw : (0 : ℝ) < {w} := by linarith\n")
        out.append(f"  have hM := {P}_mobius_tangent {lit(pr.sigma)} ({w}) {lit(c)} "
                   f"{lit(c * c)} (by norm_num) hw (by norm_num) (by norm_num)\n")
    out.append("  linarith\n")
    return "".join(out)


def _union_theorem(pr: MobiusTangentProblem, cells, names, nm: str) -> str:
    Fx = F_lean(pr)
    out = [f"/-- `F <= 0` on the whole interval [{pr.p}, {pr.q}], from {len(cells)} cell(s) "
           "tiling it at shared breakpoints.\n    conjecture1_proved = False. -/\n",
           f"theorem {nm} (x : ℝ) (hpx : {lit(pr.p)} ≤ x) (hxq : x ≤ {lit(pr.q)}) :\n"
           f"    {Fx} ≤ 0 := by\n"]
    lo = "hpx"
    for j, (c, cn) in enumerate(zip(cells, names)):
        if j == len(cells) - 1:
            out.append(f"  exact {cn} x {lo} hxq\n")
        else:
            out.append(f"  rcases le_or_gt x {lit(c.q)} with h{j} | h{j}\n"
                       f"  · exact {cn} x {lo} h{j}\n")
            lo = f"h{j}.le"
    return "".join(out)


def _nonzero_proof(d: sp.Expr, x, pr: MobiusTangentProblem) -> str:
    """`d != 0` on [P, Q] for a constant or affine denominator of the sides, by its exact sign
    at the two endpoints (an affine map keeps a strict sign between them); refuses otherwise."""
    pd = sp.Poly(sp.expand(d), x)
    if pd.degree() > 1:
        raise _refuse(f"sides denominator {d} is not affine; the sides theorem needs affine "
                      "denominators (state the template form instead)")
    vals = [d.subs(x, _S(e)) for e in (pr.p, pr.q)]
    e = sympy_to_lean(d, x)
    if all(v > 0 for v in vals):
        return "by norm_num" if pd.degree() <= 0 else f"(by linarith : (0 : ℝ) < {e}).ne'"
    if all(v < 0 for v in vals):
        return "by norm_num" if pd.degree() <= 0 else f"(by linarith : {e} < (0 : ℝ)).ne"
    raise _refuse(f"sides denominator {d} vanishes or changes sign on [{pr.p}, {pr.q}]")


def _sides_theorem(pr: MobiusTangentProblem, union_nm: str, nm: str) -> str:
    lhs, rhs, x = pr.sides
    L, R = sympy_to_lean(lhs, x), sympy_to_lean(rhs, x)
    Fx = F_lean(pr)
    out = [f"/-- The original two-sided form `lhs <= rhs` on [{pr.p}, {pr.q}] "
           "(lhs - rhs is identically the template F).\n    conjecture1_proved = False. -/\n",
           f"theorem {nm} (x : ℝ) (hpx : {lit(pr.p)} ≤ x) (hxq : x ≤ {lit(pr.q)}) :\n"
           f"    {L} ≤ {R} := by\n",
           f"  have hF := {union_nm} x hpx hxq\n"]
    dens = set()
    for e in (lhs, rhs):
        for sub in sp.preorder_traversal(e):
            if sub.is_Pow and sub.exp.is_Integer and sub.exp < 0:
                dens.add(sub.base)
            elif sub.is_Mul:
                _n, d = sp.fraction(sub)
                if d != 1:
                    dens.add(d)
    if pr.sigma != 0:
        dens.add(_S(pr.B) + _S(pr.A) * x)
    for i, d in enumerate(sorted(dens, key=str)):
        out.append(f"  have hd{i} : {sympy_to_lean(d, x)} ≠ 0 := {_nonzero_proof(d, x, pr)}\n")
    # `ring` treats `Real.log _` as an atom: first move every log argument of the sides onto
    # the template's literal form `alpha + beta * x`
    rws = []
    for e in (lhs, rhs):
        for sub in sp.preorder_traversal(e):
            if isinstance(sub, sp.log):
                pa = sp.Poly(sp.expand(sub.args[0]), x)
                cs = pa.all_coeffs()
                beta, alpha = (cs if len(cs) == 2 else [sp.Integer(0), cs[0]])
                src = sympy_to_lean(sub.args[0], x)
                dst = affine(_Q(alpha, "alpha"), _Q(beta, "beta"))
                if src != dst and (src, dst) not in rws:
                    rws.append((src, dst))
    for i, (src, dst) in enumerate(rws):
        out.append(f"  have hg{i} : Real.log ({src}) = Real.log ({dst}) := by congr 1; ring\n")
    rw = ("    rw [" + ", ".join(f"hg{i}" for i in range(len(rws))) + "]\n") if rws else ""
    out.append(f"  have e : {L} - {R} = {Fx} := by\n{rw}    field_simp\n    ring\n")
    out.append("  linarith\n")
    return "".join(out)


@dataclass
class MobiusTangentCellEmitter(Emitter):
    """Emit, per instance: one `log u <= H` theorem per distinct tangent argument, one
    theorem per cell (`F <= 0` on [p_j, q_j]), the union theorem over [P, Q] (the instance
    name), and -- when the problem came from two sides -- `<name>_sides` stating the
    original `lhs <= rhs`.  The three generic template lemmas are emitted ONCE per family,
    prefixed with the first instance name.  No `decide`, no proof hole.
    conjecture1_proved = False."""

    def __post_init__(self):
        self.kind = "mobius_tangent_cell"

    def emit_units(self, fam, profile: LeanProfile) -> list:
        """ONE unit: the generic lemmas are shared by every instance of the family."""
        return [self.emit_body(fam, profile)]

    def emit_body(self, fam, profile: LeanProfile) -> tuple:
        chunks, n_thm = [], 0
        if not fam.instances:
            return "", 0
        P = f"{fam.instances[0].lean_name}_mtc"
        chunks.append(_GENERIC.replace("{P}", P))
        n_thm += 3
        for inst in fam.instances:
            cert: MobiusTangentCellCert = inst.payload
            nm = inst.lean_name
            pr = cert.problem
            hname: dict = {}
            for c in cert.cells:
                for bd in c.bounds:
                    if bd.u not in hname:
                        hname[bd.u] = f"{nm}_logH{len(hname)}"
                        chunks.append(_log_bound_theorem(bd, hname[bd.u]))
                        n_thm += 1
            cnames = []
            for j, c in enumerate(cert.cells):
                cn = f"{nm}_cell{j}"
                cnames.append(cn)
                chunks.append(_cell_theorem(pr, c, cn, [hname[b.u] for b in c.bounds], P))
                n_thm += 1
            chunks.append(_union_theorem(pr, cert.cells, cnames, nm))
            n_thm += 1
            if pr.sides is not None:
                chunks.append(_sides_theorem(pr, nm, f"{nm}_sides"))
                n_thm += 1
        return "\n".join(chunks), n_thm


def mobius_tangent_cell_family(name: str, grid: GridSpec, lean_name: Callable,
                               spec: Callable, constants: dict | None = None
                               ) -> InequalityFamily:
    """Build a mobius_tangent_cell family (kind `mobius_tangent_cell`); see
    `certify_mobius_tangent_cell_point` for the spec dict."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("mobius_tangent_cell", spec),
        constants=dict(constants or {}),
    )
