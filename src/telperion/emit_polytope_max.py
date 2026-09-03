"""Polytope-max (multi-affine corner) box-positivity emitter — the general-d
generalization of the shipped bilinear-corner emitter ("Handelman Route B":
corner dispatch + per-edge affine slice).

A **multi-affine** polynomial ``p(x_1,…,x_d)`` (degree ≤ 1 in EACH variable) is
affine in each coordinate when the others are held fixed; on an axis-aligned box
``∏[l_i,u_i]`` it therefore attains its extremum at a CORNER.  Hence

    0 ≤ p(v)   for every one of the 2^d corners v   ⟹   0 ≤ p(x)  ∀ x∈box.

For ``d = 2`` this is exactly ``emit_bilinear_corner`` (the bilinear worst-corner
lemma ``bilinear_corner_nonneg``); this emitter generalizes it to any ``d``.

The exact certificate is the barycentric convex-combination identity

    p(x) = Σ_corner λ_corner · p(corner),   λ_corner = ∏_i w_i(x_i) ≥ 0 on the box,

where ``w_i(x_i)`` is ``(u_i−x_i)/(u_i−l_i)`` if the corner takes ``l_i`` on axis
``i`` and ``(x_i−l_i)/(u_i−l_i)`` if it takes ``u_i``.  The Σ of the products of
these per-axis convex weights is identically 1 and each weight is ≥ 0 on the box,
so a nonnegative combination of nonnegative corner values is nonnegative.

``polytope_max_certificate`` writes ``p`` in the multi-affine monomial basis
(one coefficient per subset ``S ⊆ {1,…,d}`` for the monomial ``∏_{i∈S} x_i``),
computes the ``2^d`` corner values, EXACTLY self-checks the barycentric
convex-combination identity in sympy (``expand(p − Σλ·corner) == 0``), and RAISES
``ValueError`` (the anti-phantom negative control) if any corner value is < 0 or
the box is degenerate (``u_i ≤ l_i`` on some axis).

The emitted Lean models the PROVEN ``bilinear_corner`` pattern generalized to d:
a reusable per-d lemma ``multiaffine_corner_nonneg_<d>`` is stated ONCE at the top
of the file (its proof: slice affinely in each variable in turn — the same nested
sign-cased ``mul_nonneg`` + ``nlinarith`` structure as ``bilinear_corner_nonneg``,
one level per variable), and each instance is one theorem that supplies the 2^d
``by norm_num`` corner facts and applies it.

NEGATIVE CONTROL: a form with a negative corner value (or a degenerate box) is
refused at certification with ``ValueError``.

Reference: examples/bilinear_corner (the d=2 specialization) and
docs/HANDELMAN_DEGREE_BOUNDS_LIT (Route B corner dispatch).
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly as a script
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# --- Lean identifier scheme --------------------------------------------------
# Variables x0..x_{d-1}; box bounds l0..l_{d-1}, u0..u_{d-1}.  A monomial is
# indexed by a frozenset S of axis indices (the product ∏_{i∈S} x_i); its
# coefficient symbol in Lean is c<S sorted joined by ''> e.g. c, c0, c01, c012.
def _mono_key(S: frozenset[int]) -> str:
    return "c" + "".join(str(i) for i in sorted(S))


def _all_subsets(d: int) -> list[frozenset[int]]:
    """All 2^d subsets of {0,…,d-1}, ordered by (size, lexicographic)."""
    out: list[frozenset[int]] = []
    for k in range(d + 1):
        from itertools import combinations

        for combo in combinations(range(d), k):
            out.append(frozenset(combo))
    return out


@dataclass(frozen=True)
class PolytopeMaxCertificate:
    """A verified worst-corner certificate for ``0 ≤ p(x)`` on ``∏[l_i,u_i]``,
    where ``p`` is multi-affine (degree ≤ 1 per variable).

    ``coeffs`` maps each subset ``S ⊆ {0,…,d-1}`` (the monomial ∏_{i∈S} x_i) to
    its rational coefficient.  ``corners`` maps each corner (a tuple in
    ``{0,1}^d`` selecting l_i vs u_i per axis) to the (nonnegative) value p there.
    """

    d: int
    coeffs: dict[frozenset[int], sp.Rational]
    lo: tuple[sp.Rational, ...]
    hi: tuple[sp.Rational, ...]
    corners: dict[tuple[int, ...], sp.Rational]


def _eval_at(coeffs: dict[frozenset[int], sp.Rational], vals) -> sp.Expr:
    """p(vals) = Σ_S coeff_S · ∏_{i∈S} vals[i]  (multi-affine monomial basis)."""
    total = sp.Integer(0)
    for S, c in coeffs.items():
        term = c
        for i in S:
            term = term * vals[i]
        total = total + term
    return total


def polytope_max_certificate(
    coeffs: dict, lo, hi
) -> PolytopeMaxCertificate:
    """Build and EXACTLY self-check a multi-affine worst-corner certificate.

    ``coeffs``: dict subset-of-axes -> rational (multi-affine monomial basis).
      Keys may be given as frozensets/tuples/sorted-tuples of axis indices; the
      empty set is the constant term.
    ``lo``, ``hi``: per-axis rational box bounds (length d), requiring l_i < u_i.

    Computes the 2^d corner values, verifies the barycentric convex-combination
    identity symbolically, and REFUSES (``ValueError``) a degenerate box or any
    negative corner value (the anti-phantom negative control)."""
    lo = tuple(sp.nsimplify(v) for v in lo)
    hi = tuple(sp.nsimplify(v) for v in hi)
    d = len(lo)
    if len(hi) != d:
        raise ValueError(f"polytope_max: lo/hi length mismatch ({len(lo)} vs {len(hi)})")
    if d < 1:
        raise ValueError("polytope_max needs d >= 1 variables")
    for i in range(d):
        if hi[i] <= lo[i]:
            raise ValueError(
                f"polytope_max needs l_{i} < u_{i}; got l={lo[i]}, u={hi[i]}"
            )

    # normalize coefficient keys to frozensets; validate degree (multi-affine)
    norm: dict[frozenset[int], sp.Rational] = {}
    for key, val in coeffs.items():
        if isinstance(key, frozenset):
            S = key
        elif isinstance(key, (tuple, list, set)):
            S = frozenset(int(i) for i in key)
        elif key is None:
            S = frozenset()
        else:
            S = frozenset((int(key),))
        for i in S:
            if not (0 <= i < d):
                raise ValueError(f"polytope_max: axis index {i} out of range [0,{d})")
        norm[S] = sp.nsimplify(val) + norm.get(S, sp.Integer(0))

    # corner values: corner is a d-tuple in {0,1}^d (0 -> l_i, 1 -> u_i)
    corner_vals: dict[tuple[int, ...], sp.Rational] = {}
    for corner in product((0, 1), repeat=d):
        vals = tuple(lo[i] if corner[i] == 0 else hi[i] for i in range(d))
        v = sp.simplify(_eval_at(norm, vals))
        if not v.is_rational:
            raise ValueError(f"polytope_max: corner value {v} at {corner} is not rational")
        if v < 0:
            raise ValueError(
                f"polytope_max corner {corner} value {v} < 0 — form is NOT "
                f"box-positive; certificate rejected"
            )
        corner_vals[corner] = sp.Rational(v)

    # Exact self-check of the barycentric convex-combination identity:
    #   p(x) = Σ_corner (∏_i w_i(x_i)) · p(corner),  w_i ≥ 0 on the box.
    xs = sp.symbols(f"x0:{d}")
    if d == 1:
        xs = (xs,) if not isinstance(xs, tuple) else xs
    p_expr = _eval_at(norm, xs)
    combo = sp.Integer(0)
    for corner, cval in corner_vals.items():
        lam = sp.Integer(1)
        for i in range(d):
            if corner[i] == 0:
                lam = lam * (hi[i] - xs[i]) / (hi[i] - lo[i])
            else:
                lam = lam * (xs[i] - lo[i]) / (hi[i] - lo[i])
        combo = combo + lam * cval
    if sp.expand(p_expr - combo) != 0:
        raise ValueError(
            "polytope_max convex-combination self-check failed — certificate rejected"
        )

    return PolytopeMaxCertificate(
        d=d, coeffs=norm, lo=lo, hi=hi, corners=corner_vals
    )


def certify_polytope_max_point(family, pt, name):
    """Certify one polytope-max instance from
    ``family.special[1](pt) -> (coeffs, lo, hi)``."""
    coeffs, lo, hi = family.special[1](pt)
    cert = polytope_max_certificate(coeffs, lo, hi)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# --- Lean lemma generation (per-d reusable worst-corner lemma) ---------------
def _lean_form(coeffs_syms: dict[frozenset[int], str], var_names: list[str]) -> str:
    """Render Σ_S c_S · (∏_{i∈S} x_i) in Lean, using the coeff SYMBOL names and
    the given variable expressions (each an already-rendered Lean term)."""
    subsets = _all_subsets(len(var_names)) if False else sorted(
        coeffs_syms.keys(), key=lambda S: (len(S), sorted(S))
    )
    terms = []
    for S in subsets:
        c = coeffs_syms[S]
        if not S:
            terms.append(c)
        else:
            factors = [var_names[i] for i in sorted(S)]
            prod = " * ".join(factors)
            terms.append(f"{c} * ({prod})" if len(factors) > 1 else f"{c} * {prod}")
    return " + ".join(terms)


def multiaffine_lemma(d: int) -> str:
    """The reusable ``multiaffine_corner_nonneg_<d>`` lemma for a fixed arity d.

    Generalizes ``bilinear_corner_nonneg`` (d=2): slice affinely in variable
    x_{d-1}, then x_{d-2}, …, then x_0.  Each slice is closed by the same
    sign-cased ``mul_nonneg`` + ``nlinarith`` used in the bilinear lemma."""
    subsets = _all_subsets(d)
    csym = {S: _mono_key(S) for S in subsets}
    xvars = [f"x{i}" for i in range(d)]
    lvars = [f"l{i}" for i in range(d)]
    uvars = [f"u{i}" for i in range(d)]

    # binder: all coefficients, all vars, all bounds, as ℝ
    coeff_names = [csym[S] for S in subsets]
    binder = " ".join(coeff_names + xvars + lvars + uvars)

    # box hypotheses
    box_hyps = []
    for i in range(d):
        box_hyps.append(f"(hl{i} : {lvars[i]} ≤ {xvars[i]}) (hu{i} : {xvars[i]} ≤ {uvars[i]})")

    # corner hypotheses h<bits>
    corner_hyps = []
    for corner in product((0, 1), repeat=d):
        vname = "".join(str(b) for b in corner)
        vals = [lvars[i] if corner[i] == 0 else uvars[i] for i in range(d)]
        form = _lean_form(csym, vals)
        corner_hyps.append(f"    (h{vname} : 0 ≤ {form})")

    goal_form = _lean_form(csym, xvars)

    lines: list[str] = []
    lines.append(
        f"/-- A multi-affine (degree ≤ 1 per variable) form in {d} variable(s), "
        f"nonnegative at all {2**d} corners of a box, is nonnegative on it. -/"
    )
    lines.append(f"theorem multiaffine_corner_nonneg_{d}")
    lines.append(f"    {{{binder} : ℝ}}")
    lines.append("    " + " ".join(box_hyps))
    lines.append("\n".join(corner_hyps) + " :")
    lines.append(f"    0 ≤ {goal_form} := by")

    # Build the nested slice proof.  slice_k proves: fixing x_0..x_{k-1} at
    # abstract values and x_{k+1}..x_{d-1} already reduced, the form is
    # nonnegative when it is nonnegative at x_k = l_k and x_k = u_k.
    # We emit d nested `have` steps, innermost first (slice on x_{d-1}), each a
    # ∀ over the not-yet-fixed leading variables.
    #
    # Concretely, we generalize the bilinear proof:
    #   hz : ∀ (leading vars) , corner-at-l → corner-at-u → interior  (slice x_{d-1})
    #   ...
    #   final: apply the outermost slice at x_0=l_0 / x_0=u_0.
    #
    # To keep nlinarith's job small and identical to the proven bilinear shape,
    # each slice fixes exactly one variable and quantifies over the ones before
    # it; the slope for axis j is  Σ_{S ∋ j} c_S ∏_{i∈S, i≠j} (fixed value).

    # We implement the slices from last axis (d-1) down to axis 1 as `have`
    # lemmas hslice{j}, and axis 0 as the final rcases.
    def _form_with(fixed: dict[int, str], var_at: dict[int, str]) -> str:
        """Render the form where axis i takes fixed[i] (a Lean term) if present,
        else var_at[i]."""
        vals = []
        for i in range(d):
            if i in fixed:
                vals.append(fixed[i])
            else:
                vals.append(var_at[i])
        return _lean_form(csym, vals)

    def _slope_term(j: int, fixed: dict[int, str]) -> str:
        """Slope in axis j: Σ_{S ∋ j} c_S · ∏_{i∈S, i≠j} fixed_or_var(i)."""
        terms = []
        for S in subsets:
            if j not in S:
                continue
            rest = sorted(i for i in S if i != j)
            if not rest:
                terms.append(csym[S])
            else:
                factors = [fixed.get(i, xvars[i]) for i in rest]
                prod = " * ".join(f"({f})" for f in factors)
                terms.append(f"{csym[S]} * ({prod})")
        return " + ".join(terms) if terms else "0"

    # For j from d-1 downto 1: emit slice lemma hslice{j} quantifying over the
    # abstract leading values a0..a_{j-1} (Lean vars av0.. ), fixing x_j -> the
    # slice variable, and reducing axis j via corner-at-l_j / corner-at-u_j to
    # the interior x_j.  For simplicity and to match the proven bilinear shape,
    # we instead emit the slices in the SAME concrete structure as the d=2 and
    # d=3 hand proofs: a chain of `have hs{j} : ∀ (av0..av_{j-1}) , ...`.
    body: list[str] = []

    # Represent leading abstract values as va{i} (Lean identifiers).
    for j in range(d - 1, 0, -1):
        va = {i: f"va{i}" for i in range(j)}          # abstract leading values
        # slice on axis j: interior x_j, corners l_j & u_j; axes >j are the true
        # interior variables x_{>j}; axes <j are the abstract va; axis j varies.
        fixed_lead = dict(va)                          # axes 0..j-1 = abstract
        # hypotheses at x_j = l_j and x_j = u_j (axes >j still interior x_i)
        base = dict(fixed_lead)
        form_l = _form_with({**base, j: lvars[j]}, {i: xvars[i] for i in range(d)})
        form_u = _form_with({**base, j: uvars[j]}, {i: xvars[i] for i in range(d)})
        form_i = _form_with({**base}, {i: xvars[i] for i in range(d)})
        quant = " ".join(f"va{i}" for i in range(j))
        slope = _slope_term(j, {**fixed_lead, **{i: xvars[i] for i in range(j + 1, d)}})
        body.append(f"  have hs{j} : ∀ {quant} : ℝ,")
        body.append(f"      0 ≤ {form_l} →")
        body.append(f"      0 ≤ {form_u} →")
        body.append(f"      0 ≤ {form_i} := by")
        body.append(f"    intro {quant} e_lo e_hi")
        body.append(f"    rcases le_total 0 ({slope}) with hb | hb")
        body.append(f"    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl{j})]")
        body.append(f"    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu{j})]")

    # Now assemble: reduce the top-level corners into the slice lemmas.  We need
    # to feed hslice_{1} with the outputs of hslice_{2} etc.  Build a recursion:
    # applying hs{j} at leading values (va0..va_{j-1}) requires the two
    # sub-results at x_j=l_j and x_j=u_j, which themselves come from hs{j+1}.
    #
    # We produce, for each assignment of axes 0..j-1 to {l,u} and axes j.. free,
    # a `have`.  The cleanest is to build bottom-up: for the deepest slice hs_{d-1}
    # we consume the raw corner hyps; for hs_{j} we consume results of hs_{j+1}.
    #
    # Encode a partial corner as a tuple over axes 0..k-1 in {0,1}.  Result name
    # R_<bits> proves nonnegativity with axes 0..k-1 fixed at those bits and
    # axes k.. interior.
    #
    # Base results R_<bits over all d axes> are the corner hyps h<bits>.
    # Step: R_<bits over 0..j-1> := hs{j} <l-values...> R_<bits,0> R_<bits,1>
    #   wait — hs{j} fixes axes 0..j-1 abstractly and slices axis j; its inputs
    #   are the results with axis j at l and u.  So:
    #   R_<b_0..b_{j-1}> = hs{j} (l_0-or-u_0 per b) ... via feeding corner-l/u.
    #
    # Actually hs{j} quantifies leading axes 0..j-1; we instantiate them at the
    # concrete lower/upper bounds selected by bits b_0..b_{j-1}.  Its two
    # hypotheses are R_<b,0>-analog at x_j=l_j and x_j=u_j i.e. results with axes
    # 0..j fixed (the first j by b, axis j by 0/1).
    def _bits_name(bits: tuple[int, ...]) -> str:
        return "R_" + ("".join(str(b) for b in bits) if bits else "root")

    # deepest: results with all d axes fixed = the corner hyps
    # We only need results with axes 0..j fixed for the assembly. Build from
    # k=d down to k=1.
    assembly: list[str] = []
    # results dict maps bits-tuple (len k) -> Lean term proving it
    results: dict[tuple[int, ...], str] = {}
    for corner in product((0, 1), repeat=d):
        results[corner] = "h" + "".join(str(b) for b in corner)

    for j in range(d - 1, 0, -1):
        new_results: dict[tuple[int, ...], str] = {}
        for bits in product((0, 1), repeat=j):
            # instantiate hs{j} leading vars 0..j-1 at l/u per bits
            args = []
            for i in range(j):
                args.append(lvars[i] if bits[i] == 0 else uvars[i])
            lo_term = results[bits + (0,)]
            hi_term = results[bits + (1,)]
            name = f"S{j}_" + "".join(str(b) for b in bits)
            call = f"hs{j} " + " ".join(args) + f" {lo_term} {hi_term}"
            assembly.append(f"  have {name} := {call}")
            new_results[bits] = name
        results = new_results

    # final axis 0: the goal.  results now holds len-1 bits -> proofs for
    # x_0=l_0 (bits (0,)) and x_0=u_0 (bits (1,)).
    G0 = results[(0,)]
    G1 = results[(1,)]
    slope0 = _slope_term(0, {i: xvars[i] for i in range(1, d)})
    assembly.append(f"  rcases le_total 0 ({slope0}) with hb | hb")
    assembly.append(f"  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl0), {G0}, {G1}]")
    assembly.append(f"  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu0), {G0}, {G1}]")

    lines.extend(body)
    lines.extend(assembly)
    return "\n".join(lines) + "\n"


def _multiaffine_lemma_d1() -> str:
    """d=1 degenerate case: a linear form on [l,u] — extremum at an endpoint."""
    return (
        "/-- A linear (affine) form on [l,u] nonnegative at both endpoints is "
        "nonnegative on it. -/\n"
        "theorem multiaffine_corner_nonneg_1 {c c0 x l0 u0 : ℝ}\n"
        "    (hl0 : l0 ≤ x) (hu0 : x ≤ u0)\n"
        "    (h0 : 0 ≤ c + c0 * l0) (h1 : 0 ≤ c + c0 * u0) :\n"
        "    0 ≤ c + c0 * x := by\n"
        "  rcases le_total 0 c0 with hb | hb\n"
        "  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl0)]\n"
        "  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu0)]\n"
    )


@dataclass
class PolytopeMaxMonotoneEmitter(Emitter):
    """Emit ``0 ≤ p(x)`` for a multi-affine ``p`` on a box, via the reusable
    per-d ``multiaffine_corner_nonneg_<d>`` lemma applied to the 2^d
    ``by norm_num`` corner facts.

    The needed per-d lemmas are emitted ONCE at the top of the file (deduplicated
    across instances of the same arity); each instance is one theorem.  This
    mirrors the compiling bilinear_corner ``*_cell`` proof exactly, generalized
    to d variables."""

    def __post_init__(self):
        self.kind = "polytope_max"

    def _instance_text(self, cert: PolytopeMaxCertificate, lean_name: str) -> str:
        d = cert.d
        subsets = _all_subsets(d)
        csym = {S: _mono_key(S) for S in subsets}
        xvars = [f"x{i}" for i in range(d)]
        # coeff Lean terms
        cval = {S: rat_lean(cert.coeffs.get(S, sp.Integer(0))) for S in subsets}
        lo = [rat_lean(v) for v in cert.lo]
        hi = [rat_lean(v) for v in cert.hi]

        def _form(var_terms: list[str]) -> str:
            terms = []
            for S in subsets:
                c = cval[S]
                if not S:
                    terms.append(c)
                else:
                    factors = [var_terms[i] for i in sorted(S)]
                    prod = " * ".join(factors)
                    terms.append(
                        f"{c} * ({prod})" if len(factors) > 1 else f"{c} * {prod}"
                    )
            return " + ".join(terms)

        # signature
        var_decl = " ".join(xvars)
        box_lines = []
        for i in range(d):
            box_lines.append(
                f"    (hl{i} : {lo[i]} ≤ {xvars[i]}) (hu{i} : {xvars[i]} ≤ {hi[i]})"
            )
        goal = _form(xvars)

        out: list[str] = []
        out.append(f"theorem {lean_name} ({var_decl} : ℝ)")
        out.append("\n".join(box_lines) + " :")
        out.append(f"    0 ≤ {goal} := by")

        # corner facts: h<bits> : 0 ≤ <form at corner> := by have : ... = val; rw
        corner_apply_args = []
        for corner in product((0, 1), repeat=d):
            bits = "".join(str(b) for b in corner)
            var_terms = [lo[i] if corner[i] == 0 else hi[i] for i in range(d)]
            cform = _form(var_terms)
            v = rat_lean(cert.corners[corner])
            out.append(f"  have h{bits} : (0:ℝ) ≤ {cform} := by")
            out.append(f"    have : {cform} = ({v} : ℝ) := by norm_num")
            out.append(f"    rw [this]; norm_num")
            corner_apply_args.append(f"h{bits}")

        box_args = " ".join(f"hl{i} hu{i}" for i in range(d))
        out.append(
            f"  exact multiaffine_corner_nonneg_{d} {box_args} "
            + " ".join(corner_apply_args)
        )
        return "\n".join(out) + "\n"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        # collect the arities present, emit each per-d lemma once
        arities = sorted({inst.payload.d for inst in fam.instances})  # type: ignore
        lines: list[str] = []
        nlemmas = 0
        for d in arities:
            if d == 1:
                lines.append(_multiaffine_lemma_d1())
            else:
                lines.append(multiaffine_lemma(d))
            nlemmas += 1
        nthm = 0
        for inst in fam.instances:
            cert: PolytopeMaxCertificate = inst.payload  # type: ignore[assignment]
            lines.append(self._instance_text(cert, inst.lean_name))
            nthm += 1
        # count instance theorems + the reusable per-d lemmas (kernel-checked)
        return "\n".join(lines), nthm + nlemmas


def polytope_max_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a polytope-max (multi-affine corner) box-positivity family
    (kind='polytope_max').

    ``spec``: a callable ``pt -> (coeffs, lo, hi)`` where ``coeffs`` is a dict
    subset-of-axes -> rational (multi-affine monomial basis), and ``lo``/``hi``
    are per-axis rational box bounds with ``l_i < u_i`` and every corner value
    ≥ 0.  Refuses otherwise."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("polytope_max", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    # ---- Positive case 1: d=3 product (1+x)(1+y)(1+z) on [0,1]^3 --------------
    # multi-affine monomial basis: all subset coeffs = 1.
    coeffs3 = {frozenset(S): 1 for S in _all_subsets(3)}
    cert3 = polytope_max_certificate(coeffs3, (0, 0, 0), (1, 1, 1))
    inst3 = CertifiedInstance(
        point={"case": 0}, lean_name="pm_product_unit_3", corners=(), payload=cert3
    )

    # ---- Positive case 2: a genuine d=3 mixed-slope form, box-positive --------
    # p = 4 - x - y - z + x*y*z on [0,1]^3.  Corners: min is at a single-1 corner
    # = 4 - 1 = 3 (>0); the all-1 corner = 4-3+1 = 2 (>0).  Multi-affine.
    coeffs3b = {
        frozenset(): 4,
        frozenset((0,)): -1,
        frozenset((1,)): -1,
        frozenset((2,)): -1,
        frozenset((0, 1, 2)): 1,
    }
    cert3b = polytope_max_certificate(coeffs3b, (0, 0, 0), (1, 1, 1))
    inst3b = CertifiedInstance(
        point={"case": 1}, lean_name="pm_mixed_slopes_3", corners=(), payload=cert3b
    )

    # ---- Positive case 3: d=2 (recovers the bilinear specialization) ----------
    # p = 3 - x - 2y + x*y on [0,1]^2  (the bilinear mixed_slopes instance).
    coeffs2 = {
        frozenset(): 3,
        frozenset((0,)): -1,
        frozenset((1,)): -2,
        frozenset((0, 1)): 1,
    }
    cert2 = polytope_max_certificate(coeffs2, (0, 0), (1, 1))
    inst2 = CertifiedInstance(
        point={"case": 2}, lean_name="pm_bilinear_d2", corners=(), payload=cert2
    )

    emitter = PolytopeMaxMonotoneEmitter()

    class _FamView:
        instances = (inst3, inst3b, inst2)

    text, nthm = emitter.emit_body(_FamView(), LeanProfile(namespace=("PolytopeMax",)))
    print("=" * 72)
    print(f"EMITTED LEAN ({nthm} theorems, incl. per-d lemmas):")
    print("=" * 72)
    print(text)

    # ---- Negative control 1: a form with a NEGATIVE corner must be refused ----
    print("=" * 72)
    print("NEGATIVE CONTROL (negative corner, expect ValueError):")
    try:
        # p = -1 + x + y + z on [0,1]^3: corner (0,0,0) = -1 < 0.
        polytope_max_certificate(
            {frozenset(): -1, frozenset((0,)): 1, frozenset((1,)): 1, frozenset((2,)): 1},
            (0, 0, 0), (1, 1, 1),
        )
        print("  FAIL: no ValueError raised — negative control did NOT fire!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  OK: refused as expected -> {e}")

    # ---- Negative control 2: degenerate box (u_i <= l_i) must be refused ------
    print("NEGATIVE CONTROL 2 — degenerate box (expect ValueError):")
    try:
        polytope_max_certificate({frozenset(): 1}, (1, 0), (1, 1))
        print("  FAIL: no ValueError raised on degenerate box!")
        raise SystemExit(1)
    except ValueError as e:
        print(f"  OK: refused as expected -> {e}")

    print("=" * 72)
    print("ALL SELF-TESTS PASSED")
