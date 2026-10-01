"""Curvature-boundary "extremum-on-the-boundary" emitter — the sign-definite-f''
face.

CROSS-FRONTIER CONVERGENCE.  This ports a pattern that appeared INDEPENDENTLY in
the AxiomMath/ZetaZeros Lean proof (arXiv:2609.02882, Montgomery–Taylor kernel):
a function whose second derivative has a DEFINITE SIGN attains its extremum on an
interval at the BOUNDARY.  Their ``extremalG_const`` proves ``G'' = 0 ⟹ G affine
⟹ (even ⟹) constant``, evaluated at the endpoints ``A(±1/2)``.  This emitter
GENERALIZES the existing Telperion emitter ``affine_param_endpoint`` (affine gap
→ endpoints) to the CURVATURE-SIGN setting, and it also covers the BG finding
that a per-cell gap CONCAVE in the child-message sum is minimized at box corners
(the concave-corner case).

The principle: for ``f : ℝ → ℝ`` on ``[a,b]``:

* **affine** (``f'' = 0``): ``f`` is determined by its endpoints;
  ``f(x) ≥ m ∀x∈[a,b] ⟺ f(a) ≥ m ∧ f(b) ≥ m``.
* **concave** (``f'' ≤ 0``): ``f(x) ≥ min(f(a),f(b))`` — the MIN is at an
  endpoint (a concave function on a segment dominates the chord through its
  endpoints, which dominates the min of the endpoint values).
* **convex** (``f'' ≥ 0``): ``f(x) ≤ max(f(a),f(b))`` — the MAX is at an
  endpoint.

HONEST SCOPE.  This emitter reduces a SIGN-DEFINITE-CURVATURE interval extremum to
the two endpoints.  The self-check verifies (in exact sympy) that the claimed
curvature sign actually holds of ``f'' `` on ``[a,b]``; the emitted Lean proves,
via Mathlib's ``ConcaveOn``/``ConvexOn`` API (or an ``nlinarith`` witness for the
concrete quadratic instance), that the extremum sits at a boundary point.  It does
NOT choose ``f`` for you, nor prove any downstream inequality.  The emitted file
is self-contained (only ``import Mathlib``).

KINK-MINIMUM MODE (extension, 2026-10-01; ``mode="kink"``): a continuous piecewise polynomial
with one interior kink at a rational kappa, left piece decreasing and right piece increasing
(each a Bernstein sign check on the derivative), is minimized at kappa -- `IsLeast (f '' Icc a b)
(f kappa)`, plus `0 <= f` when `f(kappa) >= 0`, and the same for an optional closed form with
`Abs` of affine arguments.  See ``kink_minimum_certificate`` and
docs/EMITTER_EXTENSIONS_BUNDLE_DESIGN_2026-10-01.md.

conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass

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
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


_MODES = ("concave", "affine", "convex")


def _lean_rat(q) -> str:
    """Render an exact rational as a Lean ℝ literal fragment (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


@dataclass(frozen=True)
class CurvatureBoundaryCertificate:
    """A verified curvature-boundary (extremum-at-endpoint) certificate.

    ``mode`` is ``"concave"``, ``"affine"``, or ``"convex"``.  ``f_expr`` is the
    exact sympy expression (in the single symbol ``x``) whose second derivative
    ``f''`` has been verified over ℚ to have the claimed sign on ``[a,b]``:

    * ``concave``: ``f'' ≤ 0`` on ``[a,b]`` — so ``min(f(a),f(b)) ≤ f(x)``.
    * ``affine`` : ``f'' = 0`` — so ``f`` is endpoint-determined.
    * ``convex`` : ``f'' ≥ 0`` on ``[a,b]`` — so ``f(x) ≤ max(f(a),f(b))``.

    A WRONG claimed sign is REFUSED at build time (the negative control).  Fields
    are exact ``sympy`` objects.  ``f2`` is the (exact) second derivative,
    ``fa``/``fb`` the endpoint values.
    """

    mode: str
    f_expr: object   # f(x), exact sympy in symbol x
    a: object        # left endpoint (exact rational)
    b: object        # right endpoint (exact rational)
    f2: object       # f''(x), exact sympy
    fa: object       # f(a)
    fb: object       # f(b)


def _f2_sign_on_interval(f2, x, a, b):
    """Return one of "zero"/"nonpos"/"nonneg"/"mixed" for the sign of ``f2`` on
    ``[a,b]`` — verified EXACTLY over ℚ.

    Constant ``f2`` is decided by its value.  Otherwise we minimise/maximise the
    (real) polynomial ``f2`` over ``[a,b]`` at its endpoints and interior real
    critical points and read off the sign of the extreme values."""
    f2 = sp.expand(f2)
    if f2.free_symbols == set():  # constant second derivative
        v = sp.nsimplify(f2)
        if v == 0:
            return "zero"
        return "nonpos" if v < 0 else "nonneg"
    # nonconstant: gather candidate extremum points = endpoints + real crit pts in [a,b]
    pts = [sp.Rational(a), sp.Rational(b)]
    for r in sp.solve(sp.diff(f2, x), x):
        if r.is_real and sp.Rational(a) <= r <= sp.Rational(b):
            pts.append(r)
    vals = [sp.nsimplify(f2.subs(x, p)) for p in pts]
    lo = min(vals)
    hi = max(vals)
    if lo == 0 and hi == 0:
        return "zero"
    if hi <= 0:
        return "nonpos"
    if lo >= 0:
        return "nonneg"
    return "mixed"


def curvature_boundary_certificate(
    *, mode: str = "concave", f_expr="-(x**2) + x", a=0, b=1
) -> CurvatureBoundaryCertificate:
    """Build and EXACTLY self-check (over ℚ) a curvature-boundary certificate.

    ``f_expr`` is parsed as a sympy expression in the symbol ``x``.  The
    self-check computes ``f'' `` exactly and verifies its sign on ``[a,b]``
    matches ``mode``:

    * ``mode="concave"``: require ``f'' ≤ 0`` on ``[a,b]``.
    * ``mode="affine"`` : require ``f'' = 0`` identically.
    * ``mode="convex"``  : require ``f'' ≥ 0`` on ``[a,b]``.

    NEGATIVE CONTROL: if the claimed curvature sign is WRONG anywhere on
    ``[a,b]`` — e.g. ``mode="concave"`` but ``f'' > 0`` somewhere — the build is
    REFUSED with ``ValueError``.  A false certificate is thus a Python-side
    refusal, never an emitted (false) Lean theorem.
    """
    if mode not in _MODES:
        raise ValueError(f"REFUSED: unknown mode {mode!r} (expected {'|'.join(_MODES)})")
    a_r = sp.Rational(a)
    b_r = sp.Rational(b)
    if not (a_r < b_r):
        raise ValueError(f"REFUSED: degenerate interval [{a_r},{b_r}] (need a < b)")

    x = sp.Symbol("x")
    f = sp.sympify(f_expr, locals={"x": x})
    if not (f.free_symbols <= {x}):
        raise ValueError(
            f"REFUSED: f = {f} must be a function of x alone (free symbols "
            f"{f.free_symbols})"
        )
    f2 = sp.expand(sp.diff(f, x, 2))
    sign = _f2_sign_on_interval(f2, x, a_r, b_r)

    if mode == "concave":
        if sign not in ("nonpos", "zero"):
            raise ValueError(
                f"REFUSED: mode='concave' claims f'' ≤ 0 on [{a_r},{b_r}] but "
                f"f'' = {f2} is {sign} there (negative control — f'' > 0 somewhere)"
            )
    elif mode == "convex":
        if sign not in ("nonneg", "zero"):
            raise ValueError(
                f"REFUSED: mode='convex' claims f'' ≥ 0 on [{a_r},{b_r}] but "
                f"f'' = {f2} is {sign} there (negative control — f'' < 0 somewhere)"
            )
    else:  # affine
        if sign != "zero":
            raise ValueError(
                f"REFUSED: mode='affine' claims f'' = 0 but f'' = {f2} is {sign} "
                f"on [{a_r},{b_r}] (negative control — nonzero curvature)"
            )

    fa = sp.nsimplify(f.subs(x, a_r))
    fb = sp.nsimplify(f.subs(x, b_r))
    return CurvatureBoundaryCertificate(
        mode=mode, f_expr=f, a=a_r, b=b_r, f2=f2, fa=fa, fb=fb
    )


def certify_curvature_boundary_point(family, pt, name):
    """Certify one curvature-boundary instance from ``family.special[1](pt)``.

    ``spec`` is a dict ``{"mode": "concave"|"affine"|"convex", "f_expr": ...,
    "a": ..., "b": ...}`` (all optional; default is the concave quadratic
    ``f(x) = -(x²) + x`` on ``[0,1]``)."""
    spec = family.special[1](pt)
    if spec.get("mode") == "kink":
        kw = {k: v for k, v in spec.items() if k != "mode"}
        kcert = kink_minimum_certificate(**kw)
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=kcert)
        return inst, 2 + len(kcert.left_cells) + len(kcert.right_cells)
    cert = curvature_boundary_certificate(
        mode=spec.get("mode", "concave"),
        f_expr=spec.get("f_expr", "-(x**2) + x"),
        a=spec.get("a", 0),
        b=spec.get("b", 1),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# ---- the abstract Lean lemmas, emitted once at the top of each family file ----
_ABSTRACT = """\
-- (1) ABSTRACT CONCAVE→ENDPOINTS.  A function concave on `[a,b]` dominates the
-- MIN of its two endpoint values everywhere on `[a,b]`: the extremum (here the
-- minimum) of a sign-definite-curvature function sits at a boundary point.
-- Proof: `x ∈ [a,b]` is a convex combination `x = t·a + (1-t)·b`; concavity gives
-- `f x ≥ t·f a + (1-t)·f b ≥ min (f a) (f b)`.
theorem concave_ge_min_endpoints {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcave : ConcaveOn ℝ (Set.Icc a b) f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    min (f a) (f b) ≤ f x := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  rcases eq_or_lt_of_le hab with he | hlt
  · -- degenerate a = b: x is forced to a, and min (f a) (f b) = f a = f x.
    subst he
    have hxa : x = a := le_antisymm hx.2 hx.1
    simp [hxa]
  · -- a < b: write x = t·a + (1-t)·b with t = (b-x)/(b-a) ∈ [0,1].
    set t : ℝ := (b - x) / (b - a) with ht
    have hba : 0 < b - a := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
    have ht1 : 0 ≤ 1 - t := by
      rw [ht]
      have : (b - x) / (b - a) ≤ 1 :=
        (div_le_one hba).mpr (by linarith [hx.1])
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hxconv : t • a + (1 - t) • b = x := by
      simp only [ht, smul_eq_mul]
      field_simp
      ring
    have hkey := hcave.2 ha hb ht0 ht1 hsum
    rw [hxconv] at hkey
    -- hkey : t • f a + (1 - t) • f b ≤ f x  (concavity: value ≥ chord)
    simp only [smul_eq_mul] at hkey
    have hmina : min (f a) (f b) ≤ f a := min_le_left _ _
    have hminb : min (f a) (f b) ≤ f b := min_le_right _ _
    have hchord : min (f a) (f b) ≤ t * f a + (1 - t) * f b := by
      nlinarith [mul_le_mul_of_nonneg_left hmina ht0,
                 mul_le_mul_of_nonneg_left hminb ht1]
    linarith

-- (3) AFFINE FACE (f'' = 0).  The `affine_param_endpoint` core restated in the
-- curvature framing: an affine `A + x·B` that is `≥ m` at both endpoints of
-- `[a,b]` is `≥ m` throughout — the extremum of a ZERO-curvature function sits at
-- a boundary point.
theorem affine_boundary {a b m x : ℝ} (hab : a < b) (A B : ℝ)
    (hL : m ≤ A + a * B) (hH : m ≤ A + b * B) (hx : x ∈ Set.Icc a b) :
    m ≤ A + x * B := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hba : 0 < b - a := sub_pos.mpr hab
  -- (b−x)(A+aB) + (x−a)(A+bB) = (b−a)(A+xB); both summands ≥ (·)·m, sum ≥ (b−a)m.
  have hprodL : 0 ≤ (b - x) * (A + a * B - m) :=
    mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hL)
  have hprodH : 0 ≤ (x - a) * (A + b * B - m) :=
    mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hH)
  nlinarith [hprodL, hprodH, hba]

-- (4) CONVEX→ENDPOINTS (f'' ≥ 0).  Dual of (1): a function convex on `[a,b]` is
-- dominated by the MAX of its two endpoint values — the (maximum) extremum of a
-- convex function sits at a boundary point.
theorem convex_le_max_endpoints {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcvx : ConvexOn ℝ (Set.Icc a b) f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ max (f a) (f b) := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  rcases eq_or_lt_of_le hab with he | hlt
  · subst he
    have hxa : x = a := le_antisymm hx.2 hx.1
    simp [hxa]
  · set t : ℝ := (b - x) / (b - a) with ht
    have hba : 0 < b - a := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
    have ht1 : 0 ≤ 1 - t := by
      rw [ht]
      have : (b - x) / (b - a) ≤ 1 :=
        (div_le_one hba).mpr (by linarith [hx.1])
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hxconv : t • a + (1 - t) • b = x := by
      simp only [ht, smul_eq_mul]
      field_simp
      ring
    have hkey := hcvx.2 ha hb ht0 ht1 hsum
    rw [hxconv] at hkey
    simp only [smul_eq_mul] at hkey
    have hmaxa : f a ≤ max (f a) (f b) := le_max_left _ _
    have hmaxb : f b ≤ max (f a) (f b) := le_max_right _ _
    have hchord : t * f a + (1 - t) * f b ≤ max (f a) (f b) := by
      nlinarith [mul_le_mul_of_nonneg_left hmaxa ht0,
                 mul_le_mul_of_nonneg_left hmaxb ht1]
    linarith
"""


@dataclass
class CurvatureBoundaryEmitter(Emitter):
    """Emit the curvature-boundary "extremum-at-endpoint" theorems.

    The abstract lemmas are emitted ONCE (from the first instance):

    1. ``concave_ge_min_endpoints`` — concave on `[a,b]` ⟹ `min(f a, f b) ≤ f x`.
    3. ``affine_boundary`` — the `affine_param_endpoint` core in curvature framing
       (zero curvature ⟹ endpoint-determined).
    4. ``convex_le_max_endpoints`` — convex on `[a,b]` ⟹ `f x ≤ max(f a, f b)`.

    Then, per instance, a CONCRETE face — porting AxiomMath's ``extremalG_const``
    move to a concrete sign-definite quadratic (default the concave
    ``f(x) = -(x²) + x`` on ``[0,1]``), proved by the ``(x−a)(b−x) ≥ 0``
    ``nlinarith`` witness:

        theorem <name> : ∀ x ∈ Set.Icc a b, min (f a) (f b) ≤ f x

    HONEST SCOPE: reduces a sign-definite-curvature interval extremum to the two
    endpoints; ports the AxiomMath/ZetaZeros (arXiv:2609.02882) Montgomery–Taylor
    ``extremalG_const`` move and covers the BG concave-corner case; generalizes
    ``affine_param_endpoint``.  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "curvature_boundary"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        abstract_emitted = False
        kink_emitted = False
        for inst in fam.instances:
            cert: CurvatureBoundaryCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if isinstance(cert, KinkMinimumCertificate):
                # kink-minimum extension (2026-10-01): its own generic lemma, emitted once
                # and only when a kink instance is present (endpoint-mode files unchanged)
                if not kink_emitted:
                    lines.append(_KINK_ABSTRACT)
                    kink_emitted = True
                    nthm += 1
                text, k = _emit_kink(cert, name)
                lines.append(text)
                nthm += k
                continue
            if not abstract_emitted:
                lines.append(_ABSTRACT)
                abstract_emitted = True
                nthm += 3
            lines.append(self._emit_concrete(cert, name))
            nthm += 1
        return "\n".join(lines), nthm

    def _emit_concrete(self, cert: CurvatureBoundaryCertificate, name: str) -> str:
        a = _lean_rat(cert.a)
        b = _lean_rat(cert.b)
        fa = _lean_rat(cert.fa)
        fb = _lean_rat(cert.fb)
        # render f(x) as a Lean ℝ expression from the sympy expr
        f_lean = _sympy_to_lean(cert.f_expr)
        if cert.mode == "concave":
            # min(f a, f b) ≤ f x, via (x-a)(b-x) ≥ 0 concavity witness.
            return (
                f"-- CONCRETE CONCAVE INSTANCE `{name}` (ports AxiomMath extremalG_const\n"
                f"-- move to the concave quadratic f x = {f_lean}, f'' = {_lean_rat(cert.f2)} ≤ 0\n"
                f"-- on [{a},{b}]): the minimum sits at a boundary, so\n"
                f"-- `min (f {a}) (f {b}) ≤ f x` for all x∈[{a},{b}], by the (x−{a})({b}−x) ≥ 0 witness.\n"
                f"theorem {name} : ∀ x ∈ Set.Icc ({a} : ℝ) ({b}),\n"
                f"    min (({fa} : ℝ)) ({fb}) ≤ (fun x : ℝ => {f_lean}) x := by\n"
                f"  intro x hx\n"
                f"  have hxa : ({a} : ℝ) ≤ x := hx.1\n"
                f"  have hxb : x ≤ ({b} : ℝ) := hx.2\n"
                f"  simp only\n"
                f"  have hmin : min (({fa} : ℝ)) ({fb}) ≤ {fa} := min_le_left _ _\n"
                f"  have hmin2 : min (({fa} : ℝ)) ({fb}) ≤ {fb} := min_le_right _ _\n"
                f"  nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hxb),\n"
                f"             hmin, hmin2]\n"
            )
        if cert.mode == "convex":
            return (
                f"-- CONCRETE CONVEX INSTANCE `{name}` (dual of the extremalG_const move:\n"
                f"-- f x = {f_lean}, f'' = {_lean_rat(cert.f2)} ≥ 0 on [{a},{b}]): the maximum sits\n"
                f"-- at a boundary, so `f x ≤ max (f {a}) (f {b})` for all x∈[{a},{b}].\n"
                f"theorem {name} : ∀ x ∈ Set.Icc ({a} : ℝ) ({b}),\n"
                f"    (fun x : ℝ => {f_lean}) x ≤ max (({fa} : ℝ)) ({fb}) := by\n"
                f"  intro x hx\n"
                f"  have hxa : ({a} : ℝ) ≤ x := hx.1\n"
                f"  have hxb : x ≤ ({b} : ℝ) := hx.2\n"
                f"  simp only\n"
                f"  have hmax : ({fa} : ℝ) ≤ max (({fa} : ℝ)) ({fb}) := le_max_left _ _\n"
                f"  have hmax2 : ({fb} : ℝ) ≤ max (({fa} : ℝ)) ({fb}) := le_max_right _ _\n"
                f"  nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hxb),\n"
                f"             hmax, hmax2]\n"
            )
        # affine: use affine_boundary with A = fa, B = slope (fb - fa)/(b - a)
        slope = sp.nsimplify((cert.fb - cert.fa) / (cert.b - cert.a))
        # f(x) = fa + (x - a)*slope; at the endpoints this reproduces fa, fb.
        A = sp.nsimplify(cert.fa - cert.a * slope)
        A_l = _lean_rat(A)
        B_l = _lean_rat(slope)
        m_l = _lean_rat(min(cert.fa, cert.fb))
        return (
            f"-- CONCRETE AFFINE INSTANCE `{name}` (f'' = 0 face — the `affine_param_endpoint`\n"
            f"-- core in curvature framing): f x = {f_lean} = {A_l} + x·({B_l}); with the endpoint\n"
            f"-- floor m = {m_l} met at both a={a}, b={b}, `m ≤ {A_l} + x·({B_l})` throughout.\n"
            f"theorem {name} : ∀ x ∈ Set.Icc ({a} : ℝ) ({b}),\n"
            f"    ({m_l} : ℝ) ≤ ({A_l}) + x * ({B_l}) := by\n"
            f"  intro x hx\n"
            f"  exact affine_boundary (by norm_num) ({A_l}) ({B_l})\n"
            f"    (by norm_num) (by norm_num) hx\n"
        )


def _sympy_to_lean(expr) -> str:
    """Render a sympy expression in x as a Lean ℝ expression (rational literals,
    ``^`` for powers)."""
    x = sp.Symbol("x")
    expr = sp.sympify(expr, locals={"x": x})
    s = sp.sstr(expr, order="lex")
    # sympy uses ** for powers; Lean uses ^.
    s = s.replace("**", "^")
    return s


def curvature_boundary_family(name, grid, lean_name, spec, constants=None):
    """Build a curvature-boundary family (kind='curvature_boundary').

    ``spec``: a callable ``pt -> {"mode": "concave"|"affine"|"convex",
    "f_expr": ..., "a": ..., "b": ...}`` (all optional; default is the concave
    quadratic ``f(x) = -(x²) + x`` on ``[0,1]``)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("curvature_boundary", spec),
        constants=dict(constants or {}),
    )


# ---------------------------------------------------------------------------
# Kink-minimum extension (2026-10-01)
# ---------------------------------------------------------------------------
#
# A continuous piecewise-polynomial function on [a, b] with ONE interior kink at a rational
# point kappa:  f(x) = L(x) for x <= kappa,  f(x) = R(x) for x > kappa,  L(kappa) = R(kappa).
# If L' <= 0 on [a, kappa] and R' >= 0 on [kappa, b], then f is antitone on [a, kappa] and
# monotone on [kappa, b], so its minimum over [a, b] is f(kappa) = v.  Each derivative sign is
# a one-variable polynomial sign check, certified by nonnegative Bernstein coefficients on
# cells of the side interval (shared machinery with concave_pooled_induction); the Lean turns
# each into AntitoneOn / MonotoneOn through Mathlib's `antitoneOn_of_deriv_nonpos` /
# `monotoneOn_of_deriv_nonneg` applied to the pieces as `Polynomial ℝ`.  Optionally a closed
# form `f_expr` (a sympy expression in x whose only non-polynomial atoms are `Abs` of AFFINE
# arguments, e.g. |x - 1/3| + x^2) is proved equal to the piecewise f on [a, b] and the same
# conclusions are restated for it.
#
# Emitted per instance: IsLeast (f '' Icc a b) v, the pointwise bound v <= f x, f kappa = v,
# and 0 <= f x on [a, b] when v >= 0.  REFUSALS: kappa not strictly inside (a, b); pieces that
# are not polynomials in x; a discontinuity L(kappa) != R(kappa); a derivative sign that fails
# anywhere on its side (with an exact counterexample point); a Bernstein cover that does not
# close by depth 8; a claimed value different from f(kappa); an f_expr that does not agree with
# the pieces, or with an Abs of a non-affine argument or one changing sign on a side.

_KINK_MAX_DEPTH = 8
_KINK_MAX_DEGREE = 12


@dataclass(frozen=True)
class KinkMinimumCertificate:
    """A verified kink-minimum certificate (all fields exact).

    ``left``/``right`` are ascending coefficient tuples of the pieces in ``x``;
    ``left_cells`` certify ``-L' >= 0`` on cells tiling ``[a, kappa]``, ``right_cells``
    certify ``R' >= 0`` on cells tiling ``[kappa, b]`` (``PolyCert`` objects in the shared
    Bernstein form).  ``value`` is ``f(kappa)``.  ``f_expr`` is the optional closed form and
    ``abs_args`` its Abs arguments with their sign on each side ("le"/"ge").  ``checked`` is
    False only for hand-forged negative controls."""

    a: object
    kappa: object
    b: object
    left: tuple
    right: tuple
    value: object
    left_cells: tuple
    right_cells: tuple
    f_expr: object = None
    abs_args: tuple = ()
    checked: bool = True


def _kink_poly(expr, x, what):
    e = sp.sympify(expr, locals={"x": x}) if isinstance(expr, str) else sp.sympify(expr)
    if e.atoms(sp.Float):
        raise ValueError(f"REFUSED: {what} = {e} contains a float")
    if not (e.free_symbols <= {x}):
        raise ValueError(f"REFUSED: {what} = {e} must be a function of x alone")
    try:
        P = sp.Poly(sp.expand(e), x, domain="QQ")
    except sp.PolynomialError as err:
        raise ValueError(f"REFUSED: {what} = {e} is not a polynomial in x ({err})") from err
    if P.degree() > _KINK_MAX_DEGREE:
        raise ValueError(f"REFUSED: {what} has degree {P.degree()} > {_KINK_MAX_DEGREE}")
    d = max(P.degree(), 0)
    return tuple(sp.Rational(P.coeff_monomial(x ** k)) for k in range(d + 1))


def _sign_cover(coeffs, s, t, depth=0):
    """Bernstein cells certifying ``0 <= P`` on ``[s, t]`` (P ascending coeffs in x), bisecting
    on failure; None when the cover does not close by ``_KINK_MAX_DEPTH``."""
    from .emit_concave_pooled_induction import R_SYM, _polycert
    P = sp.Poly(sum(c * R_SYM ** i for i, c in enumerate(coeffs)) + 0 * R_SYM, R_SYM,
                domain="QQ")
    pc = _polycert(P, s, t, False)
    if pc.ok():
        return [pc]
    if depth >= _KINK_MAX_DEPTH:
        return None
    mid = (s + t) / 2
    left = _sign_cover(coeffs, s, mid, depth + 1)
    if left is None:
        return None
    right = _sign_cover(coeffs, mid, t, depth + 1)
    if right is None:
        return None
    return left + right


def _neg_point(coeffs, s, t, x):
    """An exact point of [s, t] where the polynomial is negative, if one is easy to find."""
    P = sum(c * x ** i for i, c in enumerate(coeffs))
    cands = [s, t, (s + t) / 2]
    for r in sp.Poly(sp.diff(P, x), x).real_roots() if sp.diff(P, x) != 0 else []:
        if s <= r <= t:
            q = sp.nsimplify(r) if r.is_rational else sp.Rational(str(sp.N(r, 30)))
            if s <= q <= t:
                cands.append(q)
    for q in cands:
        if P.subs(x, q) < 0:
            return q, P.subs(x, q)
    return None


def _abs_args(f, x):
    return sorted({e.args[0] for e in sp.preorder_traversal(f) if isinstance(e, sp.Abs)},
                  key=sp.default_sort_key)


def _affine_sign(arg, x, s, t):
    """'le' if arg <= 0 on [s, t], 'ge' if arg >= 0 there (arg affine in x), else None."""
    va, vb = arg.subs(x, s), arg.subs(x, t)
    if va <= 0 and vb <= 0:
        return "le"
    if va >= 0 and vb >= 0:
        return "ge"
    return None


def kink_minimum_certificate(*, left, right, kappa, a, b, f_expr=None, value=None,
                             check: bool = True) -> KinkMinimumCertificate:
    """Build and EXACTLY verify a kink-minimum certificate.

    ``left``/``right``: the polynomial pieces (sympy expressions or strings in ``x``) on
    ``[a, kappa]`` and ``[kappa, b]``.  ``kappa``: the rational kink, ``a < kappa < b``.
    ``f_expr``: an optional closed form (``Abs`` of affine arguments allowed) checked to agree
    with the pieces.  ``value``: an optional claimed minimum, checked against ``L(kappa)``.

    ``check=False`` is for hand-forged negative controls ONLY: every sign/equality check is
    skipped and ``value`` (if given) is taken as claimed."""
    x = sp.Symbol("x")
    a_r, k_r, b_r = (sp.Rational(sp.sympify(v)) for v in (a, kappa, b))
    for nm_, v in (("a", a), ("kappa", kappa), ("b", b)):
        if isinstance(v, float):
            raise ValueError(f"REFUSED: {nm_} = {v!r} is a float; pass an exact rational")
    if not (a_r < k_r < b_r):
        raise ValueError(f"REFUSED: the kink kappa = {k_r} must lie strictly inside "
                         f"({a_r}, {b_r})")
    L = _kink_poly(left, x, "left piece")
    R = _kink_poly(right, x, "right piece")
    Lx = sum(c * x ** i for i, c in enumerate(L))
    Rx = sum(c * x ** i for i, c in enumerate(R))
    vL, vR = Lx.subs(x, k_r), Rx.subs(x, k_r)
    v = sp.Rational(vL)
    if check:
        if vL != vR:
            raise ValueError(f"REFUSED: discontinuous at the kink: L({k_r}) = {vL} but "
                             f"R({k_r}) = {vR}")
        if value is not None and sp.Rational(sp.sympify(value)) != v:
            raise ValueError(f"REFUSED: claimed minimum {value} but f({k_r}) = {v}")
    elif value is not None:
        v = sp.Rational(sp.sympify(value))
    negdL = _kink_poly(-sp.diff(Lx, x), x, "-L'")
    dR = _kink_poly(sp.diff(Rx, x), x, "R'")
    lc = _sign_cover(negdL, a_r, k_r)
    rc = _sign_cover(dR, k_r, b_r)
    if check:
        if lc is None:
            why = _neg_point(negdL, a_r, k_r, x)
            raise ValueError(
                f"REFUSED: left piece not certified decreasing on [{a_r}, {k_r}] (L' = "
                f"{sp.expand(-sum(c * x ** i for i, c in enumerate(negdL)))})"
                + (f"; L'({why[0]}) = {-why[1]} > 0" if why else ""))
        if rc is None:
            why = _neg_point(dR, k_r, b_r, x)
            raise ValueError(
                f"REFUSED: right piece not certified increasing on [{k_r}, {b_r}] (R' = "
                f"{sp.expand(sum(c * x ** i for i, c in enumerate(dR)))})"
                + (f"; R'({why[0]}) = {why[1]} < 0" if why else ""))
        for pc in lc + rc:
            if not pc.identity_holds():  # pragma: no cover - by construction
                raise ValueError("REFUSED: a Bernstein identity does not expand back")
    else:  # forged: one (possibly failing) cell per side
        from .emit_concave_pooled_induction import R_SYM, _polycert
        lc = lc or [_polycert(sp.Poly(sum(c * R_SYM ** i for i, c in enumerate(negdL))
                                      + 0 * R_SYM, R_SYM, domain="QQ"), a_r, k_r, False)]
        rc = rc or [_polycert(sp.Poly(sum(c * R_SYM ** i for i, c in enumerate(dR))
                                      + 0 * R_SYM, R_SYM, domain="QQ"), k_r, b_r, False)]
    fe = None
    abs_info: tuple = ()
    if f_expr is not None:
        fe = sp.sympify(f_expr, locals={"x": x}) if isinstance(f_expr, str) else f_expr
        if fe.atoms(sp.Float):
            raise ValueError(f"REFUSED: f_expr = {fe} contains a float")
        if not (fe.free_symbols <= {x}):
            raise ValueError(f"REFUSED: f_expr = {fe} must be a function of x alone")
        info = []
        subsL, subsR = {}, {}
        for arg in _abs_args(fe, x):
            if not (sp.Poly(arg, x).degree() <= 1 and not arg.atoms(sp.Abs)):
                raise ValueError(f"REFUSED: |{arg}| has a non-affine argument")
            sl, sr = _affine_sign(arg, x, a_r, k_r), _affine_sign(arg, x, k_r, b_r)
            if sl is None or sr is None:
                raise ValueError(f"REFUSED: the argument {arg} of an Abs changes sign on a "
                                 f"side of the kink (only one kink, at {k_r}, is supported)")
            info.append((arg, sl, sr))
            subsL[sp.Abs(arg)] = -arg if sl == "le" else arg
            subsR[sp.Abs(arg)] = -arg if sr == "le" else arg
        abs_info = tuple(info)
        if check:
            if sp.expand(fe.xreplace(subsL) - Lx) != 0:
                raise ValueError(f"REFUSED: f_expr = {fe} does not equal the left piece on "
                                 f"[{a_r}, {k_r}]")
            if sp.expand(fe.xreplace(subsR) - Rx) != 0:
                raise ValueError(f"REFUSED: f_expr = {fe} does not equal the right piece on "
                                 f"[{k_r}, {b_r}]")
    return KinkMinimumCertificate(a=a_r, kappa=k_r, b=b_r, left=L, right=R, value=v,
                                  left_cells=tuple(lc), right_cells=tuple(rc), f_expr=fe,
                                  abs_args=abs_info, checked=check)


_KINK_ABSTRACT = """\
-- (5) KINK MINIMUM (extension, 2026-10-01).  A function antitone on `[a,k]` and monotone
-- on `[k,b]` attains its minimum over `[a,b]` at the kink `k`.
theorem kink_min_of_anti_mono {a k b : ℝ} (f : ℝ → ℝ)
    (hL : AntitoneOn f (Set.Icc a k)) (hR : MonotoneOn f (Set.Icc k b))
    (hak : a ≤ k) (hkb : k ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : f k ≤ f x := by
  rcases le_total x k with h | h
  · exact hL ⟨hx.1, h⟩ ⟨hak, le_rfl⟩ h
  · exact hR ⟨le_rfl, hkb⟩ ⟨h, hx.2⟩ h
"""


def _kq(q) -> str:
    q = sp.Rational(q)
    return f"({q.p} : ℝ)" if q.q == 1 else f"({q.p} / {q.q} : ℝ)"


def _kink_polyX(coeffs) -> str:
    terms = [f"Polynomial.C {_kq(c)} * Polynomial.X ^ {i}" for i, c in enumerate(coeffs)
             if c != 0]
    return " + ".join(terms) if terms else "Polynomial.C (0 : ℝ)"


def _kink_expr_lean(e, x) -> str:
    """Render the closed form (rationals, x, +, *, integer powers, Abs) as Lean ℝ text."""
    if e == x:
        return "x"
    if e.is_Rational:
        return _kq(e)
    if isinstance(e, sp.Abs):
        return f"|{_kink_expr_lean(e.args[0], x)}|"
    if e.is_Add:
        return "(" + " + ".join(_kink_expr_lean(t, x) for t in e.args) + ")"
    if e.is_Mul:
        return "(" + " * ".join(_kink_expr_lean(t, x) for t in e.args) + ")"
    if e.is_Pow and e.exp.is_Integer and e.exp > 0:
        return f"{_kink_expr_lean(e.base, x)} ^ {int(e.exp)}"
    raise ValueError(f"REFUSED: cannot render {e} in the kink closed form")


def _ev(*polys) -> str:
    """The `Polynomial.eval` simp set for these pieces (`eval_add` only when some piece has
    two or more terms, so no simp argument is ever unused)."""
    multi = any(sum(1 for q in p if q != 0) > 1 for p in polys)
    return (("Polynomial.eval_add, " if multi else "")
            + "Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X")


def _dv(p) -> str:
    multi = sum(1 for q in p if q != 0) > 1
    return (("Polynomial.derivative_add, " if multi else "")
            + "Polynomial.derivative_C_mul_X_pow, " + _ev(p))


def _kink_sign_proof(cells, var="x") -> list[str]:
    """Lines proving `0 ≤ P x` on the union of ``cells`` from h1 : s0 ≤ x, h2 : x ≤ t_last."""
    from .emit_concave_pooled_induction import _facts
    out = []
    n = len(cells)

    def one(pc, lo_h, hi_h, ind):
        return [f"{ind}have hs : 0 ≤ {var} - {_kq(pc.s)} := by linarith [{lo_h}]",
                f"{ind}have ht : 0 ≤ {_kq(pc.t)} - {var} := by linarith [{hi_h}]",
                f"{ind}linarith [{_facts(pc)}]"]
    if n == 1:
        return one(cells[0], "h1", "h2", "  ")
    for i, pc in enumerate(cells):
        lo_h = "h1" if i == 0 else f"hc{i - 1}.le"
        if i < n - 1:
            out.append(f"  rcases le_or_gt {var} {_kq(pc.t)} with hc{i} | hc{i}")
            body = one(pc, lo_h, f"hc{i}", "    ")
            out.append("  · " + body[0].lstrip())
            out += body[1:]
        else:
            body = one(pc, lo_h, "h2", "    ")
            out.append("  · " + body[0].lstrip())
            out += body[1:]
    return out


def _emit_kink(c: KinkMinimumCertificate, nm: str) -> tuple[str, int]:
    from .emit_concave_pooled_induction import _poly1
    a, k, b, v = _kq(c.a), _kq(c.kappa), _kq(c.b), _kq(c.value)
    x = sp.Symbol("x")
    dL = tuple(-q for q in _kink_poly(-sp.diff(sum(q * x ** i for i, q in enumerate(c.left)),
                                                 x), x, "L'"))
    dR = _kink_poly(sp.diff(sum(q * x ** i for i, q in enumerate(c.right)), x), x, "R'")
    negdL = tuple(-q for q in dL)
    L: list[str] = []
    n = 0
    lin_off = ("set_option linter.unreachableTactic false in\n"
               "set_option linter.unusedTactic false in\n"
               "set_option linter.unnecessarySeqFocus false in\n")
    L.append(f"-- KINK-MINIMUM INSTANCE `{nm}` (extension, 2026-10-01): f = L on [{c.a}, "
             f"{c.kappa}], f = R on ({c.kappa}, {c.b}],\n"
             f"-- L' ≤ 0 and R' ≥ 0 certified by Bernstein cells "
             f"({len(c.left_cells)} + {len(c.right_cells)}), so min f = f({c.kappa}) = "
             f"{c.value}.")
    L.append(f"noncomputable def {nm}_L : Polynomial ℝ := {_kink_polyX(c.left)}")
    L.append(f"noncomputable def {nm}_R : Polynomial ℝ := {_kink_polyX(c.right)}")
    L.append(f"/-- The piecewise function: `L` up to the kink, `R` after it. -/")
    L.append(f"noncomputable def {nm}_f (x : ℝ) : ℝ := if x ≤ {k} then {nm}_L.eval x "
             f"else {nm}_R.eval x\n")
    for side, poly, piece in (("L", dL, c.left), ("R", dR, c.right)):
        L.append(lin_off + f"theorem {nm}_d{side} (x : ℝ) :\n"
                 f"    (Polynomial.derivative {nm}_{side}).eval x = {_poly1(poly, 'x')} := by\n"
                 f"  simp only [{nm}_{side}, {_dv(piece)}] <;> norm_num <;> ring_nf\n")
        n += 1
    # sign lemmas
    L.append(f"theorem {nm}_dL_nonpos (x : ℝ) (h1 : {a} ≤ x) (h2 : x ≤ {k}) :\n"
             f"    {_poly1(dL, 'x')} ≤ 0 := by\n"
             f"  suffices H : 0 ≤ {_poly1(negdL, 'x')} by linarith\n"
             + "\n".join(_kink_sign_proof(c.left_cells)) + "\n")
    L.append(f"theorem {nm}_dR_nonneg (x : ℝ) (h1 : {k} ≤ x) (h2 : x ≤ {b}) :\n"
             f"    0 ≤ {_poly1(dR, 'x')} := by\n"
             + "\n".join(_kink_sign_proof(c.right_cells)) + "\n")
    n += 2
    L.append(f"theorem {nm}_L_anti : AntitoneOn (fun x => {nm}_L.eval x) (Set.Icc {a} {k}) := by\n"
             f"  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) {nm}_L.continuous.continuousOn\n"
             f"    {nm}_L.differentiable.differentiableOn\n"
             f"  intro x hx\n"
             f"  rw [interior_Icc] at hx\n"
             f"  rw [Polynomial.deriv, {nm}_dL]\n"
             f"  exact {nm}_dL_nonpos x hx.1.le hx.2.le\n")
    L.append(f"theorem {nm}_R_mono : MonotoneOn (fun x => {nm}_R.eval x) (Set.Icc {k} {b}) := by\n"
             f"  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) {nm}_R.continuous.continuousOn\n"
             f"    {nm}_R.differentiable.differentiableOn\n"
             f"  intro x hx\n"
             f"  rw [interior_Icc] at hx\n"
             f"  rw [Polynomial.deriv, {nm}_dR]\n"
             f"  exact {nm}_dR_nonneg x hx.1.le hx.2.le\n")
    n += 2
    L.append(f"theorem {nm}_cont : {nm}_L.eval {k} = {nm}_R.eval {k} := by\n"
             f"  simp only [{nm}_L, {nm}_R, {_ev(c.left, c.right)}]\n"
             f"  norm_num\n")
    L.append(f"theorem {nm}_f_anti : AntitoneOn {nm}_f (Set.Icc {a} {k}) := by\n"
             f"  refine {nm}_L_anti.congr ?_\n"
             f"  intro x hx\n"
             f"  simp only [{nm}_f]\n"
             f"  rw [if_pos hx.2]\n")
    L.append(f"theorem {nm}_f_mono : MonotoneOn {nm}_f (Set.Icc {k} {b}) := by\n"
             f"  refine {nm}_R_mono.congr ?_\n"
             f"  intro x hx\n"
             f"  simp only [{nm}_f]\n"
             f"  rcases eq_or_lt_of_le hx.1 with h | h\n"
             f"  · rw [← h, if_pos le_rfl]; exact {nm}_cont.symm\n"
             f"  · rw [if_neg (not_le.mpr h)]\n")
    n += 3
    L.append(f"/-- The value at the kink. -/\n"
             f"theorem {nm}_value : {nm}_f {k} = {v} := by\n"
             f"  simp only [{nm}_f, if_pos (le_refl {k}), {nm}_L, {_ev(c.left)}]\n"
             f"  norm_num\n")
    L.append(f"/-- The minimum over `[{c.a}, {c.b}]` is attained at the kink: `{c.value} ≤ f x`. -/\n"
             f"theorem {nm} : ∀ x ∈ Set.Icc {a} {b}, {v} ≤ {nm}_f x := by\n"
             f"  intro x hx\n"
             f"  rw [← {nm}_value]\n"
             f"  exact kink_min_of_anti_mono {nm}_f {nm}_f_anti {nm}_f_mono (by norm_num) "
             f"(by norm_num) hx\n")
    L.append(f"/-- `min_{{[a,b]}} f = f(kappa) = {c.value}` as an `IsLeast` statement. -/\n"
             f"theorem {nm}_isLeast : IsLeast ({nm}_f '' Set.Icc {a} {b}) {v} :=\n"
             f"  ⟨⟨{k}, ⟨by norm_num, by norm_num⟩, {nm}_value⟩, by\n"
             f"    rintro _ ⟨x, hx, rfl⟩; exact {nm} x hx⟩\n")
    n += 3
    if c.value >= 0:
        L.append(f"/-- Nonnegativity on `[{c.a}, {c.b}]` (the kink value is `≥ 0`). -/\n"
                 f"theorem {nm}_nonneg : ∀ x ∈ Set.Icc {a} {b}, 0 ≤ {nm}_f x := fun x hx =>\n"
                 f"  le_trans (by norm_num) ({nm} x hx)\n")
        n += 1
    if c.f_expr is not None:
        fe = _kink_expr_lean(c.f_expr, x)
        rwl = ", ".join(
            f"abs_of_{'nonpos' if sl == 'le' else 'nonneg'} "
            f"(show {('' if sl == 'le' else '0 ≤ ')}{_kink_expr_lean(arg, x)}"
            f"{' ≤ 0' if sl == 'le' else ''} by linarith [hx.1, hx.2])"
            for arg, sl, _sr in c.abs_args)
        rwr = ", ".join(
            f"abs_of_{'nonpos' if sr == 'le' else 'nonneg'} "
            f"(show {('' if sr == 'le' else '0 ≤ ')}{_kink_expr_lean(arg, x)}"
            f"{' ≤ 0' if sr == 'le' else ''} by linarith [hx.1, hx.2])"
            for arg, _sl, sr in c.abs_args)
        L.append(f"/-- The closed form agrees with the piecewise `f` on `[{c.a}, {c.b}]`. -/\n"
                 f"theorem {nm}_expr_eq : ∀ x ∈ Set.Icc {a} {b}, {fe} = {nm}_f x := by\n"
                 f"  intro x hx\n"
                 f"  simp only [{nm}_f]\n"
                 f"  rcases le_or_gt x {k} with h | h\n"
                 f"  · rw [if_pos h{', ' + rwl if rwl else ''}]\n"
                 f"    simp only [{nm}_L, {_ev(c.left)}]\n"
                 f"    ring\n"
                 f"  · rw [if_neg (not_le.mpr h){', ' + rwr if rwr else ''}]\n"
                 f"    simp only [{nm}_R, {_ev(c.right)}]\n"
                 f"    ring\n")
        L.append(f"theorem {nm}_expr_min : ∀ x ∈ Set.Icc {a} {b}, {v} ≤ {fe} := by\n"
                 f"  intro x hx\n"
                 f"  rw [{nm}_expr_eq x hx]\n"
                 f"  exact {nm} x hx\n")
        L.append(f"theorem {nm}_expr_isLeast :\n"
                 f"    IsLeast ((fun x : ℝ => {fe}) '' Set.Icc {a} {b}) {v} := by\n"
                 f"  refine ⟨⟨{k}, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩\n"
                 f"  · simp only\n"
                 f"    rw [{nm}_expr_eq {k} ⟨by norm_num, by norm_num⟩, {nm}_value]\n"
                 f"  · rintro _ ⟨x, hx, rfl⟩\n"
                 f"    exact {nm}_expr_min x hx\n")
        n += 3
    return "\n".join(L), n


if __name__ == "__main__":
    print("=== positive: concave f = -(x²)+x on [0,1] (f'' = -2 ≤ 0) ===")
    c = curvature_boundary_certificate()
    print(f"  cert OK: mode={c.mode}, f={c.f_expr}, f''={c.f2}, "
          f"endpoints f({c.a})={c.fa}, f({c.b})={c.fb}")

    print("\n=== positive: convex f = x² on [0,1] (f'' = 2 ≥ 0) ===")
    cx = curvature_boundary_certificate(mode="convex", f_expr="x**2")
    print(f"  cert OK: mode={cx.mode}, f''={cx.f2}, "
          f"endpoints f(0)={cx.fa}, f(1)={cx.fb}")

    print("\n=== positive: affine f = 2*x + 1 on [0,1] (f'' = 0) ===")
    ca = curvature_boundary_certificate(mode="affine", f_expr="2*x + 1")
    print(f"  cert OK: mode={ca.mode}, f''={ca.f2}, "
          f"endpoints f(0)={ca.fa}, f(1)={ca.fb}")

    print("\n=== NEGATIVE CONTROL: mode='concave' but f = x² (f'' = 2 > 0) ===")
    try:
        curvature_boundary_certificate(mode="concave", f_expr="x**2")
        raise SystemExit("FAIL: wrong-sign curvature was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:100]}...")

    print("\n=== NEGATIVE CONTROL: mode='affine' but f = -(x²)+x (f'' = -2 ≠ 0) ===")
    try:
        curvature_boundary_certificate(mode="affine", f_expr="-(x**2)+x")
        raise SystemExit("FAIL: nonzero curvature affine claim was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:100]}...")
