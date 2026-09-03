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
        for inst in fam.instances:
            cert: CurvatureBoundaryCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
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
