# Analytic Certificate Structures — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add five reusable analytic-certificate capabilities to Telperion: an Arb transcendental-constant enclosure provider (#1), a box-robust kernel-theorem emitter (#2), a statement-match gate (#4), a hyperbolicity/real-rootedness emitter (#3, d=2), and a Turán/log-concavity emitter (#5).

**Architecture:** #1 provides certified rational boxes for transcendental constants (a documented non-kernel input, using python-flint/Arb). #2 emits `∀ c in box, P(c) ≥ 0` kernel theorems via a corner-product/`nlinarith` method. #3 and #5 are applications of #2 (real-rootedness via discriminant bridge; 3-term log-concavity). #4 is an emitter feature emitting a kernel-enforced statement-match `example` alongside any theorem. All follow the established first-class-emitter pattern.

**Tech Stack:** Python 3.14 (`fractions.Fraction`, `sympy`, `python-flint` for Arb, `mpmath` as oracle), Telperion emitter framework, Lean 4 + Mathlib v4.32.0, `lake`, warm-verify.

**Spec:** `docs/superpowers/specs/2026-09-05-analytic-cert-structures-design.md`

## Global Constraints

- **Worktree:** `/Users/peterwmurphy/telperion-analytic`, branch `telperion/analytic-cert-structures` (off `origin/main`). Do NOT switch branches; do NOT touch other worktrees.
- **Python invocation:** from `/Users/peterwmurphy/telperion-analytic/telperion`, use `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest …` (Python 3.14.6; has `python-flint` 0.9.0, `mpmath` 1.3.0, `sympy` 1.14.0; telperion imports via `src/` layout). Bare `python`/`pytest` do NOT work.
- **Certificate path is exact-rational only** (`Fraction`/`sympy.Rational`); `float`/`mpmath`/`flint` appear only in enclosure computation and test oracles, never in emitted Lean literals.
- **First-class emitter pattern** (per `src/telperion/emit_interlacing.py`): certificate dataclass + `certify_<kind>_point` (raises `ValueError` to refuse) + `<Name>Emitter(Emitter)` with `__post_init__` setting `self.kind` + `emit_body` + `<kind>_family` + register in `certify.py` `_SPECIAL_KINDS` and `_SPECIAL_DISPATCH` + export from `__init__.py`.
- **Lean = local warm verify:** copy `lean-toolchain` + `lakefile.toml` + `lake-manifest.json` from an existing example (`examples/interlacing/lean` or similar), run `/Users/peterwmurphy/.elan/bin/lake exe cache get` FIRST (downloads prebuilt Mathlib oleans — SoC-safe), then `/Users/peterwmurphy/.elan/bin/lake build`. NEVER trigger a from-scratch Mathlib compile.
- **Kernel bar:** emitted Lean builds sorry-free, axioms ⊆ `{propext, Classical.choice, Quot.sound}`.
- **No emoji anywhere.** Honesty flag `conjecture1_proved = False` in every new module docstring / Lean header.
- **Lean tactic note:** exact statements + Mathlib toolkit are given; tactic blocks are developed against the kernel. A task is done only on a green `lake build`.

---

### Task 1: #1 Arb transcendental-constant enclosure provider

**Files:**
- Create: `src/telperion/arb_enclosure.py`
- Test: `tests/test_arb_enclosure.py`

**Interfaces:**
- Produces: `enclose_constant(spec: str | Callable, prec_bits: int) -> tuple[Fraction, Fraction]` — rigorous outward-rounded rational `(lo, hi)` containing the real part of the constant. `spec` is one of `"pi"`, `"e"`, `"zeta(<rational>)"`, `"gamma(<rational>)"`, or a callable `ctx -> acb`.
- Produces: `EnclosureRecord` dataclass `(spec: str, prec_bits: int, lo: Fraction, hi: Fraction, radius: Fraction)` with `.to_dict()`.
- Produces: `_arb_ball_to_fractions(arb_ball) -> tuple[Fraction, Fraction]` (lifted from the Jensen `coefficients.py`: exact dyadic `mid ± rad` via `man_exp()`, outward).

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_arb_enclosure.py
from fractions import Fraction
import mpmath
from telperion.arb_enclosure import enclose_constant, EnclosureRecord

def _contains(lohi, val):
    lo, hi = lohi
    return float(lo) <= val <= float(hi)

def test_pi_enclosure_contains_oracle():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("pi", prec_bits=300)
    assert lo <= hi
    assert _contains((lo, hi), float(mpmath.pi))

def test_zeta_half_enclosure_contains_oracle():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("zeta(1/2)", prec_bits=300)
    assert _contains((lo, hi), float(mpmath.zeta(mpmath.mpf("0.5"))))

def test_gamma_quarter_enclosure():
    mpmath.mp.dps = 60
    lo, hi = enclose_constant("gamma(1/4)", prec_bits=300)
    assert _contains((lo, hi), float(mpmath.gamma(mpmath.mpf("0.25"))))

def test_width_shrinks_with_precision():
    lo1, hi1 = enclose_constant("pi", prec_bits=100)
    lo2, hi2 = enclose_constant("pi", prec_bits=300)
    assert (hi2 - lo2) < (hi1 - lo1)

def test_returns_fractions_outward():
    lo, hi = enclose_constant("e", prec_bits=200)
    assert isinstance(lo, Fraction) and isinstance(hi, Fraction)
    import mpmath as mp; mp.mp.dps = 80
    assert lo <= Fraction(mp.mpf(1).__class__(mp.e)).limit_denominator(10**60) or _contains((lo, hi), float(mp.e))

def test_record_roundtrip():
    lo, hi = enclose_constant("pi", prec_bits=200)
    rec = EnclosureRecord(spec="pi", prec_bits=200, lo=lo, hi=hi, radius=(hi - lo) / 2)
    d = rec.to_dict()
    assert d["spec"] == "pi" and Fraction(d["lo"]) == lo
```

- [ ] **Step 2: Run to verify fail** — `PYTHONPATH=src …python3 -m pytest tests/test_arb_enclosure.py -v` → FAIL (ModuleNotFoundError).

- [ ] **Step 3: Implement** `src/telperion/arb_enclosure.py`:
  - `import flint` (`from flint import acb, arb, ctx`); raise a clear `RuntimeError` if unavailable.
  - `_dyadic(arb_scalar) -> Fraction` via `man_exp()` (signed mantissa; `Fraction(man) * Fraction(2)**exp`), and `_arb_ball_to_fractions(ball)` returning `(mid - rad, mid + rad)` outward.
  - `_eval_spec(spec, prec_bits) -> acb`: parse `"pi"`→`acb.pi()`, `"e"`→`acb(1).exp()`, `"zeta(q)"`→`acb(str(q)).zeta()`, `"gamma(q)"`→`acb(str(q)).gamma()`, or call a passed callable with the flint module. Set `ctx.prec = prec_bits` (save/restore).
  - `enclose_constant(spec, prec_bits)`: eval, take `.real`, return `_arb_ball_to_fractions`.
  - `EnclosureRecord` frozen dataclass with `to_dict` (stringify Fractions).
  - Module docstring: this is a certified rational-box provider; **box membership is a documented non-kernel input** (Arb ball arithmetic is certified; Lean does not verify the constant's value). `conjecture1_proved = False`.

- [ ] **Step 4: Run to verify pass** — same pytest → PASS (fix any oracle-literal edge in `test_returns_fractions_outward` by using the `_contains` form).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/arb_enclosure.py tests/test_arb_enclosure.py
git commit -m "feat(telperion): Arb transcendental-constant enclosure provider (#1)"
```

---

### Task 2: #2 box-robust kernel emitter (cert + emit + example + green build)

**Files:**
- Create: `src/telperion/emit_box_robust.py`
- Modify: `src/telperion/certify.py` (add `"box_robust"` to `_SPECIAL_KINDS` and `_SPECIAL_DISPATCH`)
- Modify: `src/telperion/__init__.py` (export `BoxRobustEmitter`, `box_robust_family`)
- Create: `examples/box_robust/generate.py`, `examples/box_robust/lean/{lakefile.toml,lean-toolchain,lake-manifest.json}`, frozen output
- Test: `tests/test_box_robust.py`

**Interfaces:**
- Consumes: the `Emitter` base (`workflow.py`), `rat_lean` (`expr.py`), the family/certify machinery (`certify_interlacing_point` as the reference shape), and optionally `enclose_constant` (Task 1) to source a box in the example.
- Produces: `box_robust_family(name, symbols, grid, lean_name, spec)` where `spec(pt) -> (box, target_expr, var_syms)`; `box` = list of `(Fraction, Fraction)`, `target_expr` = a sympy separable-quadratic in `var_syms` (sum of `±(affine)^2` and `±(var_i*var_j)` and constants).
- Produces (Lean): `theorem <name> : ∀ v0 … vn : ℝ, lo0 ≤ v0 → v0 ≤ hi0 → … → 0 ≤ <target> := by …`
- Produces: `box_min_lower_bound(box, target_expr, var_syms) -> Fraction` (rigorous rational lower bound of `target` over the box via corner products for bilinear terms + endpoint-nearest for squares). Refuse via `ValueError` if `< 0`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_box_robust.py
from fractions import Fraction as F
import sympy as sp
from telperion.emit_box_robust import box_min_lower_bound, BoxRobustEmitter, box_robust_family
from telperion import certify

def test_box_min_positive_turan_shape():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    target = c1**2 - 4*c0*c2
    box = [(F(1,2), F(1,2)), (F(1), F(1)), (F(0), F(0))]  # c1^2 - 0 = 1 > 0
    m = box_min_lower_bound(box, target, (c0, c1, c2))
    assert m > 0

def test_box_min_refuses_negative():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    target = c1**2 - 4*c0*c2
    box = [(F(1), F(1)), (F(1), F(1)), (F(1), F(1))]  # 1 - 4 = -3 < 0
    m = box_min_lower_bound(box, target, (c0, c1, c2))
    assert m < 0

def test_emit_produces_forall_theorem():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    fam = box_robust_family(
        "BoxDemo", (), _grid_one(),
        lambda pt: "box_demo_0",
        lambda pt: ([(F(1,2),F(1,2)),(F(1),F(1)),(F(0),F(0))], c1**2 - 4*c0*c2, (c0,c1,c2)),
    )
    cf = certify(fam)
    text, n = BoxRobustEmitter().emit_body(cf, _profile())
    assert n == 1 and "≤" in text and "∀" in text
```

(`_grid_one`, `_profile` helpers: a single-point `GridSpec` and a `LeanProfile` — copy the shape from `examples/interlacing/generate.py`.)

- [ ] **Step 2: Run to verify fail** — FAIL (ModuleNotFoundError).

- [ ] **Step 3: Implement** `emit_box_robust.py`:
  - `box_min_lower_bound`: decompose `target` into square terms and bilinear/constant terms; lower-bound squares by endpoint-nearest-to-zero (0 if straddling), upper/lower-bound each bilinear `k*vi*vj` by the extremal of the 4 corner products (sign-aware), sum exactly as `Fraction`.
  - `BoxRobustPayload(box, target, var_names, margin)`; `certify_box_robust_point` computes margin, refuses if `< 0`.
  - `BoxRobustEmitter.emit_body`: render the `∀`-theorem; proof `by nlinarith [sq_nonneg (vi - lo_i), sq_nonneg (hi_i - vi), mul_nonneg …four corners…, (norm_num margin fact)]`. Use `rat_lean` for all box literals.
  - `box_robust_family` returns `InequalityFamily(..., special=("box_robust", spec))`.
  - Register in `certify.py` (`_SPECIAL_KINDS += ("box_robust",)`; `_SPECIAL_DISPATCH["box_robust"] = ("emit_box_robust", "certify_box_robust_point")`) and export from `__init__.py`.

- [ ] **Step 4: Python tests pass** — pytest green.

- [ ] **Step 5: Example + WARM BUILD.** Write `examples/box_robust/generate.py` (a `--check` driver like `examples/rational_identity/generate.py`) whose family sources its box from `enclose_constant("zeta(1/2)", 300)` (demonstrating #1→#2) and proves a separable-quadratic ≥ 0 over it. Set up `examples/box_robust/lean/` (copy toolchain+lakefile+manifest from an existing example; one `lean_lib`). Run `generate.py`, then `lake exe cache get` and `lake build` → green, sorry-free, `#print axioms` clean.

- [ ] **Step 6: Commit**

```bash
git add src/telperion/emit_box_robust.py src/telperion/certify.py src/telperion/__init__.py examples/box_robust/ tests/test_box_robust.py
git commit -m "feat(telperion): box-robust kernel emitter (#2) -- forall-box quadratic nonneg via nlinarith"
```

---

### Task 3: #4 statement-match gate (utility + wire into Emitter + demo on #2)

**Files:**
- Create: `src/telperion/statement_match.py`
- Modify: `src/telperion/workflow.py` (add an opt-in `emit_gate` helper on `Emitter`)
- Modify: `src/telperion/emit_box_robust.py` (emit a gate example per theorem)
- Modify: `examples/box_robust/` frozen Lean (regenerate with gates), warm build
- Test: `tests/test_statement_match.py`

**Interfaces:**
- Produces: `statement_match_example(theorem_name: str, explicit_type: str) -> str` returning `example : <explicit_type> := <theorem_name>\n`.
- Produces: `Emitter.emit_gate(self, name: str, type_str: str) -> str` (calls the above; returns "" when gating disabled).

- [ ] **Step 1: Write the failing test**

```python
# tests/test_statement_match.py
from telperion.statement_match import statement_match_example

def test_gate_text_shape():
    g = statement_match_example("my_thm", "∀ x : ℝ, 0 ≤ x^2")
    assert g.strip() == "example : ∀ x : ℝ, 0 ≤ x^2 := my_thm"

def test_gate_uses_exact_type():
    # the ascribed type must be exactly what is passed (no truncation/normalization)
    t = "(A → B → C)"
    assert t in statement_match_example("t", t)
```

- [ ] **Step 2: Run to verify fail** — FAIL.

- [ ] **Step 3: Implement** `statement_match.py` (`statement_match_example`), add `Emitter.emit_gate`, and have `BoxRobustEmitter.emit_body` append `emit_gate(thm_name, thm_type_str)` after each theorem, where `thm_type_str` is the full `∀ … 0 ≤ target` type it just rendered (build the type string once, reuse for both the theorem signature and the gate — guarantees identical types).

- [ ] **Step 4: Python test pass + regenerate #2 example + WARM BUILD green** (the gate `example`s must compile — a build-enforced statement match).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/statement_match.py src/telperion/workflow.py src/telperion/emit_box_robust.py examples/box_robust/ tests/test_statement_match.py
git commit -m "feat(telperion): kernel-enforced statement-match gate (#4) + wire into box_robust"
```

---

### Task 4: #3 hyperbolicity emitter (bridge lemma + emitter + 2-family example + green build)

**Files:**
- Create: `src/telperion/emit_hyperbolicity.py`
- Create: `examples/hyperbolicity/lean/HyperbolicityBridge.lean` (the d=2 prelude lemma), `examples/hyperbolicity/generate.py`, `examples/hyperbolicity/lean/{lakefile.toml,lean-toolchain,lake-manifest.json}`
- Modify: `src/telperion/certify.py`, `src/telperion/__init__.py` (register `"hyperbolicity"`)
- Test: `tests/test_hyperbolicity.py`

**Interfaces:**
- Consumes: `box_min_lower_bound` (#2) for the discriminant margin, `emit_gate` (#4), `rat_lean`.
- Produces (Lean prelude): `hyperbolic_deg2_of_discrim_nonneg (a b c : ℝ) (ha : a ≠ 0) (h : 0 ≤ b^2 - 4*a*c) : (Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c).roots.card = 2`.
- Produces: `hyperbolicity_family(name, symbols, grid, lean_name, spec)` where `spec(pt) -> (coeff_box, degree)`; `coeff_box` = list of `(Fraction,Fraction)` for `[a_0..a_d]` (constant→leading).
- Produces (Lean theorem): `∀ a0 … ad : ℝ, (box bounds) → (C a_d * X^d + … + C a_0).roots.card = d`.

- [ ] **Step 1: Bridge lemma.** Create `HyperbolicityBridge.lean` with the d=2 lemma stated `:= by sorry`; set up the example dir (copy toolchain/lakefile/manifest); `lake exe cache get`; `lake build` (builds with sorry warning — confirms wiring). This lemma is the generalization of the Jensen bridge; toolkit: `Mathlib.Algebra.QuadraticDiscriminant` (`discrim`, `quadratic_eq_zero_iff`), `Real.sqrt`/`Real.sq_sqrt`, `Polynomial.roots_C_mul`, `Polynomial.roots_mul`, `Polynomial.roots_X_sub_C`.

- [ ] **Step 2: Discharge the bridge** (remove sorry); `lake build` green; `#print axioms` clean.

- [ ] **Step 3: Write the failing Python test**

```python
# tests/test_hyperbolicity.py
from fractions import Fraction as F
from telperion.emit_hyperbolicity import HyperbolicityEmitter, hyperbolicity_family
from telperion import certify

def test_refuses_negative_discriminant():
    # box for a=c2, b=c1, c=c0 with c1^2 - 4 c0 c2 < 0 must refuse
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h0",
        lambda pt: ([(F(1),F(1)),(F(1),F(1)),(F(1),F(1))], 2))  # disc = 1-4 = -3
    try:
        certify(fam); assert False
    except Exception:
        pass

def test_emit_real_rooted_quadratic():
    # a real-rooted quadratic box: a0=-1..-1, a1=0..0, a2=1..1 -> x^2 - 1, disc=0-4*(-1)*1=4>0
    fam = hyperbolicity_family("H", (), _grid_one(), lambda pt: "h_x2m1",
        lambda pt: ([(F(-1),F(-1)),(F(0),F(0)),(F(1),F(1))], 2))
    text, n = HyperbolicityEmitter().emit_body(certify(fam), _profile())
    assert "roots.card = 2" in text and "hyperbolic_deg2_of_discrim_nonneg" in text
```

- [ ] **Step 4: Implement** `emit_hyperbolicity.py`: payload `(coeff_box, degree, discrim_margin, leading_sign)`; `certify_hyperbolicity_point` builds discriminant target `a1^2 - 4*a0*a2` (for d=2), computes margin via `box_min_lower_bound`, refuses if `≤ 0` or if the leading-coeff box straddles 0; `emit_body` emits the `∀`-box theorem chaining leading-coeff `≠ 0` + box-robust discriminant `≥ 0` + `hyperbolic_deg2_of_discrim_nonneg`, plus the #4 gate. Register `"hyperbolicity"`; the emitter's `requires_prelude = ("hyperbolic_deg2_of_discrim_nonneg",)` and the example imports `HyperbolicityBridge`.

- [ ] **Step 5: Python tests pass.**

- [ ] **Step 6: Example on TWO families + WARM BUILD.** `generate.py` emits real-rootedness certs for two distinct quadratic families (e.g. `x^2 - 1` and `x^2 - 3x + 2`, both via rational boxes) to prove genericity; `lake build` green, sorry-free, axioms clean, gates compile.

- [ ] **Step 7: Commit**

```bash
git add src/telperion/emit_hyperbolicity.py examples/hyperbolicity/ src/telperion/certify.py src/telperion/__init__.py tests/test_hyperbolicity.py
git commit -m "feat(telperion): hyperbolicity emitter (#3, d=2) -- roots.card=degree via discriminant bridge"
```

---

### Task 5: #5 turan-box emitter (convenience over #2 + example + green build)

**Files:**
- Create: `src/telperion/emit_turan_box.py` (thin: a `turan_box_family` + reuse of #2's certify/emit)
- Modify: `src/telperion/certify.py`, `src/telperion/__init__.py` (register `"turan_box"`)
- Create: `examples/turan_box/generate.py` + `lean/` + frozen
- Test: `tests/test_turan_box.py`

**Interfaces:**
- Consumes: `box_min_lower_bound`, `BoxRobustEmitter` machinery (#2), `emit_gate` (#4).
- Produces: `turan_box_family(name, symbols, grid, lean_name, spec)` where `spec(pt) -> (a0_box, a1_box, a2_box)` (three interval-enclosed consecutive sequence values); internally builds `target = a1^2 - a0*a2` and delegates to the #2 certifier/emitter.
- Produces (Lean): `∀ a0 a1 a2 : ℝ, (box bounds) → 0 ≤ a1^2 - a0*a2` (3-term log-concavity / Turán).

- [ ] **Step 1: Failing test** — `test_turan_box.py`: a log-concave triple (e.g. `a0=1,a1=2,a2=1` → `4-1=3>0`) emits a theorem containing `a1^2 - a0*a2` and `0 ≤`; a non-log-concave triple (`a0=1,a1=1,a2=2` → `1-2<0`) refuses.
- [ ] **Step 2: Run → fail.**
- [ ] **Step 3: Implement** `emit_turan_box.py` delegating to #2 (`target = a1**2 - a0*a2`); register `"turan_box"`.
- [ ] **Step 4: Python tests pass.**
- [ ] **Step 5: Example + WARM BUILD** green sorry-free, gates compile.
- [ ] **Step 6: Commit** `feat(telperion): turan-box emitter (#5) -- 3-term log-concavity over enclosed sequence values`.

---

### Task 6: CI jobs + capability doc + CHANGELOG

**Files:**
- Modify: `.github/workflows/telperion-lean-e2e.yml` (add `box-robust-compiles`, `hyperbolicity-compiles`, `turan-box-compiles` jobs)
- Create: `docs/ANALYTIC_CERT_STRUCTURES.md`
- Modify: `CHANGELOG.md`
- Test: (CI config validated by YAML parse + presence check)

**Interfaces:** Consumes all example dirs from Tasks 2–5.

- [ ] **Step 1:** Add three CI jobs matching the existing per-example pattern (checkout, setup-python 3.12, `pip install sympy pytest mpmath python-flint`, `python examples/<name>/generate.py --check`, cache elan, install elan, `lake exe cache get`, `lake build`). Validate: `python3 -c "import yaml; d=yaml.safe_load(open('.github/workflows/telperion-lean-e2e.yml')); assert all(j in d['jobs'] for j in ['box-robust-compiles','hyperbolicity-compiles','turan-box-compiles'])"`.
- [ ] **Step 2:** Write `docs/ANALYTIC_CERT_STRUCTURES.md`: the five capabilities, the #1 non-kernel-input trust boundary, the deferred extensions (general Bezoutian engine; d≥3 bridges; exhaustive special functions), `conjecture1_proved = False`. Update `CHANGELOG.md`.
- [ ] **Step 3: Commit** `docs(telperion): CI jobs + capability doc + changelog for analytic cert structures`.

---

## Self-Review

**Spec coverage:** #1 → Task 1 ✓. #2 → Task 2 ✓. #4 → Task 3 ✓ (built before #3/#5 so they use it). #3 (d=2) → Task 4 ✓. #5 → Task 5 ✓. CI/docs/§6 testing → Task 6 + per-task warm builds ✓. Non-kernel-input boundary (#1) → Task 1 docstring + Task 6 doc ✓. Deferred extensions (Bezoutian, d≥3) → Task 6 doc ✓.

**Placeholder scan:** Python steps carry runnable code; Lean steps carry exact statements + Mathlib toolkit + a hard warm-build gate (the honest granularity for kernel proofs). No "TBD/handle edge cases". The `_grid_one`/`_profile` test helpers are explicitly pointed at `examples/interlacing/generate.py` as the shape to copy.

**Type consistency:** `enclose_constant`/`EnclosureRecord` (T1) → used in T2 example. `box_min_lower_bound`/`box_robust_family`/`BoxRobustEmitter` (T2) → consumed by T4/T5. `statement_match_example`/`emit_gate` (T3) → used by T4/T5. `hyperbolic_deg2_of_discrim_nonneg` (T4) consistent between the prelude lemma and the emitter's `requires_prelude`. `turan_box_family` (T5) delegates to T2. Registration edits (`_SPECIAL_KINDS`, `_SPECIAL_DISPATCH`, `__init__`) named consistently across T2/T4/T5.
