"""range_completeness_decide emitter -- "every m < N satisfying P is in the explicit list",
decided by `decide +kernel` against a kernel-friendly surrogate and bridged to the real
property (CN-1 emitter survey item N6, a face of finite_decide).

These tests pin, in order: the finite_decide AST extension (exact evaluation and rendering of
ForallRange / ForallIcc / Not / And / Mem / NotMem / Mod / dvd, and that the pre-existing
nodes render exactly as before); the certify-time refusals (false coverage, vacuous coverage,
weak surrogate bound, duplicates, unsound list, floats); the emitted text; the registry
classification and the negative-control adapter; and, Lean-gated, the example compiling
axiom-clean plus the two-sided kernel negative control (drop one element, kernel rejects).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_finite_decide import (  # noqa: E402
    And, Cmp, FiniteDecideEmitter, ForallIcc, ForallIn, ForallRange, Imp, Lit, Mem, Mod,
    Mul, NatTable, Not, NotMem, Var, _eval_prop, _lean_prop, finite_decide_family,
)
from telperion.emit_range_completeness import (  # noqa: E402
    RangeCompletenessEmitter,
    SquarefreeSurrogate,
    range_completeness_certificate,
    range_completeness_family,
    render_instance,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

HEEGNER_NINE = (1, 2, 3, 7, 11, 19, 43, 67, 163)


def _sqf(n, k):
    return [m for m in range(n) if all(m % (j * j) != 0 for j in range(2, k + 1))]


def _members_200():
    return [m for m in _sqf(200, 15) if m not in HEEGNER_NINE]


# --- 1. the AST extension ---------------------------------------------------------------

def test_new_nodes_evaluate_exactly():
    tables = {"L": NatTable("L", [1, 2, 3, 5]), "X": NatTable("X", [2])}
    c = [0]
    # every m < 6 with no square factor k*k (k in 2..2) and m not in X is in L
    prop = ForallRange("m", 6,
                       Imp(ForallIcc("k", 2, 2, Not(Cmp("dvd", Mul(Var("k"), Var("k")), Var("m")))),
                           Imp(NotMem(Var("m"), "X"), Mem(Var("m"), "L"))))
    # m = 0: 4 ∣ 0 so the guard fails; m = 4 fails the guard; 2 is excluded; 1, 3, 5 in L.
    assert _eval_prop(prop, {}, tables, c) is True
    assert c[0] > 0
    # drop 5 and the coverage is false
    tables["L"] = NatTable("L", [1, 2, 3])
    assert _eval_prop(prop, {}, tables, [0]) is False
    assert _eval_prop(And(Cmp("eq", Mod(Var("m"), Lit(4)), Lit(3)), Cmp("lt", Var("m"), Lit(8))),
                      {"m": 7}, tables, [0]) is True
    assert _eval_prop(Cmp("dvd", Lit(0), Lit(0)), {}, tables, [0]) is True   # Lean: 0 ∣ 0
    assert _eval_prop(Cmp("dvd", Lit(0), Lit(3)), {}, tables, [0]) is False


def test_new_nodes_render_with_lean_precedence():
    guard = ForallIcc("k", 2, 15, Not(Cmp("dvd", Mul(Var("k"), Var("k")), Var("m"))))
    prop = ForallRange("m", 200, Imp(guard, Imp(NotMem(Var("m"), "excl"), Mem(Var("m"), "list"))))
    assert _lean_prop(prop, "t") == (
        "∀ m ∈ Finset.range 200, (∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m) → "
        "m ∉ t_excl → m ∈ t_list")
    # a binder under ∧ or ¬ is parenthesised; an atom is not
    assert _lean_prop(And(Cmp("lt", Var("m"), Lit(9)), guard), "t") == (
        "m < 9 ∧ (∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m)")
    assert _lean_prop(Not(Imp(Cmp("lt", Var("m"), Lit(9)), Mem(Var("m"), "L"))), "t") == (
        "¬ (m < 9 → m ∈ t_L)")
    assert _lean_prop(Cmp("eq", Mod(Var("m"), Lit(4)), Lit(3)), "t") == "(m % 4) = 3"


def test_pre_existing_nodes_render_exactly_as_before():
    """The finite_decide example's output must not move: a Cmp hypothesis stays unparenthesised."""
    prop = ForallIn("a", "keys", Imp(Cmp("le", Var("a"), Lit(2)), Cmp("eq", Var("a"), Lit(1))))
    assert _lean_prop(prop, "p") == "∀ a ∈ p_keys, a ≤ 2 → a = 1"


def test_finite_decide_emitter_renders_the_face_too():
    """The face belongs to finite_decide: its emitter states a range coverage by `decide`."""
    def spec(pt):
        tables = [NatTable("L", [0, 1, 2, 3])]
        return tables, ForallRange("m", 4, Mem(Var("m"), "L"))
    fam = finite_decide_family("FD", GridSpec([("i", [0])]), lambda pt: "fd_cov", spec)
    rep = emit(certify(fam), LeanProfile(namespace=("T",)), [FiniteDecideEmitter()],
               ValidationReport(checks=(("x", True),)))
    txt = next(iter(rep.files.values()))
    assert "theorem fd_cov : ∀ m ∈ Finset.range 4, m ∈ fd_cov_L := by decide" in txt


# --- 2. certification and refusals -------------------------------------------------------

def test_certificate_accepts_the_squarefree_table():
    cert, n_checks = range_completeness_certificate(
        200, _members_200(), exclude=HEEGNER_NINE, surrogate=SquarefreeSurrogate(15),
        emit_length=True, emit_nodup=True, emit_soundness=True)
    assert len(cert.members) == 113 and n_checks > 200


def test_refuses_a_dropped_element_naming_it():
    members = [m for m in _members_200() if m != 199]
    with pytest.raises(ValueError, match=r"coverage is FALSE.*m = 199"):
        range_completeness_certificate(200, members, exclude=HEEGNER_NINE,
                                       surrogate=SquarefreeSurrogate(15))


def test_refuses_a_weak_surrogate_bound():
    """K = 14 against N = 200: 14^2 = 196 <= 200, refused even though the bridge is sound."""
    with pytest.raises(ValueError, match=r"K\^2 > N fails"):
        range_completeness_certificate(200, _members_200(), exclude=HEEGNER_NINE,
                                       surrogate=SquarefreeSurrogate(14))
    with pytest.raises(ValueError, match="REFUSED"):
        range_completeness_certificate(10, [1, 2, 3], surrogate=SquarefreeSurrogate(1))


def test_refuses_vacuous_coverage():
    with pytest.raises(ValueError, match="vacuous"):
        range_completeness_certificate(5, [], exclude=[0, 1, 2, 3, 4])
    with pytest.raises(ValueError, match="REFUSED"):
        range_completeness_certificate(0, [])


def test_refuses_duplicates_and_unsound_lists_only_when_requested():
    sq = _sqf(10, 4)                                   # 1 2 3 5 6 7
    range_completeness_certificate(10, sq + [1], surrogate=SquarefreeSurrogate(4))
    with pytest.raises(ValueError, match="nodup requested"):
        range_completeness_certificate(10, sq + [1], surrogate=SquarefreeSurrogate(4),
                                       emit_nodup=True)
    range_completeness_certificate(10, sq + [4], surrogate=SquarefreeSurrogate(4))
    with pytest.raises(ValueError, match=r"soundness requested but 4"):
        range_completeness_certificate(10, sq + [4], surrogate=SquarefreeSurrogate(4),
                                       emit_soundness=True)


@pytest.mark.parametrize("kw", [
    dict(n=10.0, members=[1]),
    dict(n=10, members=[1, 2.5]),
    dict(n=10, members=[1], exclude=[-1]),
    dict(n=10, members=[True]),
])
def test_refuses_floats_negatives_and_bools(kw):
    with pytest.raises(ValueError, match="exact natural number"):
        range_completeness_certificate(**kw)


def test_certify_propagates_the_refusal():
    fam = range_completeness_family(
        "Bad", GridSpec([("i", [0])]), lambda pt: "bad",
        spec=lambda pt: dict(n=200, members=[m for m in _members_200() if m != 199],
                             exclude=HEEGNER_NINE, surrogate=SquarefreeSurrogate(15)))
    with pytest.raises(Exception, match="coverage is FALSE"):
        certify(fam)


# --- 3. emission -------------------------------------------------------------------------

def _emit_text(name="rc_t", **kw):
    fam = range_completeness_family(
        "RangeCompletenessTest", GridSpec([("i", [0])]), lambda pt: name,
        spec=lambda pt: dict(kw))
    report = emit(certify(fam), LeanProfile(namespace=("RangeCompletenessTest",)),
                  [RangeCompletenessEmitter()],
                  ValidationReport(checks=(("range_completeness", True),)))
    return next(iter(report.files.values()))


def test_kind_and_emitter_for():
    fam = range_completeness_family("T", GridSpec([("i", [0])]), lambda pt: "t",
                                    spec=lambda pt: dict(n=4, members=[0, 1, 2, 3]))
    assert fam.kind == "range_completeness_decide"
    assert emitter_for("range_completeness_decide").kind == "range_completeness_decide"


def test_emit_shape_is_deterministic_and_lint_clean():
    kw = dict(n=200, members=_members_200(), exclude=HEEGNER_NINE,
              surrogate=SquarefreeSurrogate(15), emit_length=True, emit_nodup=True,
              emit_soundness=True)
    txt = _emit_text(**kw)
    assert txt == _emit_text(**kw), "emission is not byte-deterministic"
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == [], errs
    for banned in ("sorry", "admit", "native_decide", "axiom ", "maxHeartbeats"):
        assert banned not in txt, banned
    assert ("theorem rc_t : ∀ m ∈ Finset.range 200, (∀ k ∈ Finset.Icc 2 15, ¬ (k * k) ∣ m) → "
            "m ∉ rc_t_excl → m ∈ rc_t_list := by\n  decide +kernel") in txt
    assert "set_option maxRecDepth 8192 in" in txt
    assert "theorem rc_t_sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m)" in txt
    assert ("theorem rc_t_of_squarefree : ∀ m < 200, Squarefree m → m ∉ rc_t_excl → "
            "m ∈ rc_t_list :=") in txt
    assert "theorem rc_t_length : rc_t_list.length = 113 := by\n  decide +kernel" in txt
    assert "theorem rc_t_nodup : rc_t_list.Nodup := by\n  decide +kernel" in txt
    assert "theorem rc_t_sound : ∀ m ∈ rc_t_list, m < 200 ∧" in txt
    assert "conjecture1_proved = False" in txt or "10 theorems" in txt or "6 theorems" in txt
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_companions_are_optional_and_guards_thread_through_the_consumer():
    members = [m for m in _sqf(60, 8) if m % 4 == 3]
    txt = _emit_text(name="g", n=60, members=members,
                     guards=(Cmp("eq", Mod(Var("m"), Lit(4)), Lit(3)),),
                     surrogate=SquarefreeSurrogate(8))
    assert "g_length" not in txt and "g_nodup" not in txt and "g_sound" not in txt
    assert "g_excl" not in txt
    assert ("theorem g_of_squarefree : ∀ m < 60, Squarefree m → (m % 4) = 3 → m ∈ g_list :=\n"
            "  fun m hm hsq hg1 => g m (Finset.mem_range.mpr hm) (g_sqfBelow_of_squarefree hsq) hg1"
            ) in txt
    # no surrogate: a purely decidable coverage, no bridge and no consumer theorem
    plain = _emit_text(name="p", n=4, members=[0, 1, 2, 3])
    assert "theorem p : ∀ m ∈ Finset.range 4, m ∈ p_list := by" in plain
    assert "Squarefree" not in plain


def test_example_file_matches_the_generator():
    """The island's RangeCompletenessDecide.lean is the generator's output (drift check)."""
    import importlib.util
    root = Path(__file__).resolve().parents[1] / "examples" / "range_completeness_decide"
    spec = importlib.util.spec_from_file_location("rc_generate", root / "generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert (root / "lean" / "RangeCompletenessDecide.lean").read_text(encoding="utf-8") == mod.build()
    assert (root / "lean" / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.0"


# --- 4. registry and negative-control wiring ---------------------------------------------

def test_emitter_is_classified_structurally_nonvacuous_with_adapter():
    from telperion.emitter_sensitivity import (
        NEG_CONTROL_ADAPTER, REGISTRY, STRUCTURALLY_NONVACUOUS)
    from telperion.negative_control_harness import registered_adapters
    stance = REGISTRY["RangeCompletenessEmitter"]
    assert stance.stance == STRUCTURALLY_NONVACUOUS
    assert "vacuous" in stance.reason.lower()
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "RangeCompletenessEmitter" in registered_adapters()


def test_adapter_twins_differ_in_the_list_only():
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["RangeCompletenessEmitter"]
    f, t = ad.make_false_cert(), ad.make_true_cert()
    assert t.members[-1] == 59 and f.members == t.members[:-1]
    # Layer 1 refuses the forged list on its own
    with pytest.raises(ValueError, match=r"m = 59"):
        range_completeness_certificate(f.n, f.members, exclude=f.exclude, surrogate=f.surrogate)
    ft, tt = ad.emit_call(f, "twin"), ad.emit_call(t, "twin")
    diff = [(a, b) for a, b in zip(ft.splitlines(), tt.splitlines()) if a != b]
    assert len(diff) == 1 and diff[0][0].startswith("def twin_list"), diff
    assert "twin_length" not in tt      # the control is pinned to the coverage decide


# --- 5. Lean end to end (gated on a built env) ---------------------------------------------

_ENV = Path(__file__).resolve().parents[1] / "examples" / "range_completeness_decide" / "lean"


def _env_ready():
    from lean_env import lean_env_ready
    return lean_env_ready(_ENV)


lean = pytest.mark.skipif(not _env_ready(),
                          reason="range_completeness_decide Lean env not built -- skipped")


@lean
def test_lean_example_compiles_axiom_clean():
    from telperion.verify import verify_lean
    txt = (_ENV / "RangeCompletenessDecide.lean").read_text(encoding="utf-8")
    decls = [f"RangeCompletenessDecide.{d}" for d in (
        "sqf_lt_200", "sqf_lt_200_of_squarefree", "sqf_lt_200_length", "sqf_lt_200_nodup",
        "sqf_lt_200_sound", "sqf_3mod4_lt_60_of_squarefree")]
    r = verify_lean(txt, env_dir=_ENV, decls=decls)
    assert r.okay and r.axioms_clean, (r.summary(), r.errors[:2])
    for d in decls:
        assert set(r.axioms[d]) <= {"propext", "Classical.choice", "Quot.sound"}, (d, r.axioms[d])


@lean
def test_lean_negative_control_dropped_element():
    from telperion.negative_control_harness import (
        generic_negative_control, registered_adapters)
    res = generic_negative_control(registered_adapters()["RangeCompletenessEmitter"],
                                   env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail
