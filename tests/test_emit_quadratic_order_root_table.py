"""quadratic_order_root_table emitter -- Kummer-Dedekind faces of a monogenic quadratic order.

The shape (CN-1 survey N3): for ``X^2 - t X + c`` and a prime ``p`` the kernel decides ONE face
(RAMIFIED ``p | 4c - t^2``, SPLIT ``IsRootMod t c p y``, INERT ``forall z : ZMod p, ... != 0``) and
the ``QuadraticOrderRoot`` prelude turns it into the Kummer-Dedekind statement under the
``QuadInt`` hypothesis; split primes with ``4p <= d``, ``p != c`` are class-number witnesses.

These tests pin, in order: the exact classification (hand-computed faces for d = 8, 20, 31, 56,
163); the structural control of REVIEW_E C2 (d = 8, p = 2 = c: a root exists, but the prime is
ramified and is NOT a witness, and `p != c` is the only conjunct that fails); the refusals; the
independent re-check; the emitted text; the prelude single-source; the sensitivity-registry
classification and the negative-control adapter; and, Lean-gated, an end-to-end kernel check
plus the two-sided negative control.

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_quadratic_order_root_table import (  # noqa: E402
    INERT,
    RAMIFIED,
    SPLIT,
    PrimeFace,
    QuadraticOrderRootTableEmitter,
    classify_prime,
    is_prime,
    quadratic_order_root_prelude_lean,
    quadratic_order_root_table_certificate,
    quadratic_order_root_table_family,
    root_mod,
    verify_certificate,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

_EX = Path(__file__).resolve().parents[1] / "examples" / "quadratic_order_root_table"


# --- 1. the exact classification -------------------------------------------------------

def _faces(cert):
    return [(f.p, f.face, f.y, f.witness) for f in cert.faces]


def test_d8_control_case_faces():
    """d = 8 (t = 0, c = 2, h(-8) = 1): 2 ramifies, 3 splits (not a witness), 5 and 7 are inert."""
    cert = quadratic_order_root_table_certificate(0, 2, [2, 3, 5, 7])
    assert cert.d == 8
    assert _faces(cert) == [(2, RAMIFIED, None, False), (3, SPLIT, 1, False),
                            (5, INERT, None, False), (7, INERT, None, False)]
    assert cert.witnesses == ()


def test_d163_no_root_table_and_non_witness_split():
    """d = 163 (t = 1, c = 41, h = 1): 2, 3, 5, 7 inert (CN-1's Minkowski table); 41 splits with
    y = 0 but 4 * 41 = 164 > 163 so it is NOT a witness; 163 ramifies."""
    cert = quadratic_order_root_table_certificate(1, 41, [2, 3, 5, 7, 41, 163])
    assert _faces(cert) == [(2, INERT, None, False), (3, INERT, None, False),
                            (5, INERT, None, False), (7, INERT, None, False),
                            (41, SPLIT, 0, False), (163, RAMIFIED, None, False)]
    assert cert.witnesses == ()


def test_witnesses_match_cn1_instances():
    """CN-1's w_5 : IsWitness 5 3 1, w_14 : IsWitness 14 3 1, w_31 : IsWitness 31 2 1 (we take the
    least root, y = 0 for m = 31: 0 and 1 are both roots mod 2)."""
    c20 = quadratic_order_root_table_certificate(0, 5, [2, 3, 7])
    assert _faces(c20) == [(2, RAMIFIED, None, False), (3, SPLIT, 1, True), (7, SPLIT, 3, False)]
    c56 = quadratic_order_root_table_certificate(0, 14, [2, 3, 5, 7])
    assert _faces(c56) == [(2, RAMIFIED, None, False), (3, SPLIT, 1, True),
                           (5, SPLIT, 1, True), (7, RAMIFIED, None, False)]
    c31 = quadratic_order_root_table_certificate(1, 8, [2, 5, 7])
    assert _faces(c31) == [(2, SPLIT, 0, True), (5, SPLIT, 2, True), (7, SPLIT, 3, True)]
    assert (1 * 1 - 1 * 1 + 8) % 2 == 0, "y = 1 is also a root mod 2 (CN-1's choice)"


@pytest.mark.parametrize("t,c,p,expected", [
    (0, 2, 2, (RAMIFIED, None)),
    (0, 2, 3, (SPLIT, 1)),
    (0, 2, 5, (INERT, None)),
    (1, 41, 41, (SPLIT, 0)),
    (1, 41, 163, (RAMIFIED, None)),
    (1, 41, 193, (INERT, None)),
    (0, 2, 199, (INERT, None)),
])
def test_classify_prime(t, c, p, expected):
    f = classify_prime(t, c, p)
    assert (f.face, f.y) == expected
    if f.face == SPLIT:
        assert (f.y * f.y + c - t * f.y) % p == 0 and root_mod(t, c, p) == f.y
    if f.face == INERT:
        assert root_mod(t, c, p) is None


def test_p_ne_c_only_refuses_the_t0_double_root():
    """Where `p != c` bites.  For t = 0, p = c divides d = 4c, so p is RAMIFIED (the double root
    y = 0) and the bound 4p <= d = 4p holds: `p != c` is the ONLY conjunct refusing it.  For t = 1,
    p = c can split (c = 2, p = 2: y^2 - y + 2 is even for every y) but then 4p = 4c > d = 4c - 1,
    so the bound already refuses.  Hence no split prime with 4p <= d ever has p = c."""
    for t in (0, 1):
        for c in range(1, 60):
            d = 4 * c - t * t
            for p in range(2, 60):
                if not is_prime(p):
                    continue
                f = classify_prime(t, c, p)
                if f.face == SPLIT and 4 * p <= d:
                    assert p != c and f.witness
                if p == c and t == 0:
                    assert f.face == RAMIFIED and 4 * p <= d
    f = classify_prime(1, 2, 2)
    assert f.face == SPLIT and f.y == 0 and not f.witness and 4 * 2 > 7


# --- 2. the structural control (REVIEW_E C2) ---------------------------------------------

def test_structural_control_d8_p2_root_exists_but_is_refused_by_p_ne_c():
    """d = 8, p = 2 = c, y = 0: `2 | 0^2 + 2`, `4 * 2 <= 8`, 2 is prime -- every IsWitness conjunct
    holds except `p != c`.  Since h(-8) = 1, dropping `p != c` would make the soundness lemma
    FALSE.  The generator classifies p = 2 as RAMIFIED (2 | 8) and emits no witness."""
    t, c, p, y = 0, 2, 2, 0
    assert is_prime(p)
    assert t * y <= y * y + c and (y * y + c - t * y) % p == 0
    assert 4 * p <= 4 * c - t * t
    assert p == c                                           # the one refusing conjunct
    cert = quadratic_order_root_table_certificate(t, c, [p])
    assert cert.faces[0].face == RAMIFIED and cert.witnesses == ()
    # A hand-forged "witness" at p = c fails the independent re-check.
    forged = replace(cert, faces=(PrimeFace(p, SPLIT, y, True),))
    assert not verify_certificate(forged)
    # The prelude records it as a kernel-checked theorem.
    pre = quadratic_order_root_prelude_lean()
    assert "theorem not_isWitness_two_two : ¬ IsWitness 0 2 2 0" in pre
    assert "theorem isWitness_two_two_other_conjuncts" in pre


# --- 3. refusals ----------------------------------------------------------------------

@pytest.mark.parametrize("t,c,primes", [
    (2, 1, [3]),            # t outside {0, 1}
    (-1, 5, [3]),
    (0, 0, [3]),            # c < 1
    (0, 5, []),             # empty prime list
    (0, 5, [3, 3]),         # repeated prime
    (0, 5, [9]),            # composite
    (0, 5, [1]),
    (0, 5, [10 ** 6 + 3]),  # above MAX_PRIME
    (0.0, 5, [3]),          # floats
    (0, 5.0, [3]),
    (0, 5, [3.0]),
    (0, 2, [1031]),         # inert prime above the ZMod-decide cap
])
def test_refusals(t, c, primes):
    with pytest.raises(ValueError, match="REFUSED"):
        quadratic_order_root_table_certificate(t, c, primes)


def test_inert_cap_is_explicit():
    with pytest.raises(ValueError, match="REFUSED"):
        quadratic_order_root_table_certificate(0, 2, [1031])
    cert = quadratic_order_root_table_certificate(0, 2, [1031], inert_cap=1100)
    assert cert.faces[0].face == INERT


def test_inert_face_above_100_raises_maxRecDepth_only_there():
    """The rule is `p > 100` (INERT_RECDEPTH_PRIME): the default depth fails at p = 193 and 199 and
    passes at p = 101, and the band between is unmeasured, so the knob is applied from 101 up.  It
    is an elaboration setting; the emitted Lean is the same statement either way."""
    txt = _emit_text([dict(t=0, c=2, primes=[7, 101, 199])], ["r"])
    assert "theorem r_noroot_7 : ∀ z : ZMod 7" in txt
    assert "set_option maxRecDepth 8192 in\ntheorem r_noroot_7" not in txt
    assert "set_option maxRecDepth 8192 in\ntheorem r_noroot_101 : ∀ z : ZMod 101" in txt
    assert "set_option maxRecDepth 8192 in\ntheorem r_noroot_199 : ∀ z : ZMod 199" in txt
    assert txt.count("set_option maxRecDepth") == 2
    assert txt.count("set_option maxRecDepth") == sum(1 for p in (7, 101, 199) if p > 100)


_STD = "[propext, Classical.choice, Quot.sound]"
_GUARD_ANCHORS = 24


def _real_guard_output() -> str:
    """The shape of the island's real guard output: 24 anchors, 20 with Mathlib's three axioms and
    4 (the pure `decide` tables and `not_isWitness_two_two`) with `[propext]` only."""
    names = [f"QuadraticOrderRootTable.anchor_{i}" for i in range(_GUARD_ANCHORS)]
    return "".join(f"'{n}' depends on axioms: {'[propext]' if i % 6 == 0 else _STD}\n"
                   for i, n in enumerate(names))


def _padded(bad_block: str) -> str:
    """`bad_block` plus enough standard lines to keep the anchor count at exactly 24, so a
    rejection can only come from the allow-list, never from the count pin."""
    k = sum(1 for line in bad_block.splitlines() if "depends on axioms" in line)
    pad = "".join(f"'QuadraticOrderRootTable.pad_{i}' depends on axioms: {_STD}\n"
                  for i in range(_GUARD_ANCHORS - k))
    return pad + bad_block


# bb's RealWrap.lean output (REVIEW_PR766 Add.1): a native_decide twin of d56_classNumber_ne_one.
# Lean wraps the long list one axiom per line; a line-based check reads only `[propext,`.
_REALWRAP = (
    "'QuadraticOrderRootTable.d56_classNumber_ne_one' depends on axioms: "
    "[propext, Classical.choice, Quot.sound]\n"
    "'QuadraticOrderRootTable.d56_classNumber_ne_one_nd' depends on axioms: [propext,\n"
    " Classical.choice,\n"
    " Quot.sound,\n"
    " QuadraticOrderRootTable.d56_classNumber_ne_one_nd._native.native_decide.ax_1_1]\n")
_WRAPPED_SORRY = (
    "'QuadraticOrderRootTable.d8' depends on axioms: [propext,\n"
    " sorryAx]\n")
_LOOKALIKE = "'QuadraticOrderRootTable.d8' depends on axioms: [propext, Classical_choice, Quot.sound]\n"
_NO_AXIOMS = "".join(f"'QuadraticOrderRootTable.anchor_{i}' does not depend on any axioms\n"
                     for i in range(_GUARD_ANCHORS))
_TOO_FEW = "".join(f"'QuadraticOrderRootTable.anchor_{i}' depends on axioms: {_STD}\n"
                   for i in range(_GUARD_ANCHORS - 1))


def _ci_axiom_step_run() -> str:
    yaml = pytest.importorskip("yaml")
    wf = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "telperion-lean-e2e.yml"
    job = yaml.safe_load(wf.read_text())["jobs"]["quadratic-order-root-table-compiles"]
    steps = [s for s in job["steps"]
             if "AxiomGuardQuadraticOrderRootTable" in str(s.get("run", ""))]
    assert len(steps) == 1
    assert "allow-list" in steps[0]["name"] and "sorryAx" not in steps[0]["name"]
    return steps[0]["run"]


def _run_ci_axiom_step(tmp_path, fixture: str) -> int:
    """EXECUTE the CI step's run block with the `lake env lean` line replaced by the fixture."""
    import shutil
    import subprocess
    run = _ci_axiom_step_run()
    lines = run.splitlines()
    idx = [i for i, l in enumerate(lines) if l.strip().startswith("lake env lean")]
    assert len(idx) == 1, lines
    lines[idx[0]] = 'cp "$FIXTURE" axioms.out'
    (tmp_path / "fixture.out").write_text(fixture, encoding="utf-8")
    (tmp_path / "step.sh").write_text("\n".join(lines) + "\n", encoding="utf-8")
    bash = shutil.which("bash")
    assert bash
    r = subprocess.run([bash, "step.sh"], cwd=tmp_path, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin", "FIXTURE": str(tmp_path / "fixture.out")})
    return r.returncode


@pytest.mark.parametrize("label,fixture,accept", [
    ("real guard output", _real_guard_output(), True),
    ("bb RealWrap: wrapped native_decide aux axiom", _padded(_REALWRAP), False),
    ("wrapped sorryAx", _padded(_WRAPPED_SORRY), False),
    ("look-alike Classical_choice", _padded(_LOOKALIKE), False),
    ("no axioms at all", _NO_AXIOMS, True),
    ("one anchor missing", _TOO_FEW, False),
])
def test_ci_axiom_step_executed_against_fixtures(tmp_path, label, fixture, accept):
    """REVIEW_PR766 C1 + Add.1: the CI axiom guard is an ALLOW-LIST that parses whole (possibly
    line-wrapped) axiom lists and matches fixed strings.  The step's run block is executed, not
    inspected: a deny-list of sorryAx / ofReduceBool, a line-based parser, or an -E pattern would
    each accept one of the rejected fixtures."""
    code = _run_ci_axiom_step(tmp_path, fixture)
    assert (code == 0) == accept, (label, code)


def test_axiom_guard_file_has_exactly_the_pinned_anchor_count():
    guard = _EX / "lean" / "AxiomGuardQuadraticOrderRootTable.lean"
    n = sum(1 for l in guard.read_text(encoding="utf-8").splitlines()
            if l.startswith("#print axioms"))
    assert n == _GUARD_ANCHORS


# --- 4. the independent re-check --------------------------------------------------------

def test_verify_rejects_every_forgery():
    cert = quadratic_order_root_table_certificate(0, 5, [2, 3, 7])
    assert verify_certificate(cert)
    ram, split3, split7 = cert.faces
    bad = [
        replace(cert, faces=(ram, replace(split3, y=0), split7)),          # wrong root
        replace(cert, faces=(ram, replace(split3, y=4), split7)),          # root out of range
        replace(cert, faces=(ram, replace(split3, witness=False), split7)),  # witness flag off
        replace(cert, faces=(ram, split3, replace(split7, witness=True))),   # 28 > 20
        replace(cert, faces=(replace(ram, face=SPLIT, y=0), split3, split7)),  # 2 | d: not split
        replace(cert, faces=(ram, replace(split3, face=INERT, y=None, witness=False), split7)),
        replace(cert, faces=(ram, split3, split7, PrimeFace(9, INERT))),   # composite
        replace(cert, faces=(ram, split3, split3)),                        # repeated
        replace(cert, t=2),
        replace(cert, c=0),
    ]
    for b in bad:
        assert not verify_certificate(b), b


# --- 5. emission --------------------------------------------------------------------

def _emit_text(specs, names=None):
    names = names or [f"q{i}" for i in range(len(specs))]
    fam = quadratic_order_root_table_family(
        "QuadraticOrderRootTableTest", GridSpec([("i", list(range(len(specs))))]),
        lambda pt: names[pt["i"]], spec=lambda pt: dict(specs[pt["i"]]))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("QuadraticOrderRootTableTest",),
                    imports=("Mathlib", "QuadraticOrderRoot")),
        [QuadraticOrderRootTableEmitter()],
        ValidationReport(checks=(("quadratic_order_root_table", True),)),
    )
    return next(iter(report.files.values()))


def test_kind_and_emitter_for():
    fam = quadratic_order_root_table_family("T", GridSpec([("i", [0])]), lambda pt: "t",
                                            spec=lambda pt: dict(t=0, c=5, primes=[3]))
    assert fam.kind == "quadratic_order_root_table"
    assert emitter_for("quadratic_order_root_table").kind == "quadratic_order_root_table"


def test_emit_shape_is_deterministic_and_lint_clean():
    spec = dict(t=0, c=5, primes=[2, 3, 7])
    txt = _emit_text([spec], ["d20"])
    assert txt == _emit_text([spec], ["d20"]), "emission is not byte-deterministic"
    errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
    assert errs == [], errs
    for banned in ("sorry", "admit", "native_decide", "axiom ", "maxHeartbeats"):
        assert banned not in txt, banned
    assert "theorem d20_ram_2 : 2 ∣ 4 * 5 - 0 ^ 2 := by decide" in txt
    assert "theorem d20_root_3 : IsRootMod 0 5 3 1 := by decide" in txt
    assert "theorem d20_root_7 : IsRootMod 0 5 7 3 := by decide" in txt
    assert "D.ramified_of_dvd 2 (by norm_num) (by decide) d20_ram_2" in txt
    assert "D.split_of_isRootMod 3 (by norm_num) (by decide) d20_root_3" in txt
    assert "theorem d20_w_3 : IsWitness 0 5 3 1 :=" in txt
    assert "d20_w_7" not in txt                                   # 28 > 20
    assert "theorem d20_classNumber_ne_one" in txt and "classNumber K ≠ 1" in txt
    assert "classNumber_ne_one_of_isWitness D (by decide) d20_w_3" in txt
    assert "theorem d20 : (2 ∣ 4 * 5 - 0 ^ 2) ∧ (IsRootMod 0 5 3 1) ∧ (IsRootMod 0 5 7 3) :=" in txt
    assert "example : (2 ∣ 4 * 5 - 0 ^ 2) ∧ (IsRootMod 0 5 3 1) ∧ (IsRootMod 0 5 7 3) := d20" in txt
    assert "conjecture1_proved = False" in txt
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_emit_inert_face_and_no_class_number_theorem_without_witness():
    txt = _emit_text([dict(t=0, c=2, primes=[2, 3, 5])], ["d8"])
    assert ("theorem d8_noroot_5 : ∀ z : ZMod 5, z ^ 2 - (0 : ZMod 5) * z + (2 : ZMod 5) ≠ 0 "
            ":= by decide") in txt
    assert "D.inert_of_no_root 5 (by norm_num) d8_noroot_5" in txt
    assert "P.inertiaDeg ℤ = 2" in txt
    assert "classNumber" not in txt and "IsWitness" not in txt


def test_emit_single_face_capstone_is_the_face_itself():
    txt = _emit_text([dict(t=0, c=5, primes=[3])], ["one"])
    assert "theorem one : (IsRootMod 0 5 3 1) :=\n  one_root_3\n" in txt


def test_emit_body_refuses_a_forged_payload():
    """emit_body re-checks the certificate (Layer 1 at emission); the adapter bypasses this
    deliberately by rendering directly."""
    from telperion.negative_control_harness import emit_via_single_instance_family
    cert = quadratic_order_root_table_certificate(0, 5, [3])
    forged = replace(cert, faces=(PrimeFace(3, SPLIT, 0, True),))
    with pytest.raises(ValueError, match="REFUSED"):
        emit_via_single_instance_family(QuadraticOrderRootTableEmitter(), lean_name="x",
                                        instance_kwargs={"payload": forged})


def test_prelude_is_attributed_and_clean():
    pre = quadratic_order_root_prelude_lean()
    assert pre.startswith("/-")
    assert "tenth-discriminant" in pre and "import Mathlib" in pre
    for banned in ("sorry", "native_decide", "admit", "maxHeartbeats"):
        assert banned not in pre
    for thm in ("structure QuadInt", "def IsRootMod", "def IsWitness",
                "theorem exists_eq_add_mul", "theorem split_of_isRootMod",
                "theorem inert_of_no_root", "theorem ramified_of_dvd",
                "theorem not_absNorm_eq_of_no_root", "theorem classNumber_ne_one_of_witness",
                "theorem classNumber_ne_one_of_isWitness", "theorem not_form_eq_prime"):
        assert thm in pre, thm
    assert "conjecture1_proved = False" in pre
    for ch in pre:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the prelude"


def test_example_prelude_file_matches_the_generator():
    """The island's QuadraticOrderRoot.lean is written from the SAME string (drift check)."""
    p = _EX / "lean" / "QuadraticOrderRoot.lean"
    assert p.read_text(encoding="utf-8") == quadratic_order_root_prelude_lean()


# --- 6. registry and negative-control wiring ------------------------------------------

def test_emitter_is_classified_certificate_sensitive_with_adapter():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY)
    from telperion.negative_control_harness import registered_adapters
    stance = REGISTRY["QuadraticOrderRootTableEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE
    assert stance.reason.strip()
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "QuadraticOrderRootTableEmitter" in registered_adapters()


def test_adapter_twins_differ_only_in_the_forged_root():
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["QuadraticOrderRootTableEmitter"]
    f, t = ad.make_false_cert(), ad.make_true_cert()
    assert verify_certificate(t) and not verify_certificate(f)
    assert t.faces[0].y == 1 and f.faces[0].y == 0
    ft, tt = ad.emit_call(f, "twin"), ad.emit_call(t, "twin")
    diff = [(a, b) for a, b in zip(ft.splitlines(), tt.splitlines()) if a != b]
    assert diff, "the twins must differ"
    for a, b in diff:
        assert a.replace("3 0", "3 1").replace("y = 0", "y = 1") == b, (a, b)   # only y differs


# --- 7. Lean end to end (gated on a built env) ----------------------------------------

_ENV = _EX / "lean"


def _env_ready():
    from lean_env import lean_env_ready
    olean = _ENV / ".lake" / "build" / "lib" / "lean" / "QuadraticOrderRoot.olean"
    return lean_env_ready(_ENV) and olean.is_file()


lean = pytest.mark.skipif(not _env_ready(),
                          reason="quadratic_order_root_table Lean env not built -- skipped")


@lean
def test_lean_end_to_end_axiom_clean():
    from telperion.verify import verify_lean
    txt = _emit_text([dict(t=0, c=5, primes=[2, 3, 7]), dict(t=1, c=41, primes=[2, 7, 41, 163])],
                     ["e20", "e163"])
    decls = ["QuadraticOrderRootTableTest.e20", "QuadraticOrderRootTableTest.e20_classNumber_ne_one",
             "QuadraticOrderRootTableTest.e20_root_3_kd", "QuadraticOrderRootTableTest.e163",
             "QuadraticOrderRootTableTest.e163_noroot_7_kd",
             "QuadraticOrderRootTableTest.e163_ram_163_kd"]
    r = verify_lean(txt, env_dir=_ENV, decls=decls)
    assert r.okay and r.axioms_clean, (r.summary(), r.errors[:3])
    for d in decls:
        assert set(r.axioms[d]) <= {"propext", "Classical.choice", "Quot.sound"}, (d, r.axioms[d])


@lean
def test_lean_negative_control_forged_root():
    from telperion.negative_control_harness import (
        generic_negative_control, registered_adapters)
    res = generic_negative_control(registered_adapters()["QuadraticOrderRootTableEmitter"],
                                   env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail


@lean
def test_lean_rejects_a_forged_witness_at_p_eq_c():
    """The structural control at the kernel: `IsWitness 0 2 2 0` cannot be proved (`2 ≠ 2`), and
    `IsRootMod 0 2 2 0` CAN -- the root exists, it is the ramified double root."""
    from telperion.negative_control import assert_kernel_rejects
    from telperion.verify import verify_lean
    head = "import Mathlib\nimport QuadraticOrderRoot\nopen QuadraticOrderRoot\n"
    bad = head + ("theorem forged_w : IsWitness 0 2 2 0 :=\n"
                  "  ⟨by norm_num, by decide, by decide, by decide, by decide⟩\n")
    assert assert_kernel_rejects(bad, "forged_w", env_dir=_ENV)
    good = head + "theorem root_two : IsRootMod 0 2 2 0 := by decide\n"
    r = verify_lean(good, env_dir=_ENV, decls=["root_two"])
    assert r.okay and r.axioms_clean, (r.summary(), r.errors[:2])
