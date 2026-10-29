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

The example, CI-gate and Lean-gated checks live in test_emit_quadratic_order_root_table_lab.py, which stays in Arda.

conjecture1_proved = False.
"""
import sys
from dataclasses import replace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, certify  # noqa: E402
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
from _helpers.emit_quadratic_order_root_table import _emit_text  # noqa: E402


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


def test_certify_propagates_the_refusal():
    fam = quadratic_order_root_table_family(
        "Bad", GridSpec([("i", [0])]), lambda pt: "bad",
        spec=lambda pt: dict(t=0, c=5, primes=[9]))
    with pytest.raises(Exception, match="REFUSED"):
        certify(fam)


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
