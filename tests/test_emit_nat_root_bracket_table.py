"""nat_root_bracket_table emitter -- kernel-decided q-th-root brackets of m^(+-p/q), singly and
as blocked List ℕ range-sum tables (CN-1 emitter survey phase 2, item N1).

These tests pin, in order: the exact integer arithmetic (Newton q-th root against brute force,
the bracket invariants the kernel will decide, the one-ulp width); the certify-time refusals
(forged endpoints, bad inputs, floats, the block cap); the emitted text (shape, determinism,
lint, the statement gate, the exact CN-1 ZetaTables numbers for the shared block); the
sensitivity-registry classification and the negative-control adapter; the example's
byte-stability; and, Lean-gated, an end-to-end kernel check of the four example instances plus
the two-sided negative control and the single-face `U := L` forgery.

conjecture1_proved = False.
"""
import subprocess
import sys
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_nat_root_bracket_table import (  # noqa: E402
    DEFAULT_BLOCK,
    MAX_BLOCK,
    NatRootBracketCert,
    NatRootBracketTableCert,
    NatRootBracketTableEmitter,
    nat_iroot,
    nat_root_bracket,
    nat_root_bracket_certificate,
    nat_root_bracket_prelude_body,
    nat_root_bracket_prelude_lean,
    nat_root_bracket_table_certificate,
    nat_root_bracket_table_family,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_EXAMPLE = _ROOT / "examples" / "nat_root_bracket_table"
_ENV = _EXAMPLE / "lean"


# --- 1. exact integer arithmetic -------------------------------------------------

@pytest.mark.parametrize("q", [1, 2, 3, 4, 5, 8])
def test_nat_iroot_matches_brute_force_small(q):
    for x in range(0, 700):
        r = nat_iroot(x, q)
        assert r ** q <= x < (r + 1) ** q, (x, q, r)


@pytest.mark.parametrize("q", [2, 3, 4, 7, 8])
def test_nat_iroot_large_exact_powers_and_neighbours(q):
    for base in (10 ** 12 + 7, 3 ** 40, 2 ** 200 + 12345):
        x = base ** q
        assert nat_iroot(x, q) == base
        assert nat_iroot(x - 1, q) == base - 1
        assert nat_iroot(x + 1, q) == base


def test_nat_iroot_is_newton_not_a_decrement_loop_on_a_1e12_scale_root():
    """The CN-1 generator note: a decrement loop from a float start hung for over two minutes on a
    10^12-scale root; Newton returns at once (the gate is a generous wall-clock bound)."""
    import time
    t0 = time.time()
    x = 1001 * (10 ** 12) ** 4
    r = nat_iroot(x, 4)
    assert r ** 4 <= x < (r + 1) ** 4
    assert time.time() - t0 < 2.0


def test_nat_iroot_refuses_bad_inputs():
    with pytest.raises(ValueError):
        nat_iroot(-1, 2)
    with pytest.raises(ValueError):
        nat_iroot(5, 0)


@pytest.mark.parametrize("m,p,q", [(2, 1, 2), (1001, 3, 4), (1001, 7, 8), (7, 5, 3), (1, 3, 4)])
def test_neg_bracket_facts_and_one_ulp(m, p, q):
    S = 10 ** 10
    lo, hi = nat_root_bracket(m, 1, p, q, S, -1)
    # the two facts the kernel decides
    assert lo ** q * m ** p <= S ** q <= hi ** q * m ** p
    # tightness: lo is the largest valid natural, hi the smallest
    assert (lo + 1) ** q * m ** p > S ** q
    assert hi == lo or (hi - 1) ** q * m ** p < S ** q
    assert hi - lo <= 1
    # encloses the true value as a rational statement: (lo/S)^q <= m^-p <= (hi/S)^q
    assert Fraction(lo, S) ** q <= Fraction(1, m ** p) <= Fraction(hi, S) ** q


@pytest.mark.parametrize("m,p,q", [(1001, 1, 4), (8000, 7, 8), (2, 1, 2), (16, 1, 4)])
def test_pos_bracket_facts(m, p, q):
    S = 10 ** 12
    lo, hi = nat_root_bracket(m, 1, p, q, S, +1)
    assert lo ** q <= m ** p * S ** q <= hi ** q
    assert hi - lo <= 1
    if (m ** p * S ** q) == lo ** q:      # an exact root (16^(1/4) = 2) collapses to one point
        assert hi == lo


def test_rat_base_brackets_match_the_cn1_gamma_ratio_factors():
    """GammaRatio.lean g_hA: 3635432077/10^12 <= (64003/8)^(-5/8); g_hD: 325168010868/10^12 <=
    (64007/8)^(-1/8) (the CN-1 hand-built lower endpoints)."""
    lo, hi = nat_root_bracket(64003, 8, 5, 8, 10 ** 12, -1)
    assert lo == 3635432077 and hi == lo + 1
    assert lo ** 8 * 64003 ** 5 <= 8 ** 5 * (10 ** 12) ** 8 <= hi ** 8 * 64003 ** 5
    lo, hi = nat_root_bracket(64007, 8, 1, 8, 10 ** 12, -1)
    assert lo == 325168010868
    # positive rational base: (a/b)^(p/q) = (b/a)^(-p/q), the two routes agree
    lo1, hi1 = nat_root_bracket(3, 2, 1, 2, 10 ** 6, +1)
    lo2, hi2 = nat_root_bracket(2, 3, 1, 2, 10 ** 6, -1)
    assert (lo1, hi1) == (lo2, hi2) == (1224744, 1224745)   # sqrt(3/2) = 1.2247448...


def test_single_brackets_match_the_cn1_zeta_values_file():
    """ZetaValues.lean n1001_* (scale 10^12): 1001^(1/4) in [5624818578328, 5624818578329],
    1001^(-3/4) in [5619199378, 5619199379], 1001^(-7/8) in [2369300697, 2369300698]."""
    assert nat_root_bracket(1001, 1, 1, 4, 10 ** 12, +1) == (5624818578328, 5624818578329)
    assert nat_root_bracket(1001, 1, 3, 4, 10 ** 12, -1) == (5619199378, 5619199379)
    assert nat_root_bracket(1001, 1, 7, 8, 10 ** 12, -1) == (2369300697, 2369300698)


# --- 2. certificates and refusals --------------------------------------------------

def test_single_certificate_defaults_to_the_tightest_bracket():
    c = nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6)
    assert isinstance(c, NatRootBracketCert)
    assert (c.num, c.den, c.p, c.q, c.sign, c.scale) == (2, 1, 1, 2, -1, 10 ** 6)
    assert (c.lo, c.hi) == (707106, 707107)      # 2^(-1/2) = 0.70710678...
    assert c.face == "single"


def test_single_certificate_accepts_rational_bases_in_three_spellings():
    a = nat_root_bracket_certificate((64003, 8), 5, 8, scale=10 ** 12)
    b = nat_root_bracket_certificate(Fraction(64003, 8), 5, 8, scale=10 ** 12)
    c = nat_root_bracket_certificate(sp.Rational(64003, 8), 5, 8, scale=10 ** 12)
    assert a == b == c and a.den == 8
    # a reducible pair is put in lowest terms (the lemma hypotheses use the reduced a, b)
    d = nat_root_bracket_certificate((6, 4), 1, 2, scale=10 ** 6)
    assert (d.num, d.den) == (3, 2)


def test_single_certificate_accepts_a_looser_supplied_endpoint_and_refuses_a_tighter_one():
    tight = nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6)
    loose = nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6, lo=tight.lo - 5, hi=tight.hi + 5)
    assert (loose.lo, loose.hi) == (tight.lo - 5, tight.hi + 5)
    with pytest.raises(ValueError, match="claimed lo"):
        nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6, lo=tight.lo + 1)
    with pytest.raises(ValueError, match="claimed hi"):
        nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6, hi=tight.hi - 1)
    # the forge of the negative control: U := L on a non-exact bracket
    with pytest.raises(ValueError, match="claimed hi"):
        nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6, hi=tight.lo)


@pytest.mark.parametrize("kwargs", [
    dict(base=0, p=1, q=2),
    dict(base=-3, p=1, q=2),
    dict(base=(3, 0), p=1, q=2),
    dict(base=2, p=0, q=2),
    dict(base=2, p=1, q=0),
    dict(base=2, p=1, q=2, scale=0),
    dict(base=2, p=1, q=2, sign=0),
    dict(base=2, p=1, q=2, sign=True),
    dict(base=2.0, p=1, q=2),
    dict(base=2, p=1.5, q=2),
    dict(base=sp.Float(2.0), p=1, q=2),
    dict(base=Fraction(1, 2), p=1, q=2, scale=Fraction(3, 2)),
    dict(base=sp.sqrt(2), p=1, q=2),
    dict(base=2, p=1, q=2, lo=-1),
])
def test_single_certificate_refusals(kwargs):
    with pytest.raises(ValueError, match="REFUSED"):
        nat_root_bracket_certificate(kwargs.pop("base"), kwargs.pop("p"), kwargs.pop("q"), **kwargs)


def test_table_certificate_reproduces_the_cn1_zeta_tables_block_sums():
    """ZetaTables.lean zlo34_0_sum / zhi34_0_sum = 116105226077 / 116105226275 and zlo34_1_sum /
    zhi34_1_sum = 28423242284 / 28423242483 (the generated CN-1 file, sigma = 3/4, K = 200,
    S = 10^10); the first two blocks of a 400-term table are the same numbers."""
    c = nat_root_bracket_table_certificate(3, 4, 400, scale=10 ** 10, block=200)
    assert isinstance(c, NatRootBracketTableCert)
    assert c.face == "table" and c.n_blocks == 2 and c.terms == 400
    assert c.lo_sums == (116105226077, 28423242284)
    assert c.hi_sums == (116105226275, 28423242483)
    assert c.lo_total == sum(c.lo_sums) and c.hi_total == sum(c.hi_sums)
    assert c.lo_blocks[0][0] == 10 ** 10 == c.hi_blocks[0][0]     # 1^(-3/4) = 1 exactly
    assert c.lo_blocks[0][15] == 1250000000 == c.hi_blocks[0][15]  # 16^(-3/4) = 1/8 exactly
    for cb in range(c.n_blocks):
        for n in range(c.block):
            m = c.block * cb + n + 1
            lo, hi = c.lo_blocks[cb][n], c.hi_blocks[cb][n]
            assert lo ** 4 * m ** 3 <= (10 ** 10) ** 4 <= hi ** 4 * m ** 3
            assert hi - lo <= 1


def test_table_certificate_total_encloses_the_true_partial_sum():
    import mpmath
    mpmath.mp.dps = 50
    c = nat_root_bracket_table_certificate(7, 8, 40, scale=10 ** 10, block=20)
    true = mpmath.fsum(mpmath.mpf(i + 1) ** (-mpmath.mpf(7) / 8) for i in range(40))
    assert mpmath.mpf(c.lo_total) / c.scale <= true <= mpmath.mpf(c.hi_total) / c.scale
    assert c.hi_total - c.lo_total <= 40


@pytest.mark.parametrize("args,kwargs,msg", [
    ((0, 4, 400), {}, "exponent numerator"),
    ((3, 0, 400), {}, "root index"),
    ((3, 4, 0), {}, "number of terms"),
    ((3, 4, 400), dict(scale=0), "scale"),
    ((3, 4, 400), dict(block=0), "block size"),
    ((3, 4, 300), dict(block=200), "not a multiple"),
    ((3, 4, 2 * (MAX_BLOCK + 1)), dict(block=MAX_BLOCK + 1), "MAX_BLOCK"),
    ((3, 4, 65 * 10), dict(block=10), "MAX_BLOCKS"),
    ((3.0, 4, 400), {}, "float"),
    ((3, 4, 400), dict(scale=1e10), "float"),
])
def test_table_certificate_refusals(args, kwargs, msg):
    with pytest.raises(ValueError, match=msg):
        nat_root_bracket_table_certificate(*args, **kwargs)


def test_default_block_is_200_and_within_the_measured_cap():
    assert DEFAULT_BLOCK == 200 <= MAX_BLOCK


def test_certify_dispatches_both_faces_and_propagates_the_refusal():
    fam = nat_root_bracket_table_family(
        "T", GridSpec([("case", [0, 1])]), lambda pt: ["tbl", "sgl"][pt["case"]],
        spec=lambda pt: [dict(p=3, q=4, terms=40, scale=10 ** 10, block=20),
                         dict(base=2, p=1, q=2, scale=10 ** 6)][pt["case"]])
    cf = certify(fam)
    assert cf.family.kind == "nat_root_bracket_table"
    assert isinstance(cf.instances[0].payload, NatRootBracketTableCert)
    assert isinstance(cf.instances[1].payload, NatRootBracketCert)
    assert cf.checks_passed == 4 * 2 + 2
    bad = nat_root_bracket_table_family(
        "B", GridSpec([("case", [0])]), lambda pt: "b",
        spec=lambda pt: dict(base=2, p=1, q=2, scale=10 ** 6, hi=707106))
    with pytest.raises(Exception, match="claimed hi"):
        certify(bad)


def test_kind_and_emitter_for():
    em = emitter_for("nat_root_bracket_table")
    assert isinstance(em, NatRootBracketTableEmitter)
    assert em.kind == "nat_root_bracket_table"
    assert "NatRootBracket.sum_block_lo_neg" in em.requires_prelude


# --- 3. emitted text --------------------------------------------------------------

def _emit_text(specs, names, imports=("NatRootBracket",)):
    fam = nat_root_bracket_table_family(
        "NatRootBracketTableTest", GridSpec([("case", list(range(len(specs))))]),
        lambda pt: names[pt["case"]], spec=lambda pt: dict(specs[pt["case"]]))
    report = emit(certify(fam), LeanProfile(namespace=("NatRootBracketTableTest",), imports=imports),
                  [NatRootBracketTableEmitter()], ValidationReport(checks=(("ok", True),)))
    return next(iter(report.files.values()))


_TBL = dict(p=3, q=4, terms=40, scale=10 ** 10, block=20)
_SGL_NEG = dict(base=2, p=1, q=2, scale=10 ** 6)
_SGL_POS = dict(base=1001, p=1, q=4, scale=10 ** 12, sign=+1)
_SGL_RAT = dict(base=(64003, 8), p=5, q=8, scale=10 ** 12)
_SGL_RAT_POS = dict(base=(3, 2), p=1, q=2, scale=10 ** 6, sign=+1)


def test_emit_table_shape_is_deterministic_and_lint_clean():
    t1 = _emit_text([_TBL], ["tbl"])
    t2 = _emit_text([_TBL], ["tbl"])
    assert t1 == t2
    assert lint_lean_text(t1) == []
    assert "open NatRootBracket" in t1
    for c in range(2):
        assert f"def tbl_lo_{c} : List ℕ := [" in t1 and f"def tbl_hi_{c} : List ℕ := [" in t1
        assert (f"theorem tbl_lo_{c}_fact : ∀ n < 20, (tbl_lo_{c}.getD n 0) ^ 4 * (20 * {c} + n + 1) ^ 3 "
                f"≤ 10000000000 ^ 4 := by\n  decide +kernel") in t1
        assert (f"theorem tbl_hi_{c}_fact : ∀ n < 20, 10000000000 ^ 4 ≤ (tbl_hi_{c}.getD n 0) ^ 4 * "
                f"(20 * {c} + n + 1) ^ 3 := by\n  decide +kernel") in t1
        assert f"theorem tbl_lo_{c}_sum : ∑ n ∈ Finset.range 20, tbl_lo_{c}.getD n 0 = " in t1
        assert f"sum_block_lo_neg f (-((3 : ℝ) / 4)) 3 4 10000000000 20 (20 * {c})" in t1
    assert "rw [show (40 : ℕ) = 2 * 20 from rfl, sum_range_chunk f 2 20]" in t1
    assert "theorem tbl : (" in t1 and "∑ i ∈ Finset.range 40, ((i : ℝ) + 1) ^ (-((3 : ℝ) / 4))" in t1
    assert ":= ⟨tbl_lo, tbl_hi⟩" in t1
    # the statement gate re-states the final theorem's exact type
    assert t1.count("example : (") == 1
    assert "sorry" not in t1 and "native_decide" not in t1 and "maxRecDepth" not in t1


def test_emit_single_faces_use_the_matching_prelude_lemma():
    t = _emit_text([_SGL_NEG, _SGL_POS, _SGL_RAT, _SGL_RAT_POS], ["neg", "pos", "rat", "ratpos"])
    assert lint_lean_text(t) == []
    assert "theorem neg_lo_fact : 707106 ^ 2 * 2 ^ 1 ≤ 1000000 ^ 2 := by decide +kernel" in t
    assert "theorem neg_hi_fact : 1000000 ^ 2 ≤ 707107 ^ 2 * 2 ^ 1 := by decide +kernel" in t
    assert ("theorem neg : (707106 : ℝ) / 1000000 ≤ (2 : ℝ) ^ (-((1 : ℝ) / 2)) ∧ "
            "(2 : ℝ) ^ (-((1 : ℝ) / 2)) ≤ (707107 : ℝ) / 1000000 := by") in t
    assert "rpow_neg_div_lower 2 1 2 707106 1000000 (by norm_num) (by norm_num) (by norm_num) neg_lo_fact" in t
    assert "theorem pos_lo_fact : 5624818578328 ^ 4 ≤ 1001 ^ 1 * 1000000000000 ^ 4 := by decide +kernel" in t
    assert "rpow_div_upper 1001 1 4 5624818578329 1000000000000 (by norm_num) (by norm_num) pos_hi_fact" in t
    assert "(1001 : ℝ) ^ ((1 : ℝ) / 4)" in t
    assert "theorem rat_lo_fact : 3635432077 ^ 8 * 64003 ^ 5 ≤ 8 ^ 5 * 1000000000000 ^ 8 := by decide +kernel" in t
    assert "rpow_rat_neg_div_lower 64003 8 5 8 3635432077 1000000000000 (by norm_num) (by norm_num) (by norm_num) (by norm_num) rat_lo_fact" in t
    assert "((64003 : ℝ) / 8) ^ (-((5 : ℝ) / 8))" in t
    assert "theorem ratpos_lo_fact : 1224744 ^ 2 * 2 ^ 1 ≤ 3 ^ 1 * 1000000 ^ 2 := by decide +kernel" in t
    assert "rpow_rat_div_lower 3 2 1 2 1224744 1000000" in t
    assert t.count("example : (") == 4


def test_emit_refuses_a_profile_without_the_prelude():
    from telperion.workflow import WorkflowError
    with pytest.raises(WorkflowError, match="prelude"):
        _emit_text([_SGL_NEG], ["neg"], imports=("Mathlib",))


def test_prelude_is_attributed_mathlib_only_and_clean():
    p = nat_root_bracket_prelude_lean()
    assert p.startswith("/-\nNatRootBracket")
    assert "import Mathlib\n" in p and p.count("import ") == 1     # Mathlib only
    assert "RpowBounds.lean" in p and "GammaRatio.lean" in p          # provenance
    assert "namespace NatRootBracket" in p and p.rstrip().endswith("end NatRootBracket")
    for lem in ("rpow_div_lower", "rpow_div_upper", "rpow_neg_div_lower", "rpow_neg_div_upper",
                "rpow_rat_div_lower", "rpow_rat_div_upper", "rpow_rat_neg_div_lower",
                "rpow_rat_neg_div_upper", "sum_range_chunk", "sum_block_lo_neg", "sum_block_hi_neg"):
        assert f"lemma {lem} " in p, lem
    assert "sorry" not in p and "axiom " not in p and "native_decide" not in p
    body = nat_root_bracket_prelude_body()
    assert "import" not in body and body.lstrip().startswith("/-")


# --- 4. the example is byte-stable ----------------------------------------------------

def test_example_files_match_the_generator():
    assert (_ENV / "NatRootBracket.lean").read_text(encoding="utf-8") == nat_root_bracket_prelude_lean()
    r = subprocess.run([sys.executable, str(_EXAMPLE / "generate.py"), "--check"],
                       capture_output=True, text=True, cwd=str(_ROOT))
    assert r.returncode == 0, r.stdout + r.stderr
    assert (_ENV / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.0"


def test_example_shares_the_cn1_zeta_tables_block_numbers():
    """The example's first sigma = 3/4 block is byte-for-byte the CN-1 ZetaTables zlo34_0 / zhi34_0
    sums (independent generator, same numbers)."""
    t = (_ENV / "NatRootBracketTable.lean").read_text(encoding="utf-8")
    assert "sum_neg34_400_lo_0.getD n 0 = 116105226077" in t
    assert "sum_neg34_400_hi_0.getD n 0 = 116105226275" in t
    assert "theorem pow_1001_pos14_lo_fact : 5624818578328 ^ 4 ≤ 1001 ^ 1 * 1000000000000 ^ 4" in t
    assert "theorem rat_64003_8_neg58_lo_fact : 3635432077 ^ 8 * 64003 ^ 5 ≤ 8 ^ 5 * 1000000000000 ^ 8" in t


# --- 5. registry and negative-control wiring -------------------------------------------

def test_emitter_is_classified_certificate_sensitive_with_adapter():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY)
    from telperion.negative_control_harness import registered_adapters
    stance = REGISTRY["NatRootBracketTableEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE
    assert stance.reason.strip()
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "NatRootBracketTableEmitter" in registered_adapters()


def test_adapter_twins_differ_by_one_entry_only():
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["NatRootBracketTableEmitter"]
    f, t = ad.make_false_cert(), ad.make_true_cert()
    diffs = [(c, n) for c in range(t.n_blocks) for n in range(t.block)
             if f.lo_blocks[c][n] != t.lo_blocks[c][n]]
    assert diffs == [(1, 7)]
    c, n = diffs[0]
    m = t.block * c + n + 1
    # the forged entry violates exactly the fact the kernel decides; the honest one satisfies it
    assert t.lo_blocks[c][n] ** 4 * m ** 3 <= (10 ** 10) ** 4 < f.lo_blocks[c][n] ** 4 * m ** 3
    assert f.hi_blocks == t.hi_blocks
    ft, tt = ad.emit_call(f, "twin"), ad.emit_call(t, "twin")
    diff = [(a, b) for a, b in zip(ft.splitlines(), tt.splitlines()) if a != b]
    # the list, its block sum, the two one-sided theorem statements, the conjunction and its gate
    assert 3 <= len(diff) <= 6, diff
    assert diff[0][0].startswith("def twin_lo_1 : List ℕ := [")
    # the forged CLAIM stays TRUE (the forged lower total is still below the true sum), so the
    # kernel's rejection is of a corrupted WITNESS under a true claim (REVIEW_PR765 question 3)
    import mpmath
    mpmath.mp.dps = 50
    true = mpmath.fsum(mpmath.mpf(i + 1) ** (-mpmath.mpf(3) / 4) for i in range(40))
    assert mpmath.mpf(f.lo_total) / f.scale < true < mpmath.mpf(f.hi_total) / f.scale
    assert f.lo_total == t.lo_total + 1 == 66495196525


_WF = _ROOT.parent / ".github" / "workflows" / "telperion-lean-e2e.yml"
_FIX = Path(__file__).resolve().parent / "fixtures" / "nat_root_bracket_table"


def _run_ci_axiom_check(tmp_path, axioms_text: str) -> int:
    """EXECUTE the CI axiom step's run block (everything but the `lake env lean | tee` line) in a
    directory holding the given `axioms.out`, under `bash -e` like a GitHub `run:` block."""
    yaml = pytest.importorskip("yaml")
    job = yaml.safe_load(_WF.read_text())["jobs"]["nat-root-bracket-table-compiles"]
    step = [s for s in job["steps"] if s.get("name", "").startswith("Axiom guard")][0]
    lines = [ln for ln in step["run"].splitlines() if "lake env lean" not in ln]
    (tmp_path / "axioms.out").write_text(axioms_text, encoding="utf-8")
    return subprocess.run(["bash", "-e", "-c", "\n".join(lines)], cwd=str(tmp_path),
                          capture_output=True, text=True).returncode


def _real_guard() -> str:
    return (_FIX / "guard_real.txt").read_text(encoding="utf-8")


def test_ci_axiom_guard_accepts_the_real_guard_output(tmp_path):
    real = _real_guard()
    assert real.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 10
    assert _run_ci_axiom_check(tmp_path, real) == 0
    # the guard file names exactly the ten anchors the step pins
    guard = (_ENV / "AxiomGuardNatRootBracketTable.lean").read_text(encoding="utf-8")
    assert guard.count("#print axioms ") == 10


def test_ci_axiom_guard_accepts_ten_axiom_free_declarations(tmp_path):
    noax = "".join(f"'NatRootBracket.l{i}' does not depend on any axioms\n" for i in range(10))
    assert _run_ci_axiom_check(tmp_path, noax) == 0


def test_ci_axiom_guard_rejects_real_wrapped_native_decide_output(tmp_path):
    """REVIEW_PR766 Add.1: real v4.32.0 output wraps the list one axiom per line, so a first-line
    check reads `[propext,` and accepts the `<thm>._native.native_decide.ax_1_1` axiom."""
    wrapped = (_FIX / "realwrap_native_decide.txt").read_text(encoding="utf-8")
    assert "\n Classical.choice,\n" in wrapped                 # it really is wrapped
    assert "._native.native_decide.ax_1_1]" in wrapped
    # eight clean anchors + the two real lines = ten anchors, so only the axiom check can reject it
    real8 = "".join(_real_guard().splitlines(True)[:8])
    assert _run_ci_axiom_check(tmp_path, real8 + wrapped) != 0


def test_ci_axiom_guard_rejects_wrapped_sorry_and_look_alike(tmp_path):
    real9 = "".join(_real_guard().splitlines(True)[:9])
    sorry_wrapped = ("'NatRootBracketTable.z' depends on axioms: [propext,\n sorryAx,\n Classical.choice,\n"
                     " Quot.sound]\n")
    assert _run_ci_axiom_check(tmp_path, real9 + sorry_wrapped) != 0
    look_alike = "'NatRootBracketTable.w' depends on axioms: [propext, ClassicalXchoice, Quot.sound]\n"
    assert _run_ci_axiom_check(tmp_path, real9 + look_alike) != 0
    extra = "'NatRootBracketTable.v' depends on axioms: [propext, Classical.choice, Quot.sound, myAxiom]\n"
    assert _run_ci_axiom_check(tmp_path, real9 + extra) != 0


def test_ci_axiom_guard_pins_the_anchor_count_and_closed_lists(tmp_path):
    real = _real_guard().splitlines(True)
    assert _run_ci_axiom_check(tmp_path, "".join(real[:9])) != 0            # one anchor dropped
    assert _run_ci_axiom_check(tmp_path, "".join(real) + real[0]) != 0      # one anchor too many
    truncated = "".join(real[:9]) + "'NatRootBracketTable.t' depends on axioms: [propext,\n"
    assert _run_ci_axiom_check(tmp_path, truncated) != 0                    # header without a closed list


# --- 7. Lean end to end (gated on a built env) ------------------------------------------

def _env_ready():
    from lean_env import lean_env_ready
    olean = _ENV / ".lake" / "build" / "lib" / "lean" / "NatRootBracket.olean"
    return lean_env_ready(_ENV) and olean.is_file()


lean = pytest.mark.skipif(not _env_ready(),
                          reason="nat_root_bracket_table Lean env not built -- skipped")


@lean
def test_lean_end_to_end_four_faces_axiom_clean():
    from telperion.verify import verify_lean
    t = _emit_text([_TBL, _SGL_NEG, _SGL_POS, _SGL_RAT], ["tbl", "neg", "pos", "rat"])
    decls = [f"NatRootBracketTableTest.{n}" for n in ("tbl", "neg", "pos", "rat")]
    r = verify_lean(t, env_dir=_ENV, decls=decls)
    assert r.okay and r.axioms_clean, (r.summary(), r.errors[:3])
    for d in decls:
        assert set(r.axioms[d]) <= {"propext", "Classical.choice", "Quot.sound"}, d


@lean
def test_lean_negative_control_one_table_entry():
    from telperion.negative_control_harness import (
        generic_negative_control, registered_adapters)
    res = generic_negative_control(registered_adapters()["NatRootBracketTableEmitter"],
                                   env_dir=str(_ENV))
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail


@lean
def test_lean_rejects_u_equals_l_on_the_single_face():
    """The survey's control: forge U := L on a non-exact bracket (Layer 1 bypassed by replace);
    `S^q <= U^q m^p` is then false and `decide +kernel` fails on `_hi_fact`."""
    from telperion.negative_control import assert_kernel_rejects
    from telperion.negative_control_harness import emit_via_single_instance_family
    cert = nat_root_bracket_certificate(2, 1, 2, scale=10 ** 6)
    assert cert.hi == cert.lo + 1
    forged = replace(cert, hi=cert.lo)
    body = emit_via_single_instance_family(
        NatRootBracketTableEmitter(), lean_name="forged_u_eq_l", instance_kwargs={"payload": forged})
    assert assert_kernel_rejects(f"import Mathlib\nimport NatRootBracket\n{body}\n",
                                 "forged_u_eq_l", env_dir=_ENV)
