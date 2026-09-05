"""Tests for telperion.cert_meta — structured proof metadata + content-addressed index."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))  # for the shared lean_env guard

from telperion.cert_meta import (  # noqa: E402
    CertIndex,
    CertMeta,
    extract_cert_meta,
    measure_heartbeats,
)
from lean_env import lean_env_ready  # noqa: E402

# A real emitted block (from examples/log_combination/lean/LogCombination.lean).
LOG74 = """theorem log74_le_4fstar : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by
  rw [FSTAR]
  have key : 11 * Real.log (7/4 : ℝ) ≤ 4 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) = 11 * Real.log (7/4 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have hle : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) ≤ Real.log ((621/64 : ℝ) ^ (4 : ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [e1] at hle; linarith
  linarith"""

ENV_DIR = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"


def test_extract_basic_fields():
    m = extract_cert_meta(LOG74)
    assert m.name == "log74_le_4fstar"
    # Statement is the type after `:`, up to `:=`.
    assert m.statement.startswith("Real.log")
    assert "≤" in m.statement
    assert "4 * FSTAR" in m.statement
    assert m.proof_length > 0
    assert m.n_lines > 1
    assert isinstance(m.type_hash, str) and len(m.type_hash) == 16
    assert m.heartbeats is None
    # proof_hash is populated and is a 16-hex content hash.
    assert isinstance(m.proof_hash, str) and len(m.proof_hash) == 16


def test_tactic_counts():
    m = extract_cert_meta(LOG74)
    tc = m.tactic_counts
    # norm_num appears twice, linarith twice, positivity once, rw multiple times,
    # have three times (key, e1, hle).
    assert tc["norm_num"] == 2
    assert tc["linarith"] == 2
    assert tc["positivity"] == 1
    assert tc["rw"] >= 2
    assert tc["have"] == 3
    # nlinarith must NOT be triggered by the `linarith` substring.
    assert tc["nlinarith"] == 0


def test_type_hash_stable_under_whitespace_and_ascription():
    a = "theorem t1 : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by norm_num"
    # Same statement, different whitespace and the `: ℝ` ascriptions stripped.
    b = "theorem t2 :   Real.log (7/4) ≤ (4*FSTAR)   := by linarith"
    ma = extract_cert_meta(a)
    mb = extract_cert_meta(b)
    assert ma.type_hash == mb.type_hash, (ma.statement, mb.statement)

    # A genuinely different statement hashes differently.
    c = "theorem t3 : Real.log (5/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by norm_num"
    mc = extract_cert_meta(c)
    assert mc.type_hash != ma.type_hash


def test_proof_hash_stable_under_comment_and_whitespace_churn():
    """Cosmetic churn (reindent, blank lines, added comments) must NOT move proof_hash."""
    base = (
        "theorem t : (1 : ℝ) + 1 = 2 := by\n"
        "  have h : (1 : ℝ) = 1 := rfl\n"
        "  norm_num"
    )
    # Same tactics, but: different indentation, extra blank lines, a line comment,
    # a block comment, and a trailing newline.
    churned = (
        "theorem t : (1 : ℝ) + 1 = 2 := by\n"
        "    -- reindented and commented, but structurally identical\n"
        "    have h : (1 : ℝ) = 1 := rfl   /- inline block comment -/\n"
        "\n"
        "    norm_num\n"
    )
    mb = extract_cert_meta(base)
    mc = extract_cert_meta(churned)
    assert mb.proof_hash == mc.proof_hash, (mb.proof_hash, mc.proof_hash)

    # A block comment spanning multiple lines is also cosmetic.
    block = (
        "theorem t : (1 : ℝ) + 1 = 2 := by\n"
        "  /- a\n     multi-line\n     comment -/\n"
        "  have h : (1 : ℝ) = 1 := rfl\n"
        "  norm_num"
    )
    md = extract_cert_meta(block)
    assert mb.proof_hash == md.proof_hash


def test_proof_hash_changes_when_a_tactic_changes():
    """A real proof change (different tactic) MUST move proof_hash."""
    base = "theorem t : (1 : ℝ) + 1 = 2 := by norm_num"
    changed = "theorem t : (1 : ℝ) + 1 = 2 := by linarith"
    # An added step is also a real change.
    heavier = "theorem t : (1 : ℝ) + 1 = 2 := by have h : True := trivial; norm_num"
    mb = extract_cert_meta(base)
    mc = extract_cert_meta(changed)
    mh = extract_cert_meta(heavier)
    assert mb.proof_hash != mc.proof_hash
    assert mb.proof_hash != mh.proof_hash
    # The statement is identical across all three, so type_hash collides — this is
    # exactly the regression signal proof_hash exists to disambiguate.
    assert mb.type_hash == mc.type_hash == mh.type_hash


def test_proof_hash_not_fused_tokens():
    """Normalization must keep tactic token boundaries (unlike statement normalization).

    `rw [x]` followed by `exact h` must NOT collapse to `rw[x]exacth`; a naive
    delete-all-whitespace would make `a; b` and `ab` collide.
    """
    a = "theorem t : True := by exact trivial"
    b = "theorem t : True := by exacttrivial"
    ma = extract_cert_meta(a)
    mb = extract_cert_meta(b)
    assert ma.proof_hash != mb.proof_hash


def test_duplicates_reports_shared_atom():
    idx = CertIndex()
    m1 = extract_cert_meta(
        "theorem alpha : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by norm_num"
    )
    m2 = extract_cert_meta(
        "theorem beta : Real.log (7/4) ≤ (4*FSTAR) := by linarith"
    )
    m3 = extract_cert_meta(
        "theorem gamma : Real.log (5/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by norm_num"
    )
    idx.add(m1)
    idx.add(m2)
    idx.add(m3)

    dups = idx.duplicates()
    assert m1.type_hash in dups
    assert set(dups[m1.type_hash]) == {"alpha", "beta"}
    # gamma is unique — not a duplicate.
    assert m3.type_hash not in dups


def test_proof_regressions_flags_same_stmt_different_proof():
    """Same statement, different proof body -> flagged; same proof -> not flagged."""
    idx = CertIndex()
    # alpha and beta share a statement (type_hash) but have DIFFERENT proofs.
    alpha = extract_cert_meta(
        "theorem alpha : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by norm_num"
    )
    beta = extract_cert_meta(
        "theorem beta : Real.log (7/4) ≤ (4*FSTAR) := by linarith"
    )
    # gamma and delta share a statement AND the same proof body — no regression.
    gamma = extract_cert_meta("theorem gamma : True := by trivial")
    delta = extract_cert_meta("theorem delta : True := by trivial")
    for m in (alpha, beta, gamma, delta):
        idx.add(m)

    regs = idx.proof_regressions()
    assert alpha.type_hash in regs
    reg_names = {n for (n, _) in regs[alpha.type_hash]}
    assert reg_names == {"alpha", "beta"}
    # The two distinct proof hashes are both present.
    reg_hashes = {ph for (_, ph) in regs[alpha.type_hash]}
    assert reg_hashes == {alpha.proof_hash, beta.proof_hash}
    assert len(reg_hashes) == 2

    # gamma/delta have identical proofs -> NOT a regression.
    assert gamma.type_hash not in regs


def test_index_json_roundtrip():
    idx = CertIndex()
    idx.add(extract_cert_meta(LOG74))
    restored = CertIndex.from_json(idx.to_json())
    assert restored.metas.keys() == idx.metas.keys()
    r = restored.metas["log74_le_4fstar"]
    assert r.type_hash == idx.metas["log74_le_4fstar"].type_hash
    assert r.tactic_counts == idx.metas["log74_le_4fstar"].tactic_counts
    # proof_hash survives the round-trip.
    assert r.proof_hash == idx.metas["log74_le_4fstar"].proof_hash


def test_certmeta_dict_roundtrip():
    m = extract_cert_meta(LOG74)
    m2 = CertMeta.from_dict(m.to_dict())
    assert m2 == m
    assert m2.proof_hash == m.proof_hash


def test_certmeta_from_dict_old_record_without_proof_hash():
    """An OLD serialized record that predates proof_hash must still load (proof_hash=None)."""
    m = extract_cert_meta(LOG74)
    d = m.to_dict()
    # Simulate a record written before the field existed.
    del d["proof_hash"]
    old = CertMeta.from_dict(d)
    assert old.proof_hash is None
    # Everything else still loads.
    assert old.name == m.name
    assert old.type_hash == m.type_hash
    assert old.tactic_counts == m.tactic_counts


def test_index_json_roundtrip_old_record_missing_proof_hash():
    """A whole index JSON blob written by an old version (no proof_hash keys) still loads."""
    m = extract_cert_meta(LOG74)
    d = m.to_dict()
    del d["proof_hash"]
    blob = json.dumps({"metas": [d]})
    idx = CertIndex.from_json(blob)
    assert "log74_le_4fstar" in idx.metas
    assert idx.metas["log74_le_4fstar"].proof_hash is None
    # And such a record is NOT mistaken for a regression (None hashes are ignored).
    assert idx.proof_regressions() == {}


def test_measure_heartbeats_int_or_none():
    """measure_heartbeats returns an int > 0 or None gracefully (guarded on env)."""
    trivial = "theorem cert_meta_hb_probe : (1 : ℝ) + 1 = 2 := by norm_num"
    hb = measure_heartbeats(trivial, env_dir=ENV_DIR, name="cert_meta_hb_probe")
    # Must never raise; either a positive int (env available + parsed) or None.
    assert hb is None or (isinstance(hb, int) and hb > 0)
    # When the env is actually BUILT (not merely a `.lake` dir present), `#count_heartbeats
    # in` must parse a positive int. `lean_env_ready` gates on the built Mathlib.olean, so
    # this never fires against an unbuilt env (which would return None without a rebuild).
    if lean_env_ready(ENV_DIR):
        assert isinstance(hb, int) and hb > 0, hb


def test_measure_heartbeats_missing_env_returns_none():
    """A nonexistent env_dir yields None, never an exception."""
    hb = measure_heartbeats(
        "theorem t : (1 : ℝ) = 1 := by norm_num",
        env_dir=Path("/nonexistent/telperion/env"),
        name="t",
    )
    assert hb is None


# --- AXLE per-cert dependency extraction (extract_decls dependency set) --------------

def test_refs_captures_referenced_identifiers():
    m = extract_cert_meta(
        "theorem t (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by\n"
        "  have h := Real.log_le_sub_one_of_pos (by linarith)\n  linarith\n"
    )
    assert "Real.log_le_sub_one_of_pos" in m.refs
    assert "t" not in m.refs                       # own name excluded


def test_index_dependencies_only_indexed_certs():
    base = extract_cert_meta("theorem base : (0:ℝ) < 1 := by norm_num\n")
    user = extract_cert_meta(
        "theorem user : (0:ℝ) < 2 := by\n  have := base\n  linarith [base]\n")
    idx = CertIndex()
    idx.add(base); idx.add(user)
    # `user` references `base` (indexed) plus tactic/Mathlib tokens (not indexed).
    assert idx.dependencies("user") == {"base"}
    assert idx.dependencies("base") == set()
    assert idx.dependents("base") == {"user"}


def test_index_dead_atoms_and_impact():
    a = extract_cert_meta("theorem a : (0:ℝ) < 1 := by norm_num\n")
    b = extract_cert_meta("theorem b : (0:ℝ) < 2 := by\n  have := a\n  linarith\n")
    root = extract_cert_meta("theorem root : (0:ℝ) < 3 := by\n  have := b\n  linarith\n")
    dead = extract_cert_meta("theorem dead : (0:ℝ) < 9 := by norm_num\n")
    idx = CertIndex()
    for m in (a, b, root, dead):
        idx.add(m)
    # `root` is a top-level goal; `dead` is referenced by nobody.
    assert idx.dead_atoms(roots=["root"]) == ["dead"]
    # changing `a` impacts everything transitively above it.
    assert idx.impacted_by("a") == {"b", "root"}


def test_refs_survive_json_roundtrip():
    idx = CertIndex()
    idx.add(extract_cert_meta(
        "theorem t : True := by\n  have := helper\n  trivial\n"))
    idx2 = CertIndex.from_json(idx.to_json())
    assert "helper" in idx2.metas["t"].refs
