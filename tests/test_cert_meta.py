"""Tests for telperion.cert_meta — structured proof metadata + content-addressed index."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cert_meta import (  # noqa: E402
    CertIndex,
    CertMeta,
    extract_cert_meta,
    measure_heartbeats,
)

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


def test_index_json_roundtrip():
    idx = CertIndex()
    idx.add(extract_cert_meta(LOG74))
    restored = CertIndex.from_json(idx.to_json())
    assert restored.metas.keys() == idx.metas.keys()
    r = restored.metas["log74_le_4fstar"]
    assert r.type_hash == idx.metas["log74_le_4fstar"].type_hash
    assert r.tactic_counts == idx.metas["log74_le_4fstar"].tactic_counts


def test_certmeta_dict_roundtrip():
    m = extract_cert_meta(LOG74)
    m2 = CertMeta.from_dict(m.to_dict())
    assert m2 == m


def test_measure_heartbeats_int_or_none():
    """measure_heartbeats returns an int > 0 or None gracefully (guarded on env)."""
    trivial = "theorem cert_meta_hb_probe : (1 : ℝ) + 1 = 2 := by norm_num"
    hb = measure_heartbeats(trivial, env_dir=ENV_DIR, name="cert_meta_hb_probe")
    # Must never raise; either a positive int (env available + parsed) or None.
    assert hb is None or (isinstance(hb, int) and hb > 0)
    # When the built env is present, `#count_heartbeats in` should parse a positive int.
    if ENV_DIR.exists() and (ENV_DIR / ".lake").exists():
        assert isinstance(hb, int) and hb > 0, hb


def test_measure_heartbeats_missing_env_returns_none():
    """A nonexistent env_dir yields None, never an exception."""
    hb = measure_heartbeats(
        "theorem t : (1 : ℝ) = 1 := by norm_num",
        env_dir=Path("/nonexistent/telperion/env"),
        name="t",
    )
    assert hb is None
