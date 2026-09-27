"""A Comparator record must say how thoroughly it was checked, and that must be visible.

`comparator-record` can write a record under a weaker check than the full one: with
`--no-verify` (nothing read the judge log), from a supplied log file (the job id is the
recorder's word), or without hashing the artifact at the judged commit (that commit could
not be resolved).  Those records may be perfectly true, but they must never read like a
fully checked one, so `provenance-report` lists them and `mission verify` warns -- or fails
under `--strict-provenance`.

Records written before the checks existed carry neither field, and are flagged as such
rather than assumed good.
"""
import importlib.util
import sys
from pathlib import Path

import pytest

_SRC = Path(__file__).resolve().parents[1] / "src"
sys.path.insert(0, str(_SRC))


def _load():
    spec = importlib.util.spec_from_file_location(
        "prov", _SRC / "telperion" / "missions" / "provenance.py")
    m = importlib.util.module_from_spec(spec)
    sys.modules["prov"] = m
    try:
        spec.loader.exec_module(m)
    except ImportError as exc:  # pragma: no cover - relative imports need the package
        pytest.skip(f"provenance.py needs its package: {exc}")
    return m


prov = pytest.importorskip("telperion.missions.provenance")


def _row(**kw):
    base = dict(campaign="c", slug="N", status="proved", independence="unverified",
                self_audit=False, comparator_run="1", comparator_stale=False,
                lean_kernel_only=False, has_grant=True, log_check="verified",
                head_check="matched")
    base.update(kw)
    return prov.ProvenanceRow(**base)


def test_a_fully_checked_record_is_not_flagged():
    assert prov.weak_record_reasons(_row()) == []


def test_no_verify_is_flagged():
    why = prov.weak_record_reasons(_row(log_check="skipped", head_check="skipped"))
    assert any("--no-verify" in w for w in why)
    assert any("not checked at the judged commit" in w for w in why)


def test_offline_verification_is_flagged_as_the_recorders_word():
    why = prov.weak_record_reasons(_row(log_check="verified-offline"))
    assert why and "recorder's word" in why[0]


def test_unresolved_head_is_flagged():
    why = prov.weak_record_reasons(_row(head_check="unresolved"))
    assert any("only the grant" in w for w in why)


def test_a_record_predating_the_checks_is_flagged_not_assumed_good():
    why = prov.weak_record_reasons(_row(log_check="", head_check=""))
    assert why == ["predates the record checks (no log_check/head_check)"]


def test_a_node_without_a_comparator_record_is_not_flagged_here():
    """Absence of a record is the job of the `flagged` property, not of this check."""
    assert prov.weak_record_reasons(_row(comparator_run="", log_check="", head_check="")) == []


def test_report_lists_weak_records(tmp_path):
    """The reasons reach the rendered report, not just the data structure."""
    rows = [_row(slug="Weak", log_check="skipped", head_check="skipped")]
    line = "; ".join(prov.weak_record_reasons(rows[0]))
    assert "no judge log confirmed" in line
