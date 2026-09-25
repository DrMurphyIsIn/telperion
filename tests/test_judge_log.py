"""Reading the independent judge's verdict out of a job log, and refusing to record a lie.

`mission comparator-record` used to write whatever theorem name and kernel mode it was given.
Nothing checked that the cited run had judged that node at all, so the convention -- record
the island theorem exactly as the PASS line prints it -- was enforced only by reviewers
noticing. These tests pin the parser and the checks that replace that trust.
"""
import importlib.util
import sys
from pathlib import Path

import pytest

_SRC = Path(__file__).resolve().parents[1] / "src" / "telperion" / "missions" / "judge_log.py"
_spec = importlib.util.spec_from_file_location("judge_log", _SRC)
jl = importlib.util.module_from_spec(_spec)
# Register before exec: @dataclass resolves annotations through sys.modules[cls.__module__].
sys.modules["judge_log"] = jl
_spec.loader.exec_module(jl)

# A real shard log, trimmed: the workflow's own unexpanded echo of both templates, then
# verdicts for a heavy node (Lean kernel only) and an ordinary one (both kernels).
LOG = """
2026-09-25T19:20:04Z [36;1m    echo "COMPARATOR PASS island=rvm_bridge node=$slug theorem=$thm run=36169770951 kernel=$kernel"[0m
2026-09-25T19:20:04Z [36;1m    echo "::error::COMPARATOR FAIL island=rvm_bridge node=$slug theorem=$thm"[0m
2026-09-25T20:05:11Z COMPARATOR PASS island=rvm_bridge node=MM_weil_positivity_prime_free_window theorem=weil_positivity_prime_free_window run=36169770951 kernel=lean-kernel-only
2026-09-25T20:05:12Z COMPARATOR PASS island=rvm_bridge node=RH_corridor_bound theorem=RvMBridge3.corridor_bound run=36169770951 kernel=nanoda
"""

FAIL_LOG = LOG + (
    "2026-09-25T20:06:00Z ::error::COMPARATOR FAIL island=rvm_bridge "
    "node=MM_weil_positivity_window_two_fifths theorem=weil_positivity_window_two_fifths\n")

HEAVY = "MM_weil_positivity_prime_free_window"


def test_parses_both_verdicts_and_skips_the_unexpanded_templates():
    v = jl.parse_verdicts(LOG)
    assert set(v) == {HEAVY, "RH_corridor_bound"}, "a template echo was read as a verdict"
    assert v[HEAVY].theorem == "weil_positivity_prime_free_window"
    assert v[HEAVY].kernel == "lean-kernel-only"
    assert v[HEAVY].second_kernel == "none: heavy_certificates"
    assert v["RH_corridor_bound"].second_kernel == "nanoda"
    assert v[HEAVY].run == "36169770951"


def test_failed_nodes_skips_templates_too():
    assert jl.failed_nodes(LOG) == []
    assert jl.failed_nodes(FAIL_LOG) == ["MM_weil_positivity_window_two_fifths"]


def test_a_good_record_passes():
    assert jl.check(LOG, node=HEAVY, theorem="weil_positivity_prime_free_window",
                    run_id="36169770951", expect_lean_kernel_only=True) == []


def test_wrong_theorem_is_refused():
    errs = jl.check(LOG, node=HEAVY, theorem="KWin_Bridge.weil_positivity_prime_free_window",
                    run_id="36169770951", expect_lean_kernel_only=True)
    assert errs and "not" in errs[0] and "PASS line prints" in errs[0]


def test_node_absent_from_the_log_is_refused():
    errs = jl.check(LOG, node="MM_weil_positivity_window_two_fifths",
                    theorem="weil_positivity_window_two_fifths", run_id="36169770951")
    assert errs and "no COMPARATOR PASS line" in errs[0]
    assert "nodes judged here" in errs[0], "say which nodes the log does cover"


def test_a_failing_node_is_refused_even_though_others_passed():
    errs = jl.check(FAIL_LOG, node="MM_weil_positivity_window_two_fifths",
                    theorem="weil_positivity_window_two_fifths", run_id="36169770951")
    assert any("COMPARATOR FAIL" in e for e in errs)


def test_wrong_run_id_is_refused():
    errs = jl.check(LOG, node=HEAVY, theorem="weil_positivity_prime_free_window",
                    run_id="99999999", expect_lean_kernel_only=True)
    assert any("cites run 36169770951" in e for e in errs)


def test_claiming_both_kernels_when_only_lean_ran_is_refused():
    """The dangerous direction: a record that overstates what was checked."""
    errs = jl.check(LOG, node=HEAVY, theorem="weil_positivity_prime_free_window",
                    run_id="36169770951", expect_lean_kernel_only=False)
    assert any("--lean-kernel-only" in e and "nanoda did NOT run" in e for e in errs)


def test_claiming_lean_only_when_nanoda_also_ran_is_refused():
    errs = jl.check(LOG, node="RH_corridor_bound", theorem="RvMBridge3.corridor_bound",
                    run_id="36169770951", expect_lean_kernel_only=True)
    assert any("drop the switch" in e for e in errs)


def test_unknown_kernel_mode_is_refused():
    log = LOG.replace("kernel=lean-kernel-only", "kernel=something-new")
    errs = jl.check(log, node=HEAVY, theorem="weil_positivity_prime_free_window")
    assert any("unknown kernel mode" in e for e in errs)


def test_kernel_modes_cover_what_the_workflow_can_print():
    """If the judge learns a new mode, this test is the reminder to map it."""
    wf = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "missions-comparator.yml"
    text = wf.read_text()
    for mode in jl.KERNEL_MODES:
        assert mode in text, f"{mode} is mapped here but the workflow never prints it"
