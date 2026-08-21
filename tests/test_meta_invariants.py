"""A3 — meta-drift net: invariants ABOUT the pipeline, not about any one family.

`verify` byte-diffs frozen families; this is the reflexive analogue one level up
— a standing net asserting that Telperion still HAS its own load-bearing
properties across versions:

  1. the emit-time non-vacuity gate still refuses a reflexive body;
  2. the core/bg trust boundary still holds at runtime;
  3. the CLI still exposes its stable verb surface;
  4. no regression on the certifiable-fragment benchmark solve count.

Each assertion is falsifiable: break the guard and the corresponding test goes red.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401
from telperion.nonvacuity import check_nonvacuous, NonVacuityError  # noqa: E402
from telperion.benchmark import run_benchmark, certifiable_seed_corpus  # noqa: E402
from telperion import cli  # noqa: E402


# Regression floor: measured solve count on the seed corpus (2026-08-20). The net
# guards against a drop; an improvement is welcome and should raise this floor.
BENCHMARK_SOLVE_FLOOR = 8

REFLEXIVE_BODY = "theorem vac : (0 : ℝ) ≤ 0 := by norm_num"
SUBSTANTIVE_BODY = "theorem real (a : ℝ) (ha : 0 ≤ a) : 0 ≤ a := ha"


def test_nonvacuity_gate_still_refuses_a_reflexive_body():
    with pytest.raises(NonVacuityError):
        check_nonvacuous(REFLEXIVE_BODY)


def test_nonvacuity_gate_passes_a_substantive_body():
    # guards against the opposite drift: a gate that refuses everything is useless
    check_nonvacuous(SUBSTANTIVE_BODY)  # must not raise


def test_core_does_not_drag_in_bg_at_runtime():
    bg_loaded = [m for m in sys.modules if m == "telperion.bg" or m.startswith("telperion.bg.")]
    assert bg_loaded == [], f"core import dragged in bg modules: {bg_loaded}"


def test_cli_exposes_its_stable_verb_surface():
    with pytest.raises(SystemExit) as exc:
        cli.main(["--help"])
    assert exc.value.code == 0


@pytest.mark.parametrize("verb", ["certify", "diagnose", "probe", "prove"])
def test_each_stable_verb_is_registered(verb, capsys):
    # invoking a verb with no required args exits nonzero via argparse, but a
    # MISSING verb exits with the "invalid choice" error — distinguish them.
    with pytest.raises(SystemExit):
        cli.main([verb])
    err = capsys.readouterr().err
    assert "invalid choice" not in err, f"verb {verb!r} is not registered"


def test_no_regression_on_certifiable_fragment_benchmark():
    report = run_benchmark(certifiable_seed_corpus())
    assert report.solved >= BENCHMARK_SOLVE_FLOOR, report.render()
