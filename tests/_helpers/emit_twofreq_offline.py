"""Helpers shared by test_emit_twofreq_offline.py (engine) and test_emit_twofreq_offline_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_twofreq_offline import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import (  # noqa: E402
    TwoFreqOfflineEmitter, ValidationReport, certify, emit,
)
from telperion.emit_twofreq_offline import gauss, inv_sqrt, neglog, rat, twofreq_offline_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


def _euler_spec(p, mode="displacement"):
    return {"c1": gauss(1, 0), "c2": inv_sqrt(p, sign=-1),
            "lam1": rat(0), "lam2": neglog(p), "p": p, "mode": mode}


def _emit_one(spec, name="tfo_demo"):
    fam = twofreq_offline_family("TFO", GridSpec([("_", [0])]), lambda pt: name,
                                 spec=lambda pt: spec)
    report = emit(certify(fam),
                  LeanProfile(namespace=("TFO",), imports=("Mathlib", "TwoFreqRigidity"),
                              prelude="open Quasicrystal\n"),
                  [TwoFreqOfflineEmitter()],
                  ValidationReport(checks=(("twofreq_offline", True),)))
    return next(iter(report.files.values()))
