"""P2 — 3-XOR moment-matrix PSD emitter (GF(2) closure → block-rank-one SOS).

A degree-d SoS lower bound for an UNSAT 3-XOR (Tseitin) instance whose width-2d
closure is conflict-free: the moment matrix is block-rank-one, so its PSD claim
emits as a compact SOS (one square per derivability class) via `ring`+`positivity`.
Certification is exact GF(2)/closure — a satisfiable instance, a width conflict
(refutation), or a non-block-rank-one matrix is refused.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import Xor3MomentPSDEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_xor3 import xor3_certificate, xor3_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _petersen():
    """Tseitin 3-XOR on the Petersen graph (girth 5): UNSAT, width-4-conflict-free."""
    edges = []
    for i in range(5):
        edges.append((i, (i + 1) % 5))
        edges.append((5 + i, 5 + (i + 2) % 5))
        edges.append((i, i + 5))
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    eidx = {e: k for k, e in enumerate(edges)}
    inst = [(frozenset(eidx[e] for e in edges if v in e), -1 if v == 0 else 1)
            for v in range(10)]
    return inst, len(edges)


def test_petersen_certifies_block_rank_one_psd():
    inst, n = _petersen()
    cert = xor3_certificate(inst, n, degree=2)
    assert cert.n_classes > 1                 # a nontrivial (non-identity) matrix
    assert len(cert.sos_terms) == cert.n_classes
    assert len(cert.idx) == 1 + n + n * (n - 1) // 2   # ∅ + singletons + pairs


def test_satisfiable_instance_is_refused():
    # a single clause is satisfiable — no SoS lower bound to certify
    fam = xor3_family("Sat", GridSpec([("_", [0])]), lambda pt: "sat",
                      spec=lambda pt: ([({0, 1, 2}, 1)], 3, 2))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a satisfiable instance must be refused"


def test_low_width_refutation_is_refused():
    # x_{012}=+1 and x_{012}=-1: UNSAT with a width-3 refutation -> closure conflict
    fam = xor3_family("Conf", GridSpec([("_", [0])]), lambda pt: "conf",
                      spec=lambda pt: ([({0, 1, 2}, 1), ({0, 1, 2}, -1)], 3, 2))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "an instance with a width-≤4 refutation must be refused"


def test_emit_is_lint_clean_and_deterministic():
    inst, n = _petersen()
    fam = xor3_family("Pet", GridSpec([("_", [0])]), lambda pt: "petersen_moment_psd",
                      spec=lambda pt: (inst, n, 2))
    report = emit(certify(fam), LeanProfile(namespace=("Xor3",)),
                  [Xor3MomentPSDEmitter()], ValidationReport(checks=(("xor3", True),)))
    text = next(iter(report.files.values()))
    assert "ring" in text and "positivity" in text
    assert "nlinarith" not in text            # deterministic, no search
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "Xor3MomentPSDEmitter" in REGISTRY
