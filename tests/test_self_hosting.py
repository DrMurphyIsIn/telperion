"""B1 — self-hosting: certify the load-bearing hypotheses of Telperion's OWN
reusable Lean lemmas, in Telperion's exact-arithmetic tier.

`unimodal_peak`, `RTree.telescope`, and `wz_row_invariant` are proven once in
Lean and reused by the emitters.  The self-hosting property is that the concrete
hypotheses each lemma consumes — unimodality, per-node super-solution margins,
the telescoping row identity — are exactly what Telperion certifies.  This module
certifies one concrete instance of each at the exact tier (the half this machine
can verify) and asserts each is LOAD-BEARING (a corruption breaks it).

The remaining half — compiling the prelude lemma + instance against pinned
Mathlib — is cloud-gated (`lake build` in CI); this machine does not build Lean.
See `examples/self_hosting/README.md`.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.self_hosting import (  # noqa: E402
    certify_unimodal_peak_instance,
    certify_telescope_instance,
    certify_wz_row_invariant_instance,
    SelfHostResult,
)


def test_unimodal_peak_hypotheses_certified_and_load_bearing():
    r = certify_unimodal_peak_instance()
    assert isinstance(r, SelfHostResult)
    assert r.certified
    assert r.load_bearing


def test_telescope_super_solution_certified_and_load_bearing():
    r = certify_telescope_instance()
    assert r.certified
    assert r.load_bearing


def test_wz_row_invariant_identity_certified_and_load_bearing():
    r = certify_wz_row_invariant_instance()
    assert r.certified
    assert r.load_bearing


def test_all_three_lemmas_have_a_named_instance():
    for fn in (certify_unimodal_peak_instance,
               certify_telescope_instance,
               certify_wz_row_invariant_instance):
        assert fn().lemma  # a non-empty Lean lemma name it self-hosts
