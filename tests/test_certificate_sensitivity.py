"""A2 — emitter-wide certificate-sensitivity: Telperion certifying a meta-property
of its OWN emitters.

`nonvacuity.assert_certificate_sensitive` proves an emitted identity is
load-bearing (a corrupted certificate must break the claim).  Today only the WZ
emitter invokes it.  This meta-test makes the *stance* of every emitter explicit
and enforced: each of the ~30 emitters must be classified (identity-carrying →
CERTIFICATE_SENSITIVE, or positivity/decidable → STRUCTURALLY_NONVACUOUS) with a
rationale, so a newly-added emitter cannot silently ship unclassified.  It also
truthfully reports which CERTIFICATE_SENSITIVE emitters have their semantic check
actually WIRED vs. declared-but-unwired — naming the gap rather than papering it.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (import so every Emitter subclass is loaded)
from telperion.emitter_sensitivity import (  # noqa: E402
    CERTIFICATE_SENSITIVE,
    STRUCTURALLY_NONVACUOUS,
    REGISTRY,
    discover_emitters,
    unclassified_emitters,
    stray_registry_entries,
    wired_sensitive_emitters,
)


def test_every_emitter_is_classified():
    # The standing completeness gate: a new Emitter subclass fails CI until its
    # sensitivity stance is declared in the registry.
    missing = unclassified_emitters()
    assert missing == [], f"emitters missing a sensitivity stance: {missing}"


def test_registry_has_no_stray_entries():
    # No entry may point at an emitter that no longer exists.
    assert stray_registry_entries() == []


def test_all_emitters_discovered():
    # Sanity: the discovery mechanism finds a realistic number of emitters.
    names = {c.__name__ for c in discover_emitters()}
    assert "WZEmitter" in names
    assert "DirectPolyaEmitter" in names
    assert len(names) >= 25


def test_every_stance_has_a_rationale():
    for name, stance in REGISTRY.items():
        assert stance.stance in (CERTIFICATE_SENSITIVE, STRUCTURALLY_NONVACUOUS)
        assert stance.reason.strip(), f"{name} has an empty rationale"


def test_identity_emitters_are_marked_sensitive():
    # The linear-combination / ring-identity emitters carry a corruptible
    # certificate and MUST be marked sensitive.
    for name in ("WZEmitter", "ConeFarkasEmitter", "NullstellensatzEmitter",
                 "ConsequenceEmitter", "HandelmanEmitter"):
        assert REGISTRY[name].stance == CERTIFICATE_SENSITIVE, name


def test_wz_sensitivity_check_is_actually_wired():
    # WZ is the one emitter whose semantic load-bearing check is wired today;
    # the registry's `checked_in` claim must be truthful.
    wired = wired_sensitive_emitters()
    assert "WZEmitter" in wired
