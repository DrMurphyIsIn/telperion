"""A2 — emitter-wide certificate-sensitivity: Telperion certifying a meta-property
of its OWN emitters.

`nonvacuity.assert_certificate_sensitive` proves an emitted identity is
load-bearing (a corrupted certificate must break the claim).  Today only the WZ
emitter invokes it.  This meta-test makes the *stance* of every emitter explicit
and enforced: each of the ~42 emitters must be classified (identity-carrying →
CERTIFICATE_SENSITIVE, or positivity/decidable → STRUCTURALLY_NONVACUOUS) with a
rationale, so a newly-added emitter cannot silently ship unclassified.  It also
truthfully reports which CERTIFICATE_SENSITIVE emitters have their semantic check
actually WIRED vs. declared-but-unwired — naming the gap rather than papering it.

Stream B extends this gate with the NEGATIVE-CONTROL declaration: every emitter
must also declare whether it carries a Lean-backed generic negative control (an
adapter) or is not_applicable-with-a-reason, and every REGISTERED adapter must
pass the two-sided kernel control (forged FALSE rejected AND true twin compiles).
The Lean-backed half is guarded by `tests/lean_env.py::lean_env_ready` so it
skips cleanly in a fresh clone with no built mathlib.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
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
from telperion.emitter_sensitivity import (  # noqa: E402  — neg-control layer
    NEG_CONTROL_ADAPTER,
    NEG_CONTROL_NOT_APPLICABLE,
    undeclared_neg_control_emitters,
    neg_control_adapter_gap,
)
from telperion.negative_control_harness import (  # noqa: E402
    ADAPTERS,
    generic_negative_control,
    registered_adapters,
)
from lean_env import lean_env_ready  # noqa: E402

# Import the adapter modules so their register(...) calls populate ADAPTERS.
# (Adapter modules live under telperion; importing telperion above triggers the
# first-party ones.  Any adapter package added later should be imported here or
# be import-triggered by `import telperion`.)


# --- the existing sensitivity gates (unchanged) -----------------------------

def test_every_emitter_is_classified():
    missing = unclassified_emitters()
    assert missing == [], f"emitters missing a sensitivity stance: {missing}"


def test_registry_has_no_stray_entries():
    assert stray_registry_entries() == []


def test_all_emitters_discovered():
    names = {c.__name__ for c in discover_emitters()}
    assert "WZEmitter" in names
    assert "DirectPolyaEmitter" in names
    assert len(names) >= 25


def test_every_stance_has_a_rationale():
    for name, stance in REGISTRY.items():
        assert stance.stance in (CERTIFICATE_SENSITIVE, STRUCTURALLY_NONVACUOUS)
        assert stance.reason.strip(), f"{name} has an empty rationale"


def test_identity_emitters_are_marked_sensitive():
    for name in ("WZEmitter", "ConeFarkasEmitter", "NullstellensatzEmitter",
                 "ConsequenceEmitter", "HandelmanEmitter"):
        assert REGISTRY[name].stance == CERTIFICATE_SENSITIVE, name


def test_wz_sensitivity_check_is_actually_wired():
    wired = wired_sensitive_emitters()
    assert "WZEmitter" in wired


# --- NEW: every emitter must DECLARE a negative-control stance ---------------

def test_every_emitter_declares_neg_control():
    """The standing negative-control completeness gate: each REGISTRY emitter must
    declare either an adapter or (not_applicable + reason).  A new emitter fails
    CI until it declares one — the exact analogue of the sensitivity gate."""
    undeclared = undeclared_neg_control_emitters()
    assert undeclared == [], (
        "emitters missing a neg_control declaration (set neg_control to "
        "NegControlStance(NEG_CONTROL_ADAPTER) or "
        "NegControlStance(NEG_CONTROL_NOT_APPLICABLE, reason)): " + repr(undeclared)
    )


def test_neg_control_stances_are_well_formed():
    for name, stance in REGISTRY.items():
        nc = stance.neg_control
        if nc is None:
            continue  # caught by the completeness gate above
        assert nc.kind in (NEG_CONTROL_ADAPTER, NEG_CONTROL_NOT_APPLICABLE), name
        if nc.kind == NEG_CONTROL_NOT_APPLICABLE:
            assert nc.reason.strip(), (
                f"{name} declares neg_control not_applicable with no reason")


def test_declared_adapters_are_actually_registered():
    """An emitter that DECLARES an adapter must have one live in ADAPTERS — the
    registry cannot claim a control that does not exist (mirrors the
    wired_sensitive_emitters honesty check)."""
    gap = neg_control_adapter_gap()
    assert gap == [], (
        "emitters declaring a neg_control adapter with none registered in "
        "negative_control_harness.ADAPTERS: " + repr(gap))


def test_at_least_the_log_combination_adapter_is_registered():
    # Sanity: the seed adapter re-expressing negative_control.py's control is live.
    assert "LogCombinationEmitter" in ADAPTERS


# --- NEW: every REGISTERED adapter passes the two-sided kernel control -------

_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"

_ADAPTER_ITEMS = sorted(registered_adapters().items())


@pytest.mark.skipif(
    not lean_env_ready(_ENV),
    reason="no built Lean/mathlib env (fresh clone) — Lean-backed control skipped",
)
@pytest.mark.parametrize(
    "emitter_name",
    [name for name, _ in _ADAPTER_ITEMS],
    ids=[name for name, _ in _ADAPTER_ITEMS],
)
def test_generic_negative_control_holds(emitter_name):
    """For every registered adapter: the forged FALSE proof is kernel-REJECTED AND
    the TRUE twin COMPILES clean (`.okay`, the structural invariant).

    A per-emitter env is used when one exists under examples/<snake>/lean; the
    log_combination env is the shared fallback (its `import Mathlib` is all most
    controls need).  Adapters whose Lean requires a bespoke prelude carry it on
    the adapter itself (`adapter.prelude`)."""
    adapter = registered_adapters()[emitter_name]
    env_dir = _env_for(emitter_name)
    res = generic_negative_control(adapter, env_dir=str(env_dir))
    assert res.kernel_rejects is True, (
        f"{emitter_name}: forged FALSE proof was NOT rejected — {res.detail}")
    assert res.true_compiles is True, (
        f"{emitter_name}: TRUE twin failed to compile (control invalid) — "
        f"{res.detail}")
    assert res.okay is True, res.detail


def _env_for(emitter_name):
    """Prefer a per-emitter built env under examples/<name>/lean; else the shared
    log_combination env (adequate for any control whose only import is Mathlib)."""
    root = Path(__file__).resolve().parents[1] / "examples"
    # emitter_name -> a best-effort snake-case example dir guess
    import re
    snake = re.sub(r"Emitter$", "", emitter_name)
    snake = re.sub(r"(?<!^)(?=[A-Z])", "_", snake).lower()
    cand = root / snake / "lean"
    if lean_env_ready(cand):
        return cand
    return _ENV
