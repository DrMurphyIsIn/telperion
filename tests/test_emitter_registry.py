"""First-class-emitter registry completeness — makes "is the wiring complete?" a CI
question instead of a manual audit.

For every ``kind`` registered in ``certify._SPECIAL_KINDS`` / ``_SPECIAL_DISPATCH``:
  * the two tables agree (no kind in one but not the other);
  * the arm module imports and exposes the ``certify_*_point`` function (certify side);
  * IF the entry carries a third element (emitter class name), that class imports,
    ``emitter_for(kind)`` instantiates it, and its ``.kind`` round-trips to ``kind``.

A half-wired emitter (registered kind with a missing/misnamed certify fn or emitter
class) fails here rather than silently at generate time.  conjecture1_proved = False.
"""
import importlib

import pytest

from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS, emitter_for

# Kinds handled by bespoke branches in `_certify_special_point` (not via _SPECIAL_DISPATCH).
_NON_DISPATCH_KINDS = {"sos", "bracket", "valuation"}

_DISPATCH_KINDS = sorted(set(_SPECIAL_KINDS) - _NON_DISPATCH_KINDS)


def test_special_kinds_and_dispatch_agree():
    """Every dispatch-backed kind is in both tables (no orphan in either direction)."""
    kinds = set(_SPECIAL_KINDS) - _NON_DISPATCH_KINDS
    dispatch = set(_SPECIAL_DISPATCH)
    assert kinds == dispatch, (
        f"in _SPECIAL_KINDS not _SPECIAL_DISPATCH: {sorted(kinds - dispatch)}; "
        f"in _SPECIAL_DISPATCH not _SPECIAL_KINDS: {sorted(dispatch - kinds)}"
    )


@pytest.mark.parametrize("kind", _DISPATCH_KINDS)
def test_certify_fn_resolves(kind):
    """The (module, certify_fn) pair imports and the fn exists (certify side)."""
    entry = _SPECIAL_DISPATCH[kind]
    assert len(entry) >= 2, f"{kind}: dispatch entry too short: {entry!r}"
    mod_name, fn_name = entry[:2]
    mod = importlib.import_module(f"telperion.{mod_name}")
    assert hasattr(mod, fn_name), f"{kind}: {mod_name}.{fn_name} missing"


@pytest.mark.parametrize("kind", _DISPATCH_KINDS)
def test_emitter_class_round_trips_if_registered(kind):
    """If a third element (emitter class) is present, emitter_for round-trips kind."""
    entry = _SPECIAL_DISPATCH[kind]
    if len(entry) < 3 or not entry[2]:
        pytest.skip(f"{kind}: no emitter class registered (certify-only entry)")
    em = emitter_for(kind)
    assert em.kind == kind, f"{kind}: emitter_for gave .kind={em.kind!r}"


def test_emitter_for_refuses_unregistered_emitter():
    """A certify-only (length-2) entry raises a clear ValueError, not a silent None."""
    two_elt = [k for k in _DISPATCH_KINDS if len(_SPECIAL_DISPATCH[k]) < 3]
    if not two_elt:
        pytest.skip("no length-2 entries to check")
    with pytest.raises(ValueError, match="no registered emitter class"):
        emitter_for(two_elt[0])


def test_new_dvp_bc_atoms_are_fully_wired():
    """The three 2026-09-05 emitters carry an emitter class and round-trip."""
    for kind in ("max_modulus", "bc_deriv_re", "entire_part_bound"):
        assert len(_SPECIAL_DISPATCH[kind]) == 3, f"{kind}: expected length-3 entry"
        assert emitter_for(kind).kind == kind
