"""`negctrl_adapters.__all__` must equal the adapters the package actually imports.

This file exists because of a live regression, not a hypothetical one.  The module
accumulated FIVE separate `__all__ = [...]` assignments through repeated union merges;
Python keeps the last one, so the export list silently reverted to a stale snapshot and
six wired adapters -- disjoint_discs, exp_enclosure, exp_laurent_identity,
interval_gram_inertia, weil_form_enclosure, window_form_floor -- stopped being exported
while every one of them remained imported and functional.  Nothing failed loudly.

A union merge cannot reintroduce that without turning this test red.
"""
import re
from pathlib import Path

import telperion.negctrl_adapters as negctrl_adapters


def _source() -> str:
    return Path(negctrl_adapters.__file__).read_text()


def test_exactly_one_all_assignment():
    n = len(re.findall(r"(?m)^__all__\s*=", _source()))
    assert n == 1, (
        f"{n} `__all__` assignments in negctrl_adapters/__init__.py; only the last takes "
        "effect, so any earlier one is a silent lie.  Keep exactly one."
    )


def test_every_imported_adapter_is_exported():
    imported = set(re.findall(r"(?m)^from \. import (adapter_\w+)", _source()))
    exported = set(negctrl_adapters.__all__)
    assert imported == exported, (
        f"imported but not exported: {sorted(imported - exported)}; "
        f"exported but not imported: {sorted(exported - imported)}"
    )


def test_exports_are_unique_and_resolvable():
    names = list(negctrl_adapters.__all__)
    assert len(names) == len(set(names)), "duplicate entries in __all__"
    missing = [n for n in names if not hasattr(negctrl_adapters, n)]
    assert not missing, f"__all__ names with no attribute: {missing}"
