"""The engine/lab boundary: no engine module imports a lab (spec section 3; enforced in CI).

Labs are research packages that USE the engine. They move out of the standalone Telperion repo,
so the engine must never import them -- statically (any spelling, any nesting) or at runtime.
"""
from __future__ import annotations

import ast
from pathlib import Path
from typing import List, Tuple

LABS: Tuple[str, ...] = ("bg", "rh_jensen", "bg_upper_bound", "bg_bulk_discharge",
                         "li_coeff", "weil_form_eval")


def _is_lab_path(rel_parts: Tuple[str, ...]) -> bool:
    first = rel_parts[0]
    return first in LABS or (len(rel_parts) == 1 and first[:-3] in LABS)


def engine_files(src_pkg: Path) -> List[Path]:
    """Every .py under src/telperion except lab packages/modules (subpackages included)."""
    out = []
    for p in sorted(src_pkg.rglob("*.py")):
        rel = p.relative_to(src_pkg).parts
        if "__pycache__" in rel or _is_lab_path(rel):
            continue
        out.append(p)
    return out


def _names_lab(dotted: str) -> bool:
    parts = dotted.split(".")
    if parts and parts[0] == "telperion":
        parts = parts[1:]
    return bool(parts) and parts[0] in LABS


def lab_imports(path: Path) -> List[Tuple[int, str]]:
    tree = ast.parse(path.read_text(), filename=str(path))
    hits: List[Tuple[int, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if node.level and mod and _names_lab(mod):
                hits.append((node.lineno, f"from {'.' * node.level}{mod} import ..."))
            elif not node.level and _names_lab(mod) and mod.startswith("telperion."):
                hits.append((node.lineno, f"from {mod} import ..."))
            elif (node.level and not mod) or mod == "telperion":
                for a in node.names:
                    if a.name in LABS:
                        hits.append((node.lineno, f"from {'.' * node.level}{mod} import {a.name}"))
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name.startswith("telperion.") and _names_lab(a.name):
                    hits.append((node.lineno, f"import {a.name}"))
    return sorted(hits)
