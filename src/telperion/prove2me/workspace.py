"""$HOME/prove2me_workspace management: layout, scratch Lean projects pinned
to the PLATFORM toolchain (never Telperion's own v4.32.0), and lift stubs.

The scratch project is where an attempt's emitted Lean is compiled BEFORE any
submission (invariant I1).  The lift stub embeds the milestone's
formal_statement VERBATIM so faithfulness is reviewable at a glance.
"""
from __future__ import annotations

import subprocess
from pathlib import Path

# From the platform workspace probe (examples/prove2me_compat/README.md).
PLATFORM_TOOLCHAIN = "leanprover/lean4:v4.33.1"
PLATFORM_MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"

_LAKEFILE = """name = "{name}"
defaultTargets = ["{name}"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{mathlib_rev}"

[[lean_lib]]
name = "{name}"
"""

_LIFT_STUB = '''"""Lift of prove2.me milestone {milestone_id} -> Telperion family.

FORMAL STATEMENT (verbatim from the platform -- the kernel checks our theorem
against THIS; keep it untouched for faithfulness review):

{statement_block}

Fill in: symbols, grid (often a single point), target/equation, validation().
A wrong lift fails certify() or the local build -- it cannot reach the platform.
"""
import sympy as sp

from telperion import GridSpec, InequalityFamily
from telperion.workflow import ValidationReport

# telperion must already be importable (the `telperion p2m` CLI process provides it)

MILESTONE_ID = "{milestone_id}"
FORMAL_STATEMENT = {statement_literal}


def family() -> InequalityFamily:
    x = sp.Symbol("x", nonnegative=True)
    return InequalityFamily(
        name="{name}",
        symbols=(x,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "solution",
        target=lambda pt: x - x,   # REPLACE with the lifted inequality
    )


def validation() -> ValidationReport:
    return ValidationReport.from_asserts([
        ("replace-with-exact-rational-spot-checks", lambda: None),
    ])
'''


class Workspace:
    def __init__(self, root: Path | None = None):
        self.root = Path(root) if root else Path.home() / "prove2me_workspace"

    def ensure_layout(self) -> None:
        for d in ("Definitions", "Theorems", "Solutions", "attempts"):
            (self.root / d).mkdir(parents=True, exist_ok=True)
        gi = self.root / ".gitignore"
        required_entries = ["credentials.json", "telperion_tokens.json", ".lake/", "__pycache__/"]
        existing_lines = set()
        if gi.exists():
            existing_lines = set(ln.strip() for ln in gi.read_text().splitlines() if ln.strip())
        new_entries = [ln for ln in required_entries if ln not in existing_lines]
        if new_entries:
            content = (gi.read_text() if gi.exists() else "")
            if content and not content.endswith("\n"):
                content += "\n"
            content += "\n".join(new_entries) + "\n"
            gi.write_text(content)

    def sync_official(self, repo_url: str) -> None:
        """Clone or pull the official platform workspace repo into root."""
        if (self.root / ".git").exists():
            subprocess.run(["git", "-C", str(self.root), "pull", "--ff-only"],
                           check=True)
        else:
            self.root.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "clone", repo_url, str(self.root)], check=True)
        self.ensure_layout()

    def scratch_project(self, name: str, toolchain: str = PLATFORM_TOOLCHAIN,
                        mathlib_rev: str = PLATFORM_MATHLIB_REV) -> Path:
        if not name.isidentifier():
            raise ValueError(f"scratch project name must be an identifier: {name!r}")
        proj = self.root / "attempts" / name / "lean"
        # emitted solution module goes to <proj>/<name>/<name>.lean (imported by the root file)
        (proj / name).mkdir(parents=True, exist_ok=True)
        (proj / "lean-toolchain").write_text(toolchain + "\n")
        (proj / "lakefile.toml").write_text(
            _LAKEFILE.format(name=name, mathlib_rev=mathlib_rev))
        (proj / f"{name}.lean").write_text(f"import {name}.{name}\n")
        return proj

    def scaffold_lift(self, milestone_id: str, formal_statement: str,
                      name: str) -> Path:
        d = self.root / "attempts" / name
        d.mkdir(parents=True, exist_ok=True)
        fam = d / "family.py"
        fam.write_text(_LIFT_STUB.format(
            milestone_id=milestone_id,
            name=name,
            statement_block="\n".join("    " + ln for ln in
                                      formal_statement.splitlines()),
            statement_literal=repr(formal_statement),
        ))
        return fam
