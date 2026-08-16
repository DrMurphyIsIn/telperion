"""`telperion init`: scaffold a new proof project.

Creates the complete starting layout for a fresh inequality-formalization
project: a family template (with the validation() discipline built in), a
Lean project shell pinned to the known-good toolchain, the project manifest,
and a GitHub Actions workflow that compiles the emitted Lean.  The scaffold
compiles as-is once the family's TODOs are filled.
"""
from __future__ import annotations

from pathlib import Path

KNOWN_GOOD_TOOLCHAIN = "leanprover/lean4:v4.32.0"
KNOWN_GOOD_MATHLIB = "v4.32.0"

FAMILY_TEMPLATE = '''"""My inequality family — edit the TODOs, then:

    telperion diagnose  '<a typical instance>' --symbols u     # certifiable at all?
    telperion certify   family.py:family -v
    telperion emit      family.py:family -o frozen/ --file-name {ns}.lean
    (copy frozen/{ns}.lean into lean/{ns}/ and build in CI)
    telperion verify                                            # the drift net
"""
from __future__ import annotations

import random
from fractions import Fraction

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

u = sp.Symbol("u", nonnegative=True)  # TODO: your continuous symbols


def family() -> InequalityFamily:
    return InequalityFamily(
        name="{ns}",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),          # TODO: your finite grid
        lean_name=lambda pt: "{ns_lower}_a{{}}".format(pt["a"]),
        # TODO: your claim — 0 <= target(pt) over nonneg symbols
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


def profile() -> LeanProfile:
    return LeanProfile(namespace=("{ns}",))


def validation() -> ValidationReport:
    """Exact-rational spot checks BEFORE formalization (no floats, ever)."""
    rng = random.Random(0)
    fam = family()

    def spot():
        for pt in fam.grid.points():
            for _ in range(50):
                uu = sp.Rational(Fraction(rng.randint(0, 400), rng.randint(1, 20)))
                val = fam.target(pt).subs({{u: uu}})
                assert val >= 0, (pt, uu, val)

    return ValidationReport.from_asserts([("exact_spot_checks", spot)])
'''

MANIFEST_TEMPLATE = """# `telperion verify` runs every entry; unlisted generate scripts FAIL verification.
[[check]]
name = "{ns_lower}"
script = "generate.py"
group = "quick"
"""

GENERATE_TEMPLATE = '''"""certify -> validate -> emit -> freeze for this project.  --check = drift diff."""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from family import family, profile, validation

from telperion import DirectPolyaEmitter, certify, diff_frozen, emit, freeze

HERE = Path(__file__).resolve().parent


def build():
    return emit(certify(family()), profile(), [DirectPolyaEmitter()], validation(),
                file_name="{ns}.lean")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        live = HERE / "lean" / "{ns}" / "{ns}.lean"
        live_ok = live.exists() and live.read_text() == res.files["{ns}.lean"]
        ok = rep.ok and live_ok
        if not rep.ok:
            print("DRIFT:", *rep.details, sep="\\n  ")
        if not live_ok:
            print("DRIFT: lean/{ns}/{ns}.lean differs from regenerated text")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    freeze(res, HERE / "frozen")
    (HERE / "lean" / "{ns}").mkdir(parents=True, exist_ok=True)
    (HERE / "lean" / "{ns}" / "{ns}.lean").write_text(res.files["{ns}.lean"])
    print(f"wrote {ns}.lean ({{0}} theorems); hash {{1}}".format(res.n_theorems,
                                                                 res.input_hash[:16]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''

LAKEFILE_TEMPLATE = """name = "{ns}"
defaultTargets = ["{ns}"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{mathlib}"

[[lean_lib]]
name = "{ns}"
"""

ROOT_LEAN_TEMPLATE = """/- Library root — imports the generated certificate file(s). -/
import {ns}.{ns}
"""

WORKFLOW_TEMPLATE = """name: lean-verify

on:
  push:
  workflow_dispatch:

jobs:
  verify-and-build:
    runs-on: ubuntu-latest
    timeout-minutes: 60
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: "3.12"
      - run: pip install sympy telperion
      - name: Drift net (regeneration diff for every frozen family)
        run: telperion verify
      - name: Cache elan
        uses: actions/cache@v4
        with:
          path: ~/.elan
          key: elan-${{{{ runner.os }}}}-${{{{ hashFiles('lean/lean-toolchain') }}}}
      - name: Install elan
        run: |
          curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
      - name: Build the emitted Lean (the actual verification)
        working-directory: lean
        run: |
          lake exe cache get
          lake build
"""


def init_project(directory: Path, namespace: str) -> list[Path]:
    ns = namespace
    if not ns.isidentifier() or not ns[0].isupper():
        raise ValueError("namespace must be an UpperCamel identifier (Lean module name)")
    d = directory
    if d.exists() and any(d.iterdir()):
        raise ValueError(f"{d} exists and is not empty")
    created: list[Path] = []

    def w(rel: str, text: str) -> None:
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        created.append(p)

    subs = {"ns": ns, "ns_lower": ns.lower(), "mathlib": KNOWN_GOOD_MATHLIB}
    w("family.py", FAMILY_TEMPLATE.format(**subs))
    w("generate.py", GENERATE_TEMPLATE.format(**subs))
    w("telperion.toml", MANIFEST_TEMPLATE.format(**subs))
    w("lean/lakefile.toml", LAKEFILE_TEMPLATE.format(**subs))
    w("lean/lean-toolchain", KNOWN_GOOD_TOOLCHAIN + "\n")
    w(f"lean/{ns}.lean", ROOT_LEAN_TEMPLATE.format(**subs))
    w(".github/workflows/lean-verify.yml", WORKFLOW_TEMPLATE)
    w(
        ".gitignore",
        "__pycache__/\n*.pyc\n.lake/\n",
    )
    return created
