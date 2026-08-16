"""Round-2 hardening tests: safe parsing, scaffold e2e, progress, custom assembly."""
import subprocess
import sys
from pathlib import Path

import pytest
import sympy as sp

SRC = Path(__file__).resolve().parents[1] / "src"
sys.path.insert(0, str(SRC))

from telperion import (  # noqa: E402
    CustomAssemblyEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    UnsafeExpressionError,
    ValidationReport,
    certify,
    emit,
    safe_parse_expr,
)
from telperion.scaffold import init_project  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)
GREEN = ValidationReport(checks=(("stub", True),))


# ---- safe parsing -----------------------------------------------------------
def test_safe_parse_accepts_arithmetic():
    e = safe_parse_expr("(1 + u)/(2 + u) - 1/(u + 3)", (u,))
    assert sp.simplify(e - ((1 + u) / (2 + u) - 1 / (u + 3))) == 0


def test_safe_parse_accepts_caret_power():
    e = safe_parse_expr("(u - 1)^2", (u,))
    assert sp.expand(e) == sp.expand((u - 1) ** 2)


@pytest.mark.parametrize(
    "payload",
    [
        "__import__('os').system('true')",
        "u.__class__",
        "[x for x in ()]",
        "lambda: 1",
        "open('/etc/passwd')",
        "w + 1",           # undeclared name
        "u + 'str'",
    ],
)
def test_safe_parse_rejects_hostile_input(payload):
    with pytest.raises(UnsafeExpressionError):
        safe_parse_expr(payload, (u,))


# ---- progress callback ------------------------------------------------------
def test_certify_progress_fires():
    fam = InequalityFamily(
        name="p",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"p_a{pt['a']}",
        target=lambda pt: pt["a"] + u,
    )
    seen = []
    certify(fam, progress=lambda i, total, pt: seen.append((i, total)))
    assert seen == [(1, 3), (2, 3), (3, 3)]


# ---- custom assembly escape hatch -------------------------------------------
def test_custom_assembly_renders_with_hole_checking():
    fam = InequalityFamily(
        name="c",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"c_a{pt['a']}",
        target=lambda pt: pt["a"] + u,
    )
    em = CustomAssemblyEmitter(
        statement_template=(
            "theorem my_assembly : True := by\n«branches»"
        ),
        branch_template="  -- branch for «name»\n",
        fills=lambda cf: {},
        branch_fills=lambda inst: {"name": inst.lean_name},
    )
    res = emit(certify(fam), LeanProfile(), [em], GREEN)
    text = next(iter(res.files.values()))
    assert "-- branch for c_a1" in text and "-- branch for c_a2" in text


# ---- scaffold e2e -----------------------------------------------------------
def test_init_scaffold_generates_and_checks(tmp_path):
    created = init_project(tmp_path / "proj", "DemoProof")
    names = {p.name for p in created}
    assert {"family.py", "generate.py", "telperion.toml", "lakefile.toml",
            "lean-toolchain", "lean-verify.yml"} <= names
    env = {"PYTHONPATH": str(SRC), "PATH": "/usr/bin:/bin"}
    r1 = subprocess.run(
        [sys.executable, "generate.py"],
        cwd=tmp_path / "proj", env=env, capture_output=True, text=True,
    )
    assert r1.returncode == 0, r1.stdout + r1.stderr
    r2 = subprocess.run(
        [sys.executable, "generate.py", "--check"],
        cwd=tmp_path / "proj", env=env, capture_output=True, text=True,
    )
    assert r2.returncode == 0, r2.stdout + r2.stderr
    assert "check: OK" in r2.stdout
    assert (tmp_path / "proj" / "lean" / "DemoProof" / "DemoProof.lean").exists()


def test_init_refuses_nonempty_and_bad_namespace(tmp_path):
    (tmp_path / "x").mkdir()
    (tmp_path / "x" / "f").write_text("")
    with pytest.raises(ValueError, match="not empty"):
        init_project(tmp_path / "x", "Ok")
    with pytest.raises(ValueError, match="UpperCamel"):
        init_project(tmp_path / "y", "lower_case")
