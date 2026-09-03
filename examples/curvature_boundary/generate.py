"""Generate the curvature-boundary example: certify -> emit -> write.

    python examples/curvature_boundary/generate.py           # write lean/CurvatureBoundary.lean
    python examples/curvature_boundary/generate.py --check    # drift check (no write)

Curvature-boundary "extremum-on-the-boundary".  A function whose second
derivative has a DEFINITE SIGN attains its interval extremum at a BOUNDARY point:

* affine  (f'' = 0):  f is endpoint-determined;
* concave (f'' ≤ 0):  min at an endpoint — `min(f a, f b) ≤ f x`;
* convex  (f'' ≥ 0):  max at an endpoint — `f x ≤ max(f a, f b)`.

CROSS-FRONTIER CONVERGENCE: ports the AxiomMath/ZetaZeros (arXiv:2609.02882,
Montgomery–Taylor kernel) ``extremalG_const`` move (`G'' = 0 ⟹ G affine ⟹ const`,
evaluated at `A(±1/2)`) — GENERALIZED to the curvature-sign setting; also covers
the BG per-cell concave-corner case.  Generalizes the ``affine_param_endpoint``
emitter.

Four instances: the concave quadratic `f = -(x²)+x` on [0,1] (the headline port),
a second concave quadratic `f = -2x²+x+1` on [0,1], a convex `f = x²` on [0,1],
and an affine `f = 2x+1` on [0,1].

HONEST SCOPE: reduces a sign-definite-curvature interval extremum to the two
endpoints; verifies the curvature sign in exact sympy (wrong sign ⟹ refusal).  It
does NOT choose f nor prove any downstream inequality.  conjecture1_proved=False.
"""
import argparse
import importlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `curvature_boundary` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_curvature_boundary import (  # noqa: E402
    CurvatureBoundaryEmitter,
    curvature_boundary_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"mode": ..., "f_expr": ..., "a": ..., "b": ...}.
_SPECS = {
    0: {"mode": "concave", "f_expr": "-(x**2) + x", "a": 0, "b": 1},   # headline port
    1: {"mode": "concave", "f_expr": "-2*x**2 + x + 1", "a": 0, "b": 1},
    2: {"mode": "convex", "f_expr": "x**2", "a": 0, "b": 1},
    3: {"mode": "affine", "f_expr": "2*x + 1", "a": 0, "b": 1},
}
_NAMES = {
    0: "concave_quad_min_endpoints",
    1: "concave_quad2_min_endpoints",
    2: "convex_quad_max_endpoints",
    3: "affine_line_boundary",
}
_OUT = Path(__file__).resolve().parent / "lean" / "CurvatureBoundary.lean"


def build() -> str:
    fam = curvature_boundary_family(
        "CurvatureBoundary",
        GridSpec([("case", [0, 1, 2, 3])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("CurvatureBoundary",)),
        [CurvatureBoundaryEmitter()],
        ValidationReport(checks=(("curvature_boundary", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: CurvatureBoundary.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
