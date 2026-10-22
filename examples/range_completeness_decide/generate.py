"""Generate the range-completeness example: certify -> emit -> write.

    python examples/range_completeness_decide/generate.py           # write lean/RangeCompletenessDecide.lean
    python examples/range_completeness_decide/generate.py --check   # drift check (no write)

Two instances of "every m < N satisfying P is in the explicit list", decided by
`decide +kernel` against the kernel-friendly surrogate `SqfBelow K` and bridged to
Mathlib's `Squarefree` by a once-proved lemma (CN-1 emitter survey item N6; the
template is `mem_nonHeegner190` in the tenth-discriminant formalization):

  * ``sqf_lt_200``       -- the 113 squarefree m < 200 outside the nine Heegner radicands
    {1, 2, 3, 7, 11, 19, 43, 67, 163}, K = 15 (225 > 200); with the length, nodup and
    soundness companions, so the list is EXACTLY that set;
  * ``sqf_3mod4_lt_60``  -- the 14 squarefree m < 60 with m = 3 (mod 4) (an extra decidable
    guard through the finite_decide AST), K = 8 (64 > 60); with the length companion.

The NEGATIVE CONTROL at the emission layer: dropping 199 from the first list is refused by
`range_completeness_certificate` ("coverage is FALSE -- m = 199 ..."); the kernel-level
control (the same drop, Layer 1 bypassed, `decide +kernel` fails) is
`negctrl_adapters/adapter_range_completeness.py`.  The second validation check exercises the
POLICY bound: K = 14 against N = 200 is refused because 14^2 = 196 <= 200, although SqfBelow 14
(and SqfBelow 13) would in fact agree with Squarefree on [0, 200); K^2 > N is a sufficient
condition kept as policy, and the per-m cross-check is the authority on agreement.

conjecture1_proved = False -- finite decidability facts about two explicit lists; nothing
here concerns zeta.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, Cmp, Lit, RangeCompletenessEmitter, SquarefreeSurrogate,
    ValidationReport, Var, certify, emit, range_completeness_family,
)
from telperion.emit_finite_decide import Mod  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
_OUT = _LEAN / "RangeCompletenessDecide.lean"

HEEGNER_NINE = (1, 2, 3, 7, 11, 19, 43, 67, 163)


def squarefree_below(n: int) -> list[int]:
    """The squarefree m < n, by exact trial division (0 is not squarefree)."""
    return [m for m in range(1, n)
            if all(m % (k * k) != 0 for k in range(2, int(n ** 0.5) + 2))]


_SPECS = {
    0: ("sqf_lt_200", dict(
        n=200,
        members=[m for m in squarefree_below(200) if m not in HEEGNER_NINE],
        exclude=HEEGNER_NINE,
        surrogate=SquarefreeSurrogate(15),
        emit_length=True, emit_nodup=True, emit_soundness=True)),
    1: ("sqf_3mod4_lt_60", dict(
        n=60,
        members=[m for m in squarefree_below(60) if m % 4 == 3],
        guards=(Cmp("eq", Mod(Var("m"), Lit(4)), Lit(3)),),
        surrogate=SquarefreeSurrogate(8),
        emit_length=True)),
}


def _validation() -> ValidationReport:
    def dropped_element_refused():
        spec = dict(_SPECS[0][1])
        spec["members"] = [m for m in spec["members"] if m != 199]
        bad = range_completeness_family(
            "Bad", GridSpec([("i", [0])]), lambda pt: "bad", lambda pt: spec)
        try:
            certify(bad)
        except CertificationError as e:
            assert "coverage is FALSE" in str(e) and "199" in str(e), e
            return
        raise AssertionError("a list missing 199 was not refused")

    def weak_bound_refused():
        """K = 14 is below the K^2 > N policy bound (though exact on this range)."""
        spec = dict(_SPECS[0][1])
        spec["surrogate"] = SquarefreeSurrogate(14)          # 14^2 = 196 <= 200: policy refusal
        # (SqfBelow 14 is exact on [0, 200); the bound K^2 > N is sufficient, not necessary)
        bad = range_completeness_family(
            "Bad", GridSpec([("i", [0])]), lambda pt: "bad", lambda pt: spec)
        try:
            certify(bad)
        except CertificationError as e:
            assert "K^2 > N fails" in str(e), e
            return
        raise AssertionError("K = 14 against N = 200 was not refused")

    return ValidationReport.from_asserts([
        ("range_completeness_refuses_dropped_element", dropped_element_refused),
        ("range_completeness_refuses_policy_surrogate_bound", weak_bound_refused),
    ])


def build() -> str:
    fam = range_completeness_family(
        "RangeCompletenessDecide",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _SPECS[pt["case"]][0],
        spec=lambda pt: dict(_SPECS[pt["case"]][1]),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("RangeCompletenessDecide",)),
        [RangeCompletenessEmitter()],
        _validation(),
        file_name="RangeCompletenessDecide.lean",
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: RangeCompletenessDecide.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _LEAN.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
