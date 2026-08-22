"""Generate the primality example: Pratt/Lucas certificates -> Lean.

    python examples/primality/generate.py           # write lean/Primality.lean
    python examples/primality/generate.py --check    # drift check (no write)

Each prime is certified by `lucas_primality` with a Pratt witness; the exact
`verify_pratt_certificate` self-check gates emission. Start small (cheap kernel
`decide`); scale the list once the first compile is green.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.emit_primality import primality_module  # noqa: E402

# Round 2: the two smallest primes to prove the discharge pattern compiles
# (round 1 failed on fin_cases-over-primeFactors + decide recursion depth; fixed
# with an explicit Finset-literal rewrite + maxRecDepth). Scale up (101, 1009,
# larger) once green.
PRIMES = [5, 23]
_OUT = Path(__file__).resolve().parent / "lean" / "Primality.lean"


def build() -> str:
    return primality_module(PRIMES, namespace="Primality")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    args = ap.parse_args()

    text = build()
    if args.check:
        current = _OUT.read_text(encoding="utf-8") if _OUT.exists() else ""
        if current != text:
            print("DRIFT: Primality.lean does not match the generator output")
            return 1
        print(f"check: OK ({len(PRIMES)} primes, byte-identical)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(PRIMES)} primes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
