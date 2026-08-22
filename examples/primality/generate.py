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

# The discharge pattern is proven green (PR #57): Nat.divisors + fin_cases +
# revert hq + decide. This scale-up probes the practical range — kernel `decide`
# on a^(n-1) in ZMod n unfolds npow (n-1) times, so 4-digit primes are the
# interesting stress point. 1009-1 = 2^4·3^2·7 (30 divisors), a genuine
# certificate use (unlike 5/23 which `decide` proves prime directly).
PRIMES = [5, 23, 101, 1009]
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
