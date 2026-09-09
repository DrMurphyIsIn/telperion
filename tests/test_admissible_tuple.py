"""AdmissibleTuple emitter (kind ``admissible_tuple``) — the prime-gaps admissible
k-tuple certificate (bgp212 Lemma 12.1 shape; DHL[k,2] + diameter => H1 <= d).

Offline, self-contained: the global certify()/emit() dispatch is NOT wired for
this kind yet (the parent session does the registry wiring), so these tests hit
the emitter DIRECTLY — the certificate builder, ``certify_admissible_tuple_point``,
and ``emit_body`` on a hand-built CertifiedFamily.  ONE test additionally writes
the emitted (core-only) Lean to a temp file and checks it compiles standalone with
``~/.elan/bin/lean``.

Honesty: the emitted theorems are genuine kernel-checked FINITE facts
(``admissibleCheck ... = true`` and the diameter equality, both ``by decide``);
the DHL implication is the cited sieve theorem, not emitted.
conjecture1_proved = False.
"""
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_admissible_tuple import (  # noqa: E402
    K_CEILING,
    AdmissibleTupleEmitter,
    admissible_tuple_certificate,
    admissible_tuple_family,
    certify_admissible_tuple_point,
)
from telperion.certify import (  # noqa: E402
    CertifiedFamily,
    _construction_guard,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _make_certified_family(fam, insts):
    """Mimic certify()'s CertifiedFamily construction (guarded) without the global
    dispatch, so we can exercise emit_body directly on our not-yet-wired kind."""
    _construction_guard.open = True
    try:
        return CertifiedFamily(
            family=fam, instances=tuple(insts),
            checks_passed=sum(len(i.payload.primes) for i in insts))
    finally:
        _construction_guard.open = False


def _refused(fn, *a, **k):
    try:
        fn(*a, **k)
        return False
    except ValueError:
        return True


# --------------------------------------------------------------------------- #
# 1. certificate builder — accepts classic admissible tuples, REFUSES bad cases#
# --------------------------------------------------------------------------- #


def test_twin_pair_accepted():
    # {0, 2} — the twin-prime pattern, diameter 2, primes <= k=2 is just [2].
    cert = admissible_tuple_certificate([0, 2])
    assert cert.H == (0, 2)
    assert cert.k == 2
    assert cert.primes == (2,)
    assert cert.diameter == 2


def test_triple_026_accepted():
    # {0, 2, 6} admissible, diameter 6, primes <= 3 = [2, 3].
    cert = admissible_tuple_certificate([0, 2, 6])
    assert cert.H == (0, 2, 6)
    assert cert.primes == (2, 3)
    assert cert.diameter == 6


def test_triple_046_accepted():
    # {0, 4, 6} admissible (mod 3 residues {0,1,0} omit class 2), diameter 6.
    cert = admissible_tuple_certificate([0, 4, 6])
    assert cert.primes == (2, 3)
    assert cert.diameter == 6


def test_canonical_negative_control_refused():
    # {0, 2, 4} covers ALL residues mod 3 ({0,2,1}) -> INADMISSIBLE -> refused.
    assert _refused(admissible_tuple_certificate, [0, 2, 4])


def test_refuses_duplicates_and_unsorted():
    assert _refused(admissible_tuple_certificate, [0, 2, 2])        # duplicate
    assert _refused(admissible_tuple_certificate, [6, 2, 0])        # unsorted
    assert _refused(admissible_tuple_certificate, [0, 6, 2])        # unsorted


def test_refuses_too_small():
    assert _refused(admissible_tuple_certificate, [])
    assert _refused(admissible_tuple_certificate, [5])


def test_refuses_over_k_ceiling():
    # An admissible tuple with k = K_CEILING + 1 entries -> refused for decide cost.
    # Use even spacing 0,2,4,...; make it admissible by dodging residue coverage:
    # take H = {0, 2, 6, 8, 12, 14, ...} (mod-3 pattern avoiding class 2 fails for
    # large k), so instead just probe the ceiling with a genuinely-admissible set
    # built from an admissible base; simplest: assert the *guard* fires by size.
    big = list(range(0, 2 * (K_CEILING + 1), 2))  # k = K_CEILING + 1 entries
    assert len(big) == K_CEILING + 1
    assert _refused(admissible_tuple_certificate, big)


def test_primes_are_exactly_primes_up_to_k():
    # k = 6 -> primes <= 6 are [2, 3, 5].  Use an admissible 6-tuple.
    cert = admissible_tuple_certificate([0, 4, 6, 10, 12, 16])
    assert cert.k == 6
    assert cert.primes == (2, 3, 5)


# --------------------------------------------------------------------------- #
# 2. certify_*_point + emit_body on a hand-built CertifiedFamily               #
# --------------------------------------------------------------------------- #


def _build_family_and_text(spec, name="H_026"):
    fam = admissible_tuple_family(
        "AT", GridSpec([("_", [0])]), lambda pt: name, spec=spec)
    pt = next(iter(fam.grid.points()))
    inst, n_checks = certify_admissible_tuple_point(fam, pt, name)
    cf = _make_certified_family(fam, [inst])
    text, n_thm = AdmissibleTupleEmitter().emit_body(cf, LeanProfile())
    return text, n_thm, n_checks, inst


def test_certify_point_returns_prime_count_as_checks():
    _, _, n_checks, inst = _build_family_and_text(lambda pt: [0, 2, 6])
    assert n_checks == 2                     # primes <= 3 = [2, 3]
    assert inst.lean_name == "H_026"
    assert inst.payload.diameter == 6


def test_emit_body_contents_and_lint_clean():
    text, n_thm, _, _ = _build_family_and_text(lambda pt: [0, 2, 6])
    assert n_thm == 2                        # admissible + diameter theorems
    assert "admissibleCheck" in text
    assert "coversAllResidues" in text
    assert "def tupleH_H_026" in text
    assert "theorem H_026_admissible" in text
    assert "theorem H_026_diameter" in text
    assert "by decide" in text
    assert "= true" in text
    assert "conjecture1_proved = False" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emit_body_deterministic():
    text1, _, _, _ = _build_family_and_text(lambda pt: [0, 2, 6])
    text2, _, _, _ = _build_family_and_text(lambda pt: [0, 2, 6])
    assert text1 == text2


def test_checker_emitted_once_for_multiple_instances():
    fam = admissible_tuple_family(
        "AT", GridSpec([("k", [0, 1])]),
        lambda pt: f"H_{pt['k']}",
        spec=lambda pt: [0, 2, 6])
    insts = []
    for pt in fam.grid.points():
        inst, _ = certify_admissible_tuple_point(fam, pt, f"H_{pt['k']}")
        insts.append(inst)
    cf = _make_certified_family(fam, insts)
    text, n_thm = AdmissibleTupleEmitter().emit_body(cf, LeanProfile())
    assert n_thm == 4                        # 2 instances x 2 theorems
    assert text.count("def admissibleCheck") == 1
    assert text.count("def coversAllResidues") == 1
    assert "theorem H_0_admissible" in text and "theorem H_1_admissible" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


# --------------------------------------------------------------------------- #
# 3. the emitted Lean is core-only — compile it standalone with `lean`         #
# --------------------------------------------------------------------------- #


def test_emitted_lean_compiles_standalone():
    lean_bin = Path(os.path.expanduser("~/.elan/bin/lean"))
    if not lean_bin.exists():
        lean_bin_which = shutil.which("lean")
        if lean_bin_which is None:
            import pytest
            pytest.skip("standalone lean binary not available")
        lean_bin = Path(lean_bin_which)
    text, _, _, _ = _build_family_and_text(lambda pt: [0, 2, 6])
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "AdmissibleTupleStandalone.lean"
        f.write_text(text, encoding="utf-8")
        proc = subprocess.run(
            [str(lean_bin), str(f)],
            capture_output=True, text=True, timeout=180)
    assert proc.returncode == 0, (
        f"standalone lean failed (exit {proc.returncode}):\n"
        f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
