"""EnclosureIntervalFold emitter (kind ``enclosure_interval_fold``) — the integer
near-CUE row-band checker distilled from ``anthropics/zeta-23-lean`` (PairCeiling
NumericCert.lean / RowCert.lean).

Offline, self-contained: the global certify()/emit() dispatch is NOT wired for
this kind yet (the parent session does the registry wiring), so these tests hit
the emitter DIRECTLY — the certificate builder, ``certify_enclosure_interval_fold_point``,
and ``emit_body`` on a hand-built CertifiedFamily.

Honesty: the emitted theorem is a genuine kernel-checked INTEGER fact
(``rowsOK … = true`` by ``decide``); the Arb enclosures are the trust seam
(inputs).  conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.emit_enclosure_fold import (  # noqa: E402
    DECIDE_N_CEILING,
    EnclosureIntervalFoldEmitter,
    certify_enclosure_interval_fold_point,
    enclosure_interval_fold_certificate,
    enclosure_interval_fold_family,
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
            family=fam, instances=tuple(insts), checks_passed=sum(len(i.payload.encl) for i in insts)
        )
    finally:
        _construction_guard.open = False


def _refused(fn, *a, **k):
    try:
        fn(*a, **k)
        return False
    except ValueError:
        return True


# --------------------------------------------------------------------------- #
# 1. certificate builder — accepts a valid grid, REFUSES each bad case         #
# --------------------------------------------------------------------------- #


def test_valid_small_enclosure_grid_accepted():
    # K = 10, τ = 0.2 -> τK = 2.  Band for row j is [10j - 2, 10j + 2].
    # Enclosures sit inside: j=1 -> [9,11], j=2 -> [19,21], j=3 -> [28,32].
    cert = enclosure_interval_fold_certificate(10, 2, [(9, 11), (19, 21), (28, 32)])
    assert cert.K == 10 and cert.tauK == 2
    assert cert.N == 4  # N = len(encl) + 1
    assert cert.encl == ((9, 11), (19, 21), (28, 32))
    assert cert.use_native is False


def test_tight_band_edges_accepted():
    # Enclosures exactly on the band edges are admissible (≤, not <).
    cert = enclosure_interval_fold_certificate(10, 2, [(8, 12), (18, 22)])
    assert cert.N == 3


def test_refuses_bad_K():
    assert _refused(enclosure_interval_fold_certificate, 0, 2, [(9, 11)])
    assert _refused(enclosure_interval_fold_certificate, -5, 2, [(9, 11)])


def test_refuses_negative_tolerance():
    assert _refused(enclosure_interval_fold_certificate, 10, -1, [(9, 11)])


def test_refuses_empty_enclosure():
    assert _refused(enclosure_interval_fold_certificate, 10, 2, [])


def test_refuses_inconsistent_enclosure():
    # lo > hi is an inconsistent interval.
    assert _refused(enclosure_interval_fold_certificate, 10, 2, [(9, 11), (25, 19)])


def test_refuses_out_of_band_row():
    # j=1 band is [8,12]; enclosure [13,14] is entirely above it -> FALSE claim.
    assert _refused(enclosure_interval_fold_certificate, 10, 2, [(13, 14)])
    # a lower-side violation too: j=2 band [18,22], enclosure [15,17].
    assert _refused(enclosure_interval_fold_certificate, 10, 2, [(9, 11), (15, 17)])


def test_refuses_N_over_decide_ceiling():
    # DECIDE_N_CEILING rows -> N = ceiling + 1, one past the ceiling -> refused.
    big = [(10 * j, 10 * j) for j in range(1, DECIDE_N_CEILING + 1)]
    assert len(big) + 1 == DECIDE_N_CEILING + 1 > DECIDE_N_CEILING
    assert _refused(enclosure_interval_fold_certificate, 10, 0, big)
    # ... but the SAME data is accepted with use_native=True.
    cert = enclosure_interval_fold_certificate(10, 0, big, use_native=True)
    assert cert.use_native is True and cert.N == DECIDE_N_CEILING + 1
    # exactly at the ceiling (N = ceiling) `decide` is still allowed.
    at = [(10 * j, 10 * j) for j in range(1, DECIDE_N_CEILING)]
    ok = enclosure_interval_fold_certificate(10, 0, at)
    assert ok.N == DECIDE_N_CEILING and ok.use_native is False


# --------------------------------------------------------------------------- #
# 2. certify_*_point + emit_body on a hand-built CertifiedFamily               #
# --------------------------------------------------------------------------- #


def _build_family_and_text(spec, name="nearCUE_N4"):
    fam = enclosure_interval_fold_family(
        "EF", GridSpec([("_", [0])]), lambda pt: name, spec=spec)
    pt = next(iter(fam.grid.points()))
    inst, n_checks = certify_enclosure_interval_fold_point(fam, pt, name)
    cf = _make_certified_family(fam, [inst])
    text, n_thm = EnclosureIntervalFoldEmitter().emit_body(cf, LeanProfile())
    return text, n_thm, n_checks, inst


def test_certify_point_returns_row_count_as_checks():
    _, _, n_checks, inst = _build_family_and_text(
        lambda pt: (10, 2, [(9, 11), (19, 21), (28, 32)]))
    assert n_checks == 3            # N - 1 rows, each band membership re-verified
    assert inst.lean_name == "nearCUE_N4"
    assert inst.payload.N == 4


def test_emit_body_contents_and_lint_clean():
    text, n_thm, _, _ = _build_family_and_text(
        lambda pt: (10, 2, [(9, 11), (19, 21), (28, 32)]))
    assert n_thm == 1
    # the self-contained checker + the decide theorem, as specified
    assert "rowsOK" in text
    assert "def enclData_nearCUE_N4" in text
    assert "theorem nearCUE_N4" in text
    assert "by decide" in text
    assert "= true" in text
    # trust-seam provenance is spelled out in the emitted comments
    assert "trust seam" in text.lower()
    assert "ceiling_nearCUE" in text
    assert "conjecture1_proved = False" in text
    # lints clean (no error-severity issues)
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emit_body_deterministic():
    text1, _, _, _ = _build_family_and_text(lambda pt: (10, 2, [(9, 11), (19, 21)]))
    text2, _, _, _ = _build_family_and_text(lambda pt: (10, 2, [(9, 11), (19, 21)]))
    assert text1 == text2


def test_emit_body_native_decide_for_large_N():
    big = [(10 * j, 10 * j) for j in range(1, DECIDE_N_CEILING + 1)]  # N > ceiling
    text, n_thm, _, _ = _build_family_and_text(
        lambda pt: (10, 0, big, True), name="nearCUE_big")
    assert n_thm == 1
    assert "by native_decide" in text
    assert "by decide" not in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_rowsOK_emitted_once_for_multiple_instances():
    # emit_body shares the rowsOK checker across all instances (one def).
    fam = enclosure_interval_fold_family(
        "EF", GridSpec([("k", [0, 1])]),
        lambda pt: f"nearCUE_{pt['k']}",
        spec=lambda pt: (10, 2, [(9, 11), (19, 21)]))
    insts = []
    for pt in fam.grid.points():
        inst, _ = certify_enclosure_interval_fold_point(fam, pt, f"nearCUE_{pt['k']}")
        insts.append(inst)
    cf = _make_certified_family(fam, insts)
    text, n_thm = EnclosureIntervalFoldEmitter().emit_body(cf, LeanProfile())
    assert n_thm == 2
    assert text.count("def rowsOK") == 1
    assert "theorem nearCUE_0" in text and "theorem nearCUE_1" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
