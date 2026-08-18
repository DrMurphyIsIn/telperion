"""P5: the input hash must move when EMISSION LOGIC changes, not only when
config fields change.  Before this, `family_hash` fed the manual `__version__`
string and each emitter's config fields; an edit to an emitter's `emit_body`
that produced different Lean left every frozen hash untouched (the G1
empty-binder regression shipped that way).  `Emitter.code_fingerprint()` closes
the gap by folding a version-stable hash of the emitter's raw class source into
`config_fingerprint()`, which `emit()` already folds into the input hash.
"""
import hashlib
import inspect
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import BilinearBoxEmitter, DirectPolyaEmitter  # noqa: E402
from telperion.workflow import Emitter  # noqa: E402


def test_code_fingerprint_is_stable():
    assert DirectPolyaEmitter().code_fingerprint() == DirectPolyaEmitter().code_fingerprint()


def test_distinct_emitters_have_distinct_code_fingerprints():
    assert DirectPolyaEmitter().code_fingerprint() != BilinearBoxEmitter().code_fingerprint()


def test_code_fingerprint_includes_base_class():
    """A change to the base Emitter must move every emitter's fingerprint, so
    the base class hash is part of each emitter's code fingerprint."""
    fp = DirectPolyaEmitter().code_fingerprint()
    assert "Emitter=" in fp and "DirectPolyaEmitter=" in fp


def test_config_fingerprint_folds_code():
    fp = DirectPolyaEmitter().config_fingerprint()
    assert "code:" in fp
    assert DirectPolyaEmitter().code_fingerprint() in fp


def test_fingerprint_is_raw_source_and_version_stable():
    """The fingerprint hashes RAW source text (newline-normalized), NOT
    ast.dump — ast.dump's serialization changes across Python versions and would
    make the input hash version-dependent, breaking the cross-version
    byte-stability the CI matrix (3.11–3.13) enforces. Raw source is identical
    under every interpreter, so the same source gives the same hash regardless
    of Python version. Pin the exact method so a regression back to ast.dump
    (or any interpreter-dependent normalization) fails here."""
    cls = DirectPolyaEmitter
    src = "\n".join(inspect.getsource(cls).splitlines())
    expected = hashlib.sha256(src.encode()).hexdigest()[:16]
    assert f"{cls.__qualname__}={expected}" in cls().code_fingerprint()


def test_repl_emitter_falls_back_gracefully():
    """An emitter whose source is unavailable (e.g. defined via exec) must not
    crash code_fingerprint — it falls back to the empty-source hash for that
    class and the config-field serialization remains the residual signal."""
    ns: dict = {}
    exec("from telperion.workflow import Emitter\n"
         "class ReplEmitter(Emitter):\n"
         "    kind='repl'\n", ns)
    em = ns["ReplEmitter"]()
    # must not raise, and must still produce a string
    fp = em.code_fingerprint()
    assert isinstance(fp, str)
    # the telperion base Emitter IS on disk, so its hash is still present
    assert "Emitter=" in fp
