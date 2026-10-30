from telperion.verify import _parse_output

KERNEL = "f.lean:3:0: error: (kernel) declaration type mismatch, 'bad' has type\n  Nat\nbut is expected\n  Bool\n"
ELAB = "f.lean:3:8: error: unknown identifier 'x'\n"
META = "f.lean:5:0: error: declaration has metavariables 'z'\n"


def _r(out, rc=1):
    from telperion.verify import VerifyResult
    return VerifyResult(**_parse_output(out, rc, decls=(), permitted=("propext",)))


def test_kernel_prefixed_is_kernel_rejected():
    r = _r(KERNEL)
    assert r.kernel_rejected and len(r.kernel_errors) == 1 and not r.okay
    assert r.summary().startswith("[KERNEL_REJECTED")


def test_elab_error_is_not_kernel():
    r = _r(ELAB)
    assert not r.kernel_rejected and r.kernel_errors == []


def test_non_prefixed_is_elab():
    assert not _r(META).kernel_rejected


def test_mixed_reports_both():
    r = _r(ELAB + KERNEL)
    assert r.kernel_rejected and len(r.errors) == 2 and len(r.kernel_errors) == 1
