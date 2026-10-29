"""Helpers shared by test_emit_complex_re_im_split.py (engine) and test_emit_complex_re_im_split_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.emit_complex_re_im_split import ...` resolves, as `from missions_fixtures import ...` does.
"""
from telperion import complex_re_im_split_certificate  # noqa: E402


def _cert(p, mode, **kw):
    cert, _n = complex_re_im_split_certificate(p, mode=mode, **kw)
    return cert
