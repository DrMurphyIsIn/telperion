"""Empty-band (zero-free) box driver: compute the boundary winding N, assert N == 0, and emit a
Lean `no_zeros_in_box_<tag>` certificate.

This is the driver half of the RH-in-box `55/16` no-low-zeros closure.  Where `run_box`
(generate.py) exhibits and count-matches ON-LINE zeros (`N_line == N_total >= 1`), this driver
handles the EMPTY case: a box with boundary winding `N == 0` contains no zeros at all, so there is
nothing to exhibit.  It REFUSES a box with nonzero winding (that is the count-matching path).

The winding integer and edge non-vanishing are documented Arb (python-flint) NON-KERNEL inputs; the
emitted Lean derives "the box is zero-free" from them via `zeta_count_eq_winding_generic` at N=0.
conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from .arb_enclosure import enclose_zeta_segments
from .emit_box_localization import emit_empty_band_instantiation, empty_band_certificate
from .emit_winding_count import segment_winding_certificate


def _box_tag(re_lo, re_hi, im_lo, im_hi) -> str:
    """Filesystem-safe tag for a box, e.g. [1/100,99/100]x[0,55/16] -> 1d100_99d100_0_55d16."""
    def _t(x: Fraction) -> str:
        return str(x).replace("/", "d").replace("-", "m")
    return "_".join(_t(Fraction(v)) for v in (re_lo, re_hi, im_lo, im_hi))


def run_empty_band(re_lo, re_hi, im_lo, im_hi, *, winding_prec: int = 160, n_seed: int = 4,
                   out_dir: Path | None = None, write: bool = True, check: bool = False) -> str:
    """Compute the boundary winding N of `[re_lo,re_hi] x [im_lo,im_hi]`, assert N == 0, verify edge
    non-vanishing, and emit the empty-band certificate.

    REFUSALS (ValueError):
    * nonzero boundary winding (`N != 0`) — the box contains a zero; use the count-matching driver;
    * a boundary segment enclosure straddling 0 (edge non-vanishing failed);
    * an invalid box (sigma-range excludes 1/2, or the box reaches the pole s = 1) — via
      `empty_band_certificate` / `choose_ball`.

    Returns the emitted Lean text (written to `NoZerosInBox_<tag>.lean` unless `write=False`)."""
    rl, rh, il, ih = (Fraction(v) for v in (re_lo, re_hi, im_lo, im_hi))
    box = (rl, rh, il, ih)

    # 1. Boundary winding N (rigorous zeta Taylor segments -> half-plane-witnessed winding).
    segs = enclose_zeta_segments(box, winding_prec, n_seed=n_seed)
    wind = segment_winding_certificate((rl, rh, il, ih), segs)
    n_total = wind.n
    if n_total != 0:
        raise ValueError(
            f"run_empty_band [{rl},{rh}]x[{il},{ih}]: boundary winding N = {n_total} != 0 — the box "
            f"contains a zero to exhibit; this is the count-matching path (run_box), not an empty band"
        )

    # 2. Edge non-vanishing: no boundary segment enclosure straddles 0 (redundant with the winding
    #    certificate's own refusal, but an explicit driver-level guard).
    for i, (_param, seg_box) in enumerate(segs):
        (slo_re, shi_re), (slo_im, shi_im) = seg_box
        if slo_re <= 0 <= shi_re and slo_im <= 0 <= shi_im:
            raise ValueError(f"run_empty_band: boundary segment {i} straddles 0 — edge non-vanishing failed")

    # 3. Certificate (refuses invalid box AND n_total != 0) + emit.
    cert = empty_band_certificate(str(rl), str(rh), str(il), str(ih), n_total=n_total)
    tag = _box_tag(rl, rh, il, ih)
    text = emit_empty_band_instantiation(cert, tag)
    print(f"run_empty_band [{rl},{rh}]x[{il},{ih}]: winding N=0 (zero-free); emitted no_zeros_in_box_{tag}")

    if write:
        out_dir = Path(out_dir) if out_dir is not None else (
            Path(__file__).resolve().parents[2] / "examples" / "zeta_zero_localization" / "lean")
        out_path = out_dir / f"NoZerosInBox_{tag}.lean"
        if check:
            if not out_path.exists() or out_path.read_text(encoding="utf-8") != text:
                print(f"DRIFT: NoZerosInBox_{tag}.lean does not match regeneration")
            else:
                print(f"check: OK (NoZerosInBox_{tag}.lean regenerates byte-for-byte; winding N == 0)")
        else:
            out_path.write_text(text, encoding="utf-8")
            print(f"wrote {out_path} ({len(text)} bytes)")
    return text
