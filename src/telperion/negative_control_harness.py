"""Generic negative-control ENGINE — the two-layer ``disprove`` lesson, for every
emitter.

``negative_control.py`` proves, for the ONE log-combination emitter, the
load-bearing claim of Telperion's trust model: even if the untrusted Python
self-check (Layer 1) were bypassed and the generator FORGED a certificate of a
FALSE statement, the emitted Lean **fails to compile** — the Lean KERNEL, not
our Python, is the arbiter (Layer 2).  This module GENERALIZES that control to
any emitter, and adds the missing half a negative control alone cannot supply.

Two things every genuine negative control must establish, together:

1. NEGATIVE — a forged proof of a FALSE instance is REJECTED by the kernel
   (:func:`negative_control.assert_kernel_rejects`).
2. POSITIVE (the invariant) — a genuine proof of the TRUE twin COMPILES clean.

Requirement 2 is what stops a rejection-for-the-wrong-reason from masquerading
as a passing control: if the emitter's Lean is malformed (a typo, a missing
lemma, a renamed Mathlib API), the FALSE proof is rejected too — but so is the
TRUE twin.  :class:`GenericNegativeControlResult` therefore makes ``okay`` a
computed property ``kernel_rejects AND true_compiles`` with NO settable backing
field: it is structurally impossible to report ``okay=True`` without a compiled
positive twin.

An adapter (:class:`NegativeControlAdapter`) is the per-emitter glue: it supplies
a forged-false certificate, a true-twin certificate, and the callable that turns
a certificate into emitted Lean.  Most emitters expose only the monolithic public
``emit_body(fam, profile)`` (not private ``_emit_<route>`` like log_combination),
so :func:`emit_via_single_instance_family` builds a one-instance
:class:`CertifiedFamily` carrying the (forged or true) cert and calls
``emit_body`` — an adapter may target EITHER that helper OR a private route.

Untrusted sympy/Python generates; the Lean KERNEL is the sole arbiter.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

import sympy as sp

try:  # normal package import
    from .certify import (
        CertifiedFamily,
        CertifiedInstance,
        _construction_guard,
    )
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .negative_control import assert_kernel_rejects
    from .verify import verify_lean
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import (
        CertifiedFamily,
        CertifiedInstance,
        _construction_guard,
    )
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.negative_control import assert_kernel_rejects
    from telperion.verify import verify_lean
    from telperion.workflow import Emitter


# ---------------------------------------------------------------------------
# The TRUSTED Layer-2 positive primitive — inverse of assert_kernel_rejects.
# ---------------------------------------------------------------------------

def assert_kernel_accepts(
    content, name, *, env_dir, prelude="", allow_axioms=()
) -> bool:
    """Confirm the Lean KERNEL ACCEPTS the proof of theorem ``name`` CLEAN.

    The exact inverse of :func:`negative_control.assert_kernel_rejects`: returns
    ``True`` iff ``content`` (with ``prelude`` spliced after any leading imports,
    via the same splice ``assert_kernel_rejects`` uses) elaborates with no Lean
    error AND every checked declaration carries only permitted axioms.  A TRUE
    twin that fails to compile — a typo, a missing prelude lemma, a renamed
    Mathlib API — returns ``False``, which is what forces the negative control's
    ``okay`` to ``False`` (a rejection-for-the-wrong-reason cannot masquerade).

    Reuses :func:`assert_kernel_rejects` so the SAME elaboration path (identical
    prelude splicing, identical clean-axiom gate) decides both directions; there
    is no second, subtly-different notion of "compiles".
    """
    return not assert_kernel_rejects(
        content, name, env_dir=env_dir, prelude=prelude, allow_axioms=allow_axioms
    )


# ---------------------------------------------------------------------------
# Single-forged-instance CertifiedFamily helper (for the emit_body route).
# ---------------------------------------------------------------------------

_FAMILY_MODES = (
    "target", "before", "after", "equation", "witnesses", "bracket",
    "valuation_facts", "special",
)


def build_single_instance_family(
    *, lean_name: str, instance_kwargs: Mapping[str, Any],
    family_name: str = "negctrl", family_kwargs: "Mapping[str, Any] | None" = None,
) -> CertifiedFamily:
    """Mint a ONE-instance :class:`CertifiedFamily` carrying a (forged or true)
    certificate, WITHOUT going through :func:`certify.certify` (which would refuse
    a forged-false cert at its self-check — that refusal is Layer 1, deliberately
    bypassed here so Layer 2 can be exercised).

    ``instance_kwargs`` are the payload fields the target emitter's ``emit_body``
    reads off each :class:`CertifiedInstance` — e.g. ``{"payload": cert}`` for the
    log-combination / BG first-class emitters, ``{"equation": (lhs, rhs)}`` for the
    identity/consequence emitters, or ``{"corners": (polya_cert,)}`` for the
    positivity emitters.  ``point`` and ``lean_name`` are filled here; anything not
    supplied defaults to the :class:`CertifiedInstance` empties.

    GOTCHA (the construction guard): ``CertifiedFamily.__post_init__`` refuses any
    caller but ``certify()``.  This helper flips ``certify._construction_guard``
    exactly as ``certify.restrict_instances`` does (open in a try/finally), so the
    forged family is legally constructed for the SOLE purpose of feeding
    ``emit_body`` — it is never certified and never emitted through ``workflow.emit``.
    """
    # `corners` is a required positional field of CertifiedInstance (the positivity
    # route); default it to the empty tuple when an adapter does not supply it, so
    # the equation/payload routes need not pass it explicitly.
    kwargs = dict(instance_kwargs)
    kwargs.setdefault("corners", ())
    inst = CertifiedInstance(point={}, lean_name=lean_name, **kwargs)
    # `InequalityFamily.__post_init__` requires EXACTLY ONE mode. Most emitters'
    # emit_body reads the instance and never consults the family mode, so a dummy
    # `target` satisfies the validation harmlessly; the exception is SOSEmitter,
    # whose emit_body reads `fam.family.target(inst.point)` for the polynomial p —
    # its adapter passes the real mode via `family_kwargs={"target": ...}`.
    fmode = dict(family_kwargs) if family_kwargs else {}
    # An emitter whose emit_body binds `∀ <symbols>` (cone, WZ, SOS, …) reads them
    # from fam.family.symbols; a symbolic instance must declare its free symbols via
    # family_kwargs={"symbols": (...)} or the emitted theorem references unbound
    # identifiers (both twins fail to compile — the positive-control invariant then
    # correctly refuses the control).
    symbols = tuple(fmode.pop("symbols", ()))
    if not any(k in fmode for k in _FAMILY_MODES):
        fmode["target"] = lambda pt: sp.Integer(0)
    fam = InequalityFamily(
        name=family_name,
        symbols=symbols,
        grid=GridSpec(axes=(("i", (0,)),)),
        lean_name=lambda pt: lean_name,
        **fmode,
    )
    _construction_guard.open = True
    try:
        return CertifiedFamily(
            family=fam, instances=(inst,), checks_passed=0,
        )
    finally:
        _construction_guard.open = False


def emit_via_single_instance_family(
    emitter: Emitter, *, lean_name: str, instance_kwargs: Mapping[str, Any],
    profile: LeanProfile | None = None,
    family_kwargs: "Mapping[str, Any] | None" = None,
) -> str:
    """Render ONE forged/true instance through ``emitter.emit_body`` and return the
    Lean body text (dropping the theorem count).

    The default route for the ~40 emitters that expose only the monolithic public
    ``emit_body(fam, profile)``.  An adapter whose emitter has a usable private
    ``_emit_<route>(cert, name)`` may bypass this and call that directly instead —
    both are equally valid ``emit_call`` implementations (see
    :class:`NegativeControlAdapter`).
    """
    fam = build_single_instance_family(
        lean_name=lean_name, instance_kwargs=instance_kwargs,
        family_kwargs=family_kwargs,
    )
    body, _n = emitter.emit_body(fam, profile or LeanProfile())
    return body


# ---------------------------------------------------------------------------
# The adapter interface (what 18 downstream adapter agents target).
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NegativeControlAdapter:
    """Per-emitter glue for the generic negative-control engine.

    An adapter is a pure DATA + CALLABLES record; it holds no kernel/verify logic
    of its own (:func:`generic_negative_control` owns all Lean interaction).

    Fields:

    * ``emitter_name`` — the ``Emitter`` subclass name this control targets; matches
      a key of ``emitter_sensitivity.REGISTRY`` and is what the gate test uses to
      pair an adapter to a registry stance.
    * ``make_false_cert`` — ``() -> cert``: build a certificate of a FALSE instance
      BY HAND, bypassing the emitter's own ``*_certificate()`` self-check (Layer 1).
      Whatever object the emitter's ``emit_call`` consumes.
    * ``make_true_cert`` — ``() -> cert``: build a certificate of a genuinely TRUE
      twin (the tightest honest instance the emitter certifies).
    * ``emit_call`` — ``(cert, name) -> str``: render ``cert`` as Lean source that
      states-and-proves ``theorem <name> : ... := by ...`` (a proof ATTEMPT, never a
      ``sorry`` stub).  Two idiomatic implementations:
        - single-instance-family route: wrap
          :func:`emit_via_single_instance_family` (emitter exposes only
          ``emit_body``);
        - private route: call ``emitter._emit_<route>(cert, name)`` directly
          (emitter exposes a per-instance renderer, as log_combination does).
    * ``prelude`` — Lean spliced AFTER any leading imports (e.g. the ``FSTAR`` def);
      passed straight to ``assert_kernel_rejects`` / ``assert_kernel_accepts``.
      Default ``""``.
    * ``allow_axioms`` — extra axiom names to permit beyond mathlib's three when
      axiom-checking BOTH twins (rarely needed; default empty).
    * ``label`` — human-readable summary of the false claim being disproved.
    * ``imports_line`` — the file's leading import(s); default ``"import Mathlib"``.
      ``emit_call`` returns only the theorem block, so the engine prepends this.

    ``make_false_cert`` / ``make_true_cert`` are callables (built fresh per run)
    rather than pre-built certs so an adapter module stays import-cheap and any
    sympy construction happens only when the (Lean-backed) control actually runs.
    """

    emitter_name: str
    make_false_cert: Callable[[], Any]
    make_true_cert: Callable[[], Any]
    emit_call: Callable[[Any, str], str]
    prelude: str = ""
    allow_axioms: tuple[str, ...] = ()
    label: str = ""
    imports_line: str = "import Mathlib"


# ---------------------------------------------------------------------------
# The generic engine result — okay is a STRUCTURAL invariant, not a field.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GenericNegativeControlResult:
    """Outcome of one adapter's Layer-2 negative control.

    ``kernel_rejects`` — the forged FALSE proof was rejected by the kernel (the
    load-bearing negative claim).  ``true_compiles`` — the genuine TRUE twin
    compiled clean (the positive-control INVARIANT).

    ``okay`` is a read-only PROPERTY, ``kernel_rejects and true_compiles`` — there
    is no settable ``okay`` field, so a caller cannot report success without a
    compiled positive twin.  A rejection-for-the-wrong-reason (the emitter's Lean
    is malformed, so the FALSE proof is rejected for a compile error unrelated to
    falsity) is caught: the TRUE twin then also fails to compile,
    ``true_compiles=False``, and ``okay`` is ``False`` regardless of
    ``kernel_rejects``.
    """

    emitter_name: str
    kernel_rejects: bool          # Layer 2 negative: forged FALSE proof rejected
    true_compiles: bool           # Layer 2 positive INVARIANT: TRUE twin compiles
    false_name: str = ""
    true_name: str = ""
    label: str = ""
    detail: str = ""

    @property
    def okay(self) -> bool:
        """The control HOLDS iff the false twin is rejected AND the true twin
        compiles.  Both bytes-of-truth are required; neither alone suffices."""
        return bool(self.kernel_rejects) and bool(self.true_compiles)


def generic_negative_control(
    adapter: NegativeControlAdapter, *, env_dir,
    false_name: str = "negctrl_forged_false",
    true_name: str = "negctrl_true_twin",
) -> GenericNegativeControlResult:
    """Run the two-sided Layer-2 negative control for ``adapter`` against the
    built Lean env at ``env_dir``.

    (a) NEGATIVE — build the forged FALSE cert (bypassing Layer 1), emit it via
        ``adapter.emit_call``, and assert the kernel REJECTS it
        (:func:`negative_control.assert_kernel_rejects`).
    (b) POSITIVE (invariant) — build the TRUE-twin cert, emit it, and assert the
        kernel ACCEPTS it clean (:func:`assert_kernel_accepts`).

    Returns a :class:`GenericNegativeControlResult` whose ``okay`` property is
    ``kernel_rejects and true_compiles``.  Requires a real Lean env — callers must
    guard with ``tests/lean_env.py::lean_env_ready``.
    """
    # (a) NEGATIVE: forge a false cert, emit, confirm the kernel rejects it.
    false_cert = adapter.make_false_cert()
    false_body = adapter.emit_call(false_cert, false_name)
    false_content = f"{adapter.imports_line}\n{false_body}\n"
    kernel_rejects = assert_kernel_rejects(
        false_content, false_name, env_dir=env_dir,
        prelude=adapter.prelude, allow_axioms=adapter.allow_axioms,
    )

    # (b) POSITIVE INVARIANT: emit the TRUE twin, confirm the kernel accepts it.
    true_cert = adapter.make_true_cert()
    true_body = adapter.emit_call(true_cert, true_name)
    true_content = f"{adapter.imports_line}\n{true_body}\n"
    true_compiles = assert_kernel_accepts(
        true_content, true_name, env_dir=env_dir,
        prelude=adapter.prelude, allow_axioms=adapter.allow_axioms,
    )

    neg = ("kernel REJECTED the forged FALSE proof" if kernel_rejects
           else "kernel ACCEPTED the forged FALSE proof (control BREACH)")
    pos = ("TRUE twin compiled clean" if true_compiles
           else "TRUE twin FAILED to compile (control INVALID — rejection may be "
                "for the wrong reason)")
    detail = f"[{adapter.emitter_name}] negative[{neg}] | positive[{pos}]"
    return GenericNegativeControlResult(
        emitter_name=adapter.emitter_name,
        kernel_rejects=bool(kernel_rejects),
        true_compiles=bool(true_compiles),
        false_name=false_name,
        true_name=true_name,
        label=adapter.label,
        detail=detail,
    )


# ---------------------------------------------------------------------------
# The adapter registry (downstream adapter modules call register()).
# ---------------------------------------------------------------------------

ADAPTERS: dict[str, NegativeControlAdapter] = {}


def register(adapter: NegativeControlAdapter) -> NegativeControlAdapter:
    """Register ``adapter`` under its ``emitter_name`` (returned for chaining).

    Refuses a duplicate emitter_name with a different adapter object — two adapter
    modules must not silently contend for the same emitter.  Re-registering the
    SAME object (idempotent import) is a no-op.
    """
    name = adapter.emitter_name
    existing = ADAPTERS.get(name)
    if existing is not None and existing is not adapter:
        raise ValueError(
            f"negative-control adapter already registered for {name!r}; "
            "two modules must not register the same emitter"
        )
    ADAPTERS[name] = adapter
    return adapter


def registered_adapters() -> dict[str, NegativeControlAdapter]:
    """A snapshot copy of the adapter registry (for the parametrized gate test)."""
    return dict(ADAPTERS)


# ---------------------------------------------------------------------------
# First adapter: log_combination (re-expressing negative_control.py's control
# through the generic engine, via the emitter's private _emit_<route>).
# ---------------------------------------------------------------------------

def _log_combination_adapter() -> NegativeControlAdapter:
    """The log-combination control, re-expressed as the first generic adapter.

    NEGATIVE twin: the classic false monotone ``log(3) − 4·FSTAR ≤ 0`` (fold
    ``3^11 / (621/64)^4 ≈ 20 > 1``; the emitted ``norm_num`` fact ``3^11 ≤
    (621/64)^4`` is false, so the forged proof will not compile).
    TRUE twin: ``log(7/4) − 4·FSTAR ≤ 0`` (fold ≈ 0.053 ≤ 1), the BG
    ``log74_le_4fstar`` shape.

    Uses the emitter's PRIVATE ``_emit_monotone`` route directly (log_combination
    is the one emitter with a per-instance renderer), demonstrating the private-
    route ``emit_call`` alongside the single-instance-family route other adapters
    use.  This does NOT touch ``negative_control.log_combination_negative_control``
    (still the canonical two-LAYER control there); it is the same falsity re-run
    through the generic two-SIDED engine.
    """
    import sympy as sp

    from .emit_log_combination import (
        LogCombinationCertificate,
        LogCombinationEmitter,
    )
    from .negative_control import FSTAR_PRELUDE

    B = sp.Rational(621, 64)
    N = sp.Integer(11)
    emitter = LogCombinationEmitter()

    def _cert(rat) -> LogCombinationCertificate:
        rat = sp.Rational(rat)
        fold = sp.nsimplify(rat ** (1 * N) / B ** 4)   # r^{cN} / B^{k}, k=4
        return LogCombinationCertificate(
            coeff=sp.Integer(1), rat=rat, fstar_coeff=sp.Integer(4),
            fstar_base=B, fstar_den=N, q=sp.Integer(0), route="monotone",
            fold_value=fold,
        )

    return NegativeControlAdapter(
        emitter_name="LogCombinationEmitter",
        make_false_cert=lambda: _cert(3),          # fold ≈ 20 > 1  (FALSE)
        make_true_cert=lambda: _cert(sp.Rational(7, 4)),  # fold ≈ 0.053 ≤ 1  (TRUE)
        emit_call=lambda cert, name: emitter._emit_monotone(cert, name),
        prelude=FSTAR_PRELUDE,
        label="log(3) - 4*FSTAR <= 0 is FALSE (fold 3^11/(621/64)^4 ~ 20 > 1)",
    )


register(_log_combination_adapter())
