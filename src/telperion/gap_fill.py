"""Gap-driven emitter loop: sorry-in-cell -> extract goal -> route-match -> fill.

Automates the round-trip that was hand-driven cell-by-cell: the BG session writes
a cell whose analytic core is a ``sorry``-bodied standalone lemma, e.g.

    theorem log79_add_fstar : Real.log (7/9 : ℝ) + FSTAR + 1/24 ≤ 0 := by sorry

and this module EXTRACTS that goal, RECOGNIZES it as a log-combination enclosure,
AUTO-SELECTS the route (monotone / tangent / tight), GENERATES the proof with
``emit_log_combination``, and (optionally) VERIFIES it against a built Lean env.

Scope: the FSTAR-normalized log-enclosure family
``c·log(r) − k·FSTAR (+ const) ≤ q`` (``FSTAR = log(B)/N``, default the BG
``B=621/64, N=11``) — exactly the atoms the BG subaction cells need.  This is the
concrete first slice of an AXLE-style ``sorry2lemma`` → route-match → fill loop;
other emitter families can register their own matchers behind the same interface.

conjecture1_proved = False.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

import sympy as sp

try:
    from .emit_log_combination import (
        LogCombinationEmitter, log_combination_certificate, log_combination_family,
    )
    from .family import GridSpec
    from .lean import LeanProfile
    from .certify import certify
    from .workflow import emit, ValidationReport
except ImportError:  # run directly
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.emit_log_combination import (
        LogCombinationEmitter, log_combination_certificate, log_combination_family,
    )
    from telperion.family import GridSpec
    from telperion.lean import LeanProfile
    from telperion.certify import certify
    from telperion.workflow import emit, ValidationReport


_FSTAR_PRELUDE = "noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11"

# theorem <name> : <statement> := by sorry   (statement may span lines but must not
# itself contain `:=` -- else the non-greedy match leaps across an intervening
# non-sorry declaration into the next `:= by sorry`).
_SORRY_THM = re.compile(
    r"(?:theorem|lemma)\s+([A-Za-z_][\w']*)\s*(?:\([^)]*\)\s*)*:\s*"
    r"((?:(?!:=)[\s\S])+?)\s*:=\s*by\s+sorry",
)
_LOG = re.compile(r"Real\.log\s*\(?\s*([0-9]+\s*/\s*[0-9]+|[0-9]+)\s*(?::\s*ℝ)?\s*\)?")


@dataclass
class Gap:
    name: str
    statement: str


@dataclass
class EnclosureSpec:
    terms: list          # [(coeff, rat), (fneg, fstar_base)]
    q: str               # rational
    route: str           # monotone | tangent | tight
    fstar_base: str = "621/64"
    fstar_den: int = 11


# have <name> : <statement> := by sorry   (an explicit-typed subgoal inside a proof)
_SORRY_HAVE = re.compile(
    r"\bhave\s+([A-Za-z_][\w']*)\s*:\s*((?:(?!:=)[\s\S])+?)\s*:=\s*by\s+sorry",
)
_GOAL = re.compile(r"⊢\s*(.+)")


def extract_gaps(content: str, *, include_haves: bool = False):
    """All ``:= by sorry`` gaps in ``content`` as :class:`Gap`s — standalone
    theorems/lemmas, and (with ``include_haves``) explicit-typed ``have h : T := by
    sorry`` subgoals inside proofs (the AXLE ``have2lemma`` case; the ``have``'s type
    IS the goal, so no elaboration is needed to recover it)."""
    gaps = [Gap(name=m.group(1), statement=" ".join(m.group(2).split()))
            for m in _SORRY_THM.finditer(content)]
    if include_haves:
        gaps += [Gap(name=m.group(1), statement=" ".join(m.group(2).split()))
                 for m in _SORRY_HAVE.finditer(content)]
    return gaps


def extract_sorry_goals(content: str, *, env_dir):
    """Recover the GOAL at each *bare* ``sorry`` (no explicit type) by elaborating a
    copy with every ``sorry`` replaced by ``?_`` and parsing Lean's ``unsolved
    goals`` report — the AXLE ``extract_proof_states`` lesson, Lean-backed (needs a
    built ``env_dir``).  Returns the list of goal strings (the RHS of each ``⊢``).
    For standalone/`have` gaps with explicit types, prefer ``extract_gaps`` (no build)."""
    from .verify import verify_lean
    probed = re.sub(r"\bsorry\b", "?_", content)
    r = verify_lean(probed, env_dir=env_dir)
    return [m.strip() for m in _GOAL.findall(r.raw)]


def match_log_enclosure(statement: str, *, fstar_base="621/64", fstar_den=11):
    """Parse ``c·log(r) − k·FSTAR (+ const) ≤ q`` -> ``EnclosureSpec`` (route TBD),
    or ``None`` if the statement is not a single-log FSTAR enclosure."""
    if "≤" not in statement and "<=" not in statement:
        return None
    lhs, rhs = re.split(r"≤|<=", statement, maxsplit=1)

    # substitute Real.log(rat) -> LOGi symbols, FSTAR -> F, strip ℝ ascriptions
    logs: list = []

    def _sub_log(m):
        r = sp.Rational(m.group(1).replace(" ", ""))
        logs.append(r)
        return f" LOG{len(logs) - 1} "

    def prep(s):
        s = _LOG.sub(_sub_log, s)
        s = s.replace("FSTAR", " F ").replace(":", " ").replace("ℝ", " ")
        s = s.replace("(", " ( ").replace(")", " ) ")
        return s

    n_before = len(logs)
    lhs_s, rhs_s = prep(lhs), prep(rhs)
    n_logs = len(logs)
    syms = {f"LOG{i}": sp.Symbol(f"LOG{i}") for i in range(n_logs)}
    syms["F"] = sp.Symbol("F")
    try:
        L = sp.sympify(lhs_s, locals=syms)
        R = sp.sympify(rhs_s, locals=syms)
    except (sp.SympifyError, SyntaxError, TypeError):
        return None
    expr = sp.expand(L - R)  # inequality is expr ≤ 0

    F = syms["F"]
    fc = expr.coeff(F, 1)
    if not fc.is_number:
        return None
    # collect the single leading log term
    log_terms = []
    for i in range(n_logs):
        c = expr.coeff(syms[f"LOG{i}"], 1)
        if c != 0:
            log_terms.append((c, logs[i]))
    if len(log_terms) != 1:
        return None  # only the single-leading-log family for now
    (c, r) = log_terms[0]
    const = expr
    for i in range(n_logs):
        const = const.coeff(syms[f"LOG{i}"], 0)
    const = const.coeff(F, 0)
    # normalized: c·log(r) + fc·F + const ≤ 0  ==>  c·log(r) − k·FSTAR ≤ q
    #   fneg (= −k) = fc ;  q = −const
    if c <= 0 or not (isinstance(c, sp.Integer) or c == int(c)):
        return None
    terms = [(int(c), f"{r.p}/{r.q}" if r.q != 1 else f"{r.p}"),
             (int(fc), fstar_base)]
    q = -sp.Rational(const)
    return EnclosureSpec(terms=terms, q=f"{q.p}/{q.q}" if q.q != 1 else f"{q.p}",
                         route="", fstar_base=fstar_base, fstar_den=fstar_den)


def pick_route(spec: EnclosureSpec) -> str:
    """Try monotone -> tangent -> tight; return the first route whose certificate
    accepts (raising if none does)."""
    order = ["monotone", "tangent", "tight"] if sp.Rational(spec.q) == 0 \
        else ["tangent", "tight", "monotone"]
    last = None
    for route in order:
        try:
            log_combination_certificate(
                terms=spec.terms, q=spec.q, route=route,
                fstar_base=spec.fstar_base, fstar_den=spec.fstar_den)
            return route
        except ValueError as e:
            last = e
    raise ValueError(f"no route fills {spec.terms} ≤ {spec.q}: {last}")


@dataclass
class FillResult:
    """Outcome of filling one gap.  ``verified``/``axioms_clean`` are ``None`` when
    no ``env_dir`` was supplied (fill-only)."""

    name: str
    proof: str
    matcher: str
    route: str = ""
    verified: object = None       # bool | None
    axioms_clean: object = None   # bool | None
    repaired: list = None         # list of repair records (from telperion.repair)


# --- extensible matcher registry ------------------------------------------------
# A matcher is a (name, recognizer, filler) triple:
#   recognizer(statement) -> spec | None   (None = not this family; may RAISE
#       ValueError if the family shape matches but is unfillable, e.g. no route)
#   filler(gap, spec) -> (proof: str, route: str)
_MATCHERS: list = []


def register_matcher(name, recognizer, filler):
    """Register a gap-family matcher.  Other emitter families plug in here behind
    the same extract -> match -> fill interface (cf. AXLE's family-agnostic loop)."""
    _MATCHERS.append((name, recognizer, filler))


def _extract_theorem(text: str, name: str) -> str:
    """Pull the full ``theorem <name> … := by …`` block out of an emitted file."""
    start = text.index(f"theorem {name}")
    end = text.find("\nend ", start)
    return (text[start:end] if end != -1 else text[start:]).rstrip()


def _log_enclosure_recognizer(statement: str):
    spec = match_log_enclosure(statement)
    if spec is None:
        return None
    spec.route = pick_route(spec)   # raises ValueError if no route fills it
    return spec


def _log_enclosure_filler(gap: Gap, spec: EnclosureSpec):
    fam = log_combination_family(
        "Gap", GridSpec([("case", [0])]), lambda pt: gap.name,
        spec=lambda pt: {"terms": spec.terms, "q": spec.q, "route": spec.route,
                         "fstar_base": spec.fstar_base, "fstar_den": spec.fstar_den})
    rep = emit(certify(fam),
               LeanProfile(namespace=("Gap",), prelude=""),
               [LogCombinationEmitter()],
               ValidationReport(checks=(("log_combination", True),)))
    text = next(iter(rep.files.values()))
    return _extract_theorem(text, gap.name), spec.route


register_matcher("log_enclosure", _log_enclosure_recognizer, _log_enclosure_filler)


def fill_gap(gap: Gap, *, env_dir=None, prelude=None, repair=True,
             allow_axioms=()) -> FillResult:
    """Extract -> match (registry) -> route-select -> emit, then optionally VERIFY
    (and repair) against a built Lean env.  Returns a :class:`FillResult`.  Raises
    ``ValueError`` if no registered family matches (or a matched family cannot fill).
    """
    for name, recognizer, filler in _MATCHERS:
        spec = recognizer(gap.statement)   # may raise ValueError (matched-but-unfillable)
        if spec is None:
            continue
        proof, route = filler(gap, spec)
        res = FillResult(name=gap.name, proof=proof, matcher=name, route=route,
                         repaired=[])
        if env_dir is not None:
            pre = _FSTAR_PRELUDE if prelude is None else prelude
            content = f"import Mathlib\n{pre}\n{proof}\n"
            if repair:
                from .repair import verify_with_repair
                r, final, applied = verify_with_repair(
                    content, env_dir=env_dir, decls=[gap.name], allow_axioms=allow_axioms)
                res.repaired = applied
                if applied and r.okay and r.axioms_clean:
                    res.proof = _extract_theorem(final, gap.name)
            else:
                from .verify import verify_lean
                r = verify_lean(content, env_dir=env_dir, decls=[gap.name],
                                allow_axioms=allow_axioms)
            res.verified = r.okay
            res.axioms_clean = r.axioms_clean
        return res
    raise ValueError(f"gap {gap.name!r} matched no registered family: {gap.statement}")


def _main(argv=None) -> int:
    import argparse
    from pathlib import Path
    ap = argparse.ArgumentParser(description="Fill sorry log-enclosure gaps with emitted proofs.")
    ap.add_argument("file", help="Lean file containing `:= by sorry` enclosure lemmas")
    ap.add_argument("--env", help="built Lake project dir to VERIFY the fills against")
    a = ap.parse_args(argv)
    content = Path(a.file).read_text(encoding="utf-8")
    gaps = extract_gaps(content)
    if not gaps:
        print("no `:= by sorry` gaps found")
        return 0
    ok = True
    for g in gaps:
        try:
            res = fill_gap(g, env_dir=a.env)
        except ValueError as e:
            print(f"[skip] {g.name}: {e}")
            continue
        vtag = "" if res.verified is None else (
            f"  [verified, axioms {'clean' if res.axioms_clean else 'DIRTY'}]"
            if res.verified else "  [VERIFY FAILED]")
        rep = f"  (repaired: {[r[1] + '->' + r[2] for r in res.repaired]})" if res.repaired else ""
        print(f"[fill] {g.name}  (matcher={res.matcher}, route={res.route}){vtag}{rep}")
        print(res.proof)
        print()
        if res.verified is False or res.axioms_clean is False:
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
