"""Stage-1 certificate-first triage (spec section 3).

Deterministic and cheap: normalize the Lean formal_statement, match SHAPE_RULES
(regex features -> candidate emitter CLASS NAMES), veto on structure-keyword
blocklist.  Registry-driven honesty: every rule class must exist among the
enumerated Emitter subclasses (unknown_rule_classes == error), and emitters no
rule can select are NAMED in unmatched_registry_classes rather than hidden.
Stage 2 (scouting + the actual lift) is the driving session's job.
"""
from __future__ import annotations

import importlib
import json
import pkgutil
import re
from dataclasses import asdict, dataclass
from pathlib import Path

from .ledger import AttemptLedger

_NUMERIC = r"(ℕ|ℤ|ℚ|ℝ|Nat|Int|Rat|Real)"  # N Z Q R

# Modules outside the emit* naming convention that define Emitter subclasses.
# _load_all_emitters imports these in addition to the emit* scan.
EXTRA_EMITTER_MODULES: tuple[str, ...] = ("tails", "dichotomy", "varmap")

# Structure keywords that mark a statement OUTSIDE certificate shapes.
# Uniform prefix semantics: single alternation, one outer \w* — no inner \b.
BLOCKLIST = re.compile(
    r"\b(Group|Ring|Field|Module|Category|Continuous|Measure|Measurabl|"
    r"Topolog|SimpleGraph|Homeomorph|Isometry|Deriv|integral|"
    r"Filter\.|Matrix\.det)\w*"
)

# Import failures recorded during the last _load_all_emitters() call.
# List of (module_name, error_repr) tuples; cleared and repopulated on each scan.
IMPORT_FAILURES: list[tuple[str, str]] = []


@dataclass(frozen=True)
class ShapeRule:
    feature: str
    emitter_classes: tuple[str, ...]
    pattern: str
    weight: float

    def hits(self, text: str) -> bool:
        return re.search(self.pattern, text) is not None


SHAPE_RULES: tuple[ShapeRule, ...] = (
    ShapeRule(
        "nonneg-or-le-inequality",
        ("DirectPolyaEmitter", "SOSEmitter", "RationalSOSEmitter",
         "PSDFormEmitter", "CauchySchwarzEmitter", "TangentSumEmitter"),
        r"(≤|<)",
        0.4,
    ),
    ShapeRule(
        "polynomial-content",
        ("SOSEmitter", "DirectPolyaEmitter"),
        r"\^\s*\d|\*",
        0.2,
    ),
    ShapeRule(
        "exact-identity",
        ("IdentityEmitter", "ExactFactEmitter", "RationalIdentityEmitter"),
        r"(?<!:)=\s*[-\d(]",  # negative lookbehind excludes Lean's := definitions
        0.5,
    ),
    ShapeRule(
        "padic-valuation",
        ("PadicValuationEmitter",),
        r"padicValNat|padicValRat|multiplicity",
        1.0,
    ),
    ShapeRule(
        "nat-tail",
        ("TailNatEmitter", "EventualThresholdEmitter", "MonotoneRatioTailEmitter"),
        r"∀\s*\w+\s*:\s*ℕ.*(≤|<).*→",
        0.6,
    ),
    ShapeRule(
        "bounded-nat-dispatch",
        ("FiniteDecideEmitter", "CaseDispatchAssemblyEmitter"),
        r"∀\s*\w+\s*:\s*ℕ.*\w\s*(≤|<)\s*\d+\s*→",
        0.7,
    ),
    ShapeRule(
        "infeasibility",
        ("InfeasibilityEmitter", "SOSRefutationEmitter",
         "RealNullstellensatzEmitter"),
        r"¬\s*∃",
        0.8,
    ),
    ShapeRule(
        "finite-sum-identity",
        ("WZEmitter", "IdentityEmitter"),
        r"∑|Finset\.(sum|range)|choose",
        0.6,
    ),
    ShapeRule(
        "interval-enclosure",
        ("IntervalBracketEmitter", "BernsteinEmitter", "SturmPositiveEmitter"),
        r"Real\.exp|Real\.log|Real\.sqrt",
        0.3,
    ),
)


def _load_all_emitters() -> None:
    """Import every module that may define Emitter subclasses.

    Covers two populations:
    - emit*-prefixed modules (the main corpus, discovered via pkgutil)
    - EXTRA_EMITTER_MODULES (tails, dichotomy, varmap — use non-emit names)

    Import failures are recorded in IMPORT_FAILURES (module_name, error_repr)
    rather than silently absorbed so coverage_report() can surface them.
    """
    global IMPORT_FAILURES
    IMPORT_FAILURES = []
    import telperion
    candidates: list[str] = [
        m.name for m in pkgutil.iter_modules(telperion.__path__)
        if m.name.startswith("emit")
    ] + list(EXTRA_EMITTER_MODULES)
    for name in candidates:
        try:
            importlib.import_module(f"telperion.{name}")
        except Exception as exc:
            # Optional-extra emitters (sdp/bg) may have uninstalled deps.
            # Record rather than hide so coverage_report() can name the gap.
            IMPORT_FAILURES.append((name, repr(exc)))


def registry_class_names() -> set[str]:
    _load_all_emitters()
    from telperion.workflow import Emitter
    names: set[str] = set()
    stack = list(Emitter.__subclasses__())
    while stack:
        cls = stack.pop()
        names.add(cls.__name__)
        stack.extend(cls.__subclasses__())
    return names


def coverage_report() -> dict:
    registry = registry_class_names()
    ruled = {c for r in SHAPE_RULES for c in r.emitter_classes}
    return {
        "unknown_rule_classes": sorted(ruled - registry),
        "unmatched_registry_classes": sorted(registry - ruled),
        "import_failures": list(IMPORT_FAILURES),  # (module_name, error_repr)
    }


def match_statement(formal_statement: str) -> tuple[float, tuple[str, ...]]:
    text = " ".join(formal_statement.split())
    has_numeric = re.search(_NUMERIC, text) is not None
    if BLOCKLIST.search(text) or not has_numeric:
        return 0.0, ()
    conf, classes = 0.0, []
    for rule in SHAPE_RULES:
        if rule.hits(text):
            conf += rule.weight
            classes.extend(c for c in rule.emitter_classes if c not in classes)
    return min(conf, 1.0), tuple(classes)


@dataclass(frozen=True)
class QueueItem:
    milestone_id: str        # the THEOREM id (POST /verify target)
    mission_id: str
    statement: str
    emitter_classes: tuple[str, ...]
    score: float
    theorem_name: str = ""   # e.g. "Foo.bar" -> I2 module Theorems.Thm_Foo_bar
    preamble: str = ""       # imports/opens the formal_statement needs to parse


def triage(
    milestones: list[dict], ledger: AttemptLedger | None = None
) -> list[QueueItem]:
    items: list[QueueItem] = []
    for m in milestones:
        if m.get("status", "open") != "open":
            continue
        mid = str(m["id"])
        if ledger is not None and ledger.attempted(mid):
            continue
        stmt = m.get("formal_statement", "")
        conf, classes = match_statement(stmt)
        if conf <= 0:
            continue
        prior = 1.0
        if ledger is not None:
            rates = [ledger.win_rate(c) for c in classes]
            known = [r for r in rates if r is not None]
            if known:
                prior = 0.5 + 0.5 * max(known)
        items.append(QueueItem(
            mid,
            str(m.get("mission_id", "")),
            stmt,
            classes,
            round(conf * prior, 4),
            theorem_name=str(m.get("theorem_name", "")),
            preamble=str(m.get("preamble", "")),
        ))
    return sorted(items, key=lambda i: -i.score)


def save_queue(items: list[QueueItem], path: Path) -> None:
    Path(path).write_text(
        json.dumps(
            {"format": "telperion-p2m-queue-v1",
             "items": [asdict(i) for i in items]},
            indent=1,
        ) + "\n"
    )


def load_queue(path: Path) -> list[QueueItem]:
    doc = json.loads(Path(path).read_text())
    # tolerate queues written before theorem_name/preamble existed
    return [
        QueueItem(**{
            "theorem_name": "", "preamble": "", **d,
            "emitter_classes": tuple(d["emitter_classes"]),
        })
        for d in doc["items"]
    ]
