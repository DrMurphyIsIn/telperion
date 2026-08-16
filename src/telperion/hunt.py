"""The adversarial minimizer: try hard, exactly, to break a claim.

The origin campaign's confidence in each conjectured inequality came from
genuinely attacking it — hillclimbing over trees, adversarial sweeps,
hard-verification with adversarial training — before any proof attempt.  This
module is that discipline as a primitive: an exact-rational optimizer that
minimizes an expression over the closed orthant (or a box) by seeded
coordinate descent with a rational perturbation schedule and restarts.

Everything is exact: a returned value below zero is a THEOREM (the claim is
false, witness attached); a nonnegative minimum is evidence, not proof.
"""
from __future__ import annotations

import random
from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class HuntResult:
    minimum: sp.Rational
    argmin: dict            # {symbol name: exact Rational}
    evaluations: int

    @property
    def is_disproof(self) -> bool:
        return self.minimum < 0

    def render(self) -> str:
        arg = ", ".join(f"{k} = {v}" for k, v in self.argmin.items())
        tag = "DISPROOF (exact witness)" if self.is_disproof else "adversarial minimum"
        return f"{tag}: {self.minimum} at {arg}"


_STEPS = [
    sp.Integer(1), sp.Rational(1, 2), sp.Rational(1, 4), sp.Rational(1, 16),
    sp.Rational(1, 64), sp.Rational(1, 512),
]
_SNAPS = [
    sp.Integer(0), sp.Rational(1, 8), sp.Rational(1, 4), sp.Rational(1, 2),
    sp.Integer(1), sp.Integer(2), sp.Integer(4), sp.Integer(16),
]


def hunt_minimum(
    expr: sp.Expr,
    syms,
    iters: int = 400,
    restarts: int = 6,
    seed: int = 0,
    lo: dict | None = None,
    hi: dict | None = None,
) -> HuntResult:
    """Minimize expr over syms >= 0 (optionally boxed by lo/hi per symbol),
    exactly.  Coordinate descent: from each start, sweep coordinates trying
    snaps and +/- rational steps (multiplicative and additive), accepting
    strict improvements, shrinking the schedule as sweeps stall."""
    lo = lo or {}
    hi = hi or {}
    rng = random.Random(seed)
    evals = 0

    def clamp(s, x):
        if s in lo and x < lo[s]:
            x = lo[s]
        if s in hi and x > hi[s]:
            x = hi[s]
        return x if x >= 0 else sp.Integer(0)

    def value(point):
        nonlocal evals
        evals += 1
        v = expr.subs(point)
        return v if v.is_number else None

    best_v, best_p = None, None
    for restart in range(restarts):
        point = {}
        for s in syms:
            if restart == 0:
                point[s] = clamp(s, sp.Integer(0))
            else:
                point[s] = clamp(
                    s, sp.Rational(rng.randint(0, 64 * 8), rng.randint(1, 8))
                )
        cur = value(point)
        if cur is None:
            continue
        budget = iters
        improved = True
        while improved and budget > 0:
            improved = False
            for s in syms:
                candidates = [clamp(s, c) for c in _SNAPS]
                x = point[s]
                for d in _STEPS:
                    candidates += [clamp(s, x + d), clamp(s, x - d)]
                    if x != 0:
                        candidates += [clamp(s, x * (1 + d)), clamp(s, x / (1 + d))]
                if s in hi:
                    candidates.append(hi[s])
                seen = set()
                for c in candidates:
                    if c in seen:
                        continue
                    seen.add(c)
                    budget -= 1
                    trial = dict(point)
                    trial[s] = c
                    tv = value(trial)
                    if tv is not None and tv < cur:
                        cur, point = tv, trial
                        improved = True
                if budget <= 0:
                    break
        if best_v is None or cur < best_v:
            best_v, best_p = cur, dict(point)
    return HuntResult(
        minimum=best_v,
        argmin={str(k): v for k, v in best_p.items()},
        evaluations=evals,
    )


# ---------------------------------------------------------------- GA + QD hunts
# The Arda evolution engine's transferable pieces, exact-rational: a small
# genetic algorithm with the coordinate-descent above as the MEMETIC refiner
# (population explores basins, descent polishes champions), and a MAP-Elites
# style quality-diversity archive that returns DIVERSE near-tight points —
# tie varieties have many points, and a pure minimizer only ever finds one.
# Deliberately absent: Rust kernels (audit surface) and the island/climate
# machinery (overkill at these budgets).  Named future step: pluggable
# domains (the origin campaign's hunt evolved TREES via Prufer sequences).


def _mutate(point, syms, rng, clamp):
    child = dict(point)
    s = syms[rng.randrange(len(syms))]
    x = child[s]
    kind = rng.randrange(4)
    if kind == 0:
        child[s] = clamp(s, _SNAPS[rng.randrange(len(_SNAPS))])
    elif kind == 1:
        d = _STEPS[rng.randrange(len(_STEPS))]
        child[s] = clamp(s, x + (d if rng.random() < 0.5 else -d))
    elif kind == 2 and x != 0:
        d = _STEPS[rng.randrange(len(_STEPS))]
        child[s] = clamp(s, x * (1 + d) if rng.random() < 0.5 else x / (1 + d))
    else:
        child[s] = clamp(s, sp.Rational(rng.randint(0, 64 * 8), rng.randint(1, 8)))
    return child


def _crossover(a, b, syms, rng):
    child = {}
    for s in syms:
        r = rng.random()
        if r < 0.4:
            child[s] = a[s]
        elif r < 0.8:
            child[s] = b[s]
        else:
            child[s] = (a[s] + b[s]) / 2   # exact rational blend
    return child


def hunt_evolve(
    expr: sp.Expr,
    syms,
    pop: int = 24,
    gens: int = 30,
    seed: int = 0,
    lo: dict | None = None,
    hi: dict | None = None,
    memetic_every: int = 10,
) -> HuntResult:
    """GA hunt: tournament selection + rational crossover/mutation, with
    periodic coordinate-descent refinement of the champion (the memetic
    pattern).  Better than pure descent on multimodal landscapes."""
    lo, hi = lo or {}, hi or {}
    rng = random.Random(seed)
    evals = 0

    def clamp(s, x):
        if s in lo and x < lo[s]:
            x = lo[s]
        if s in hi and x > hi[s]:
            x = hi[s]
        return x if x >= 0 else sp.Integer(0)

    def value(point):
        nonlocal evals
        evals += 1
        v = expr.subs(point)
        return v if v.is_number else None

    population = []
    for i in range(pop):
        p = {
            s: clamp(s, sp.Rational(rng.randint(0, 64 * 8), rng.randint(1, 8)))
            for s in syms
        }
        if i == 0:
            p = {s: clamp(s, sp.Integer(0)) for s in syms}
        v = value(p)
        if v is not None:
            population.append((v, p))
    for g in range(gens):
        population.sort(key=lambda t: t[0])
        nxt = population[:2]  # elitism
        while len(nxt) < pop:
            a = min(rng.sample(population, min(3, len(population))), key=lambda t: t[0])[1]
            b = min(rng.sample(population, min(3, len(population))), key=lambda t: t[0])[1]
            child = _mutate(_crossover(a, b, syms, rng), syms, rng, clamp)
            v = value(child)
            if v is not None:
                nxt.append((v, child))
        population = nxt
        if (g + 1) % memetic_every == 0:
            champ_v, champ = min(population, key=lambda t: t[0])
            refined = hunt_minimum(
                expr, syms, iters=80, restarts=1, seed=seed + g, lo=lo, hi=hi
            )
            evals += refined.evaluations
            rp = {s: refined.argmin[str(s)] for s in syms}
            rv = value(rp)
            if rv is not None and rv < champ_v:
                population.append((rv, rp))
    best_v, best_p = min(population, key=lambda t: t[0])
    return HuntResult(
        minimum=best_v,
        argmin={str(k): v for k, v in best_p.items()},
        evaluations=evals,
    )


def _cell_key(point, syms):
    """Dyadic behavior descriptor: which scale-cell of the domain a point
    occupies (0, (0,1/4], (1/4,1], (1,4], (4,16], (16,inf))."""
    edges = [sp.Integer(0), sp.Rational(1, 4), sp.Integer(1), sp.Integer(4), sp.Integer(16)]
    key = []
    for s in syms:
        x = point[s]
        c = 0
        for e in edges:
            if x > e:
                c += 1
        key.append(c)
    return tuple(key)


def hunt_diverse(
    expr: sp.Expr,
    syms,
    iters: int = 800,
    seed: int = 0,
    lo: dict | None = None,
    hi: dict | None = None,
    top: int = 8,
) -> list[HuntResult]:
    """Quality-diversity hunt (MAP-Elites-lite): maintain the best exact value
    per dyadic domain cell, evolving by mutating randomly chosen elites.
    Returns the `top` most-tight DIVERSE points — tie varieties have many
    points, and a pure minimizer only ever finds one."""
    lo, hi = lo or {}, hi or {}
    rng = random.Random(seed)
    evals = 0

    def clamp(s, x):
        if s in lo and x < lo[s]:
            x = lo[s]
        if s in hi and x > hi[s]:
            x = hi[s]
        return x if x >= 0 else sp.Integer(0)

    def value(point):
        nonlocal evals
        evals += 1
        v = expr.subs(point)
        return v if v.is_number else None

    archive: dict[tuple, tuple] = {}

    def offer(point):
        v = value(point)
        if v is None:
            return
        key = _cell_key(point, syms)
        if key not in archive or v < archive[key][0]:
            archive[key] = (v, dict(point))

    for _ in range(max(16, len(syms) * 8)):
        offer({s: clamp(s, sp.Rational(rng.randint(0, 64 * 8), rng.randint(1, 8)))
               for s in syms})
    offer({s: clamp(s, sp.Integer(0)) for s in syms})
    for _ in range(iters):
        _, parent = archive[rng.choice(list(archive))]
        offer(_mutate(parent, syms, rng, clamp))
    ranked = sorted(archive.values(), key=lambda t: t[0])[:top]
    return [
        HuntResult(
            minimum=v,
            argmin={str(k): x for k, x in p.items()},
            evaluations=evals,
        )
        for v, p in ranked
    ]
