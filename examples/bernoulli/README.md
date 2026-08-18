# Bernoulli's inequality — a non-BG genericity example

This example proves the integer form of **Bernoulli's inequality** —
`(1 + x)^k - 1 - k*x ≥ 0` for integer `k ≥ 1` and real `x ≥ 0` — over the grid
`k ∈ {1,2,3,4,5,6}`, driven end to end through the enforced telperion pipeline
(`certify → validate → emit → freeze`) using **only** the general `telperion`
core (`DirectPolyaEmitter`); it never imports `telperion.bg`. The expansion
`(1+x)^k = Σ C(k,j) x^j` has its degree-0 and degree-1 terms cancel against the
subtracted `1 + k*x`, leaving `Σ_{j≥2} C(k,j) x^j` — a polynomial with
all-nonnegative integer (binomial) coefficients and denominator 1, i.e. a Polya
certificate closed in Lean by `positivity`. It matters because it demonstrates
**genericity**: a textbook inequality with nothing to do with Brualdi–Goldwasser
flows through the same certify/emit/freeze machinery and the same enforcement
gates as the research lab, rebutting the criticism that the "reusable" emitters
were only ever exercised on one problem. (Per the trust model, in-session
evidence is Python-green certification/validation plus a byte-stable freeze; the
emitted Lean is verified by the kernel in CI only.)
