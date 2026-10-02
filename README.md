# AGV Expected-Externality Mechanism in Lean 4

Lean 4 / Mathlib formalization of the AGV (d'Aspremont–Gérard-Varet–Arrow)
expected-externality mechanism: with independent types, ex post efficiency,
Bayesian incentive compatibility, and budget balance are jointly attainable —
the possibility flip side of the Myerson–Satterthwaite impossibility theorem.

## M0 research note (2026-10-02)

### Setting (finite version)

- `n ≥ 2` agents, indexed by `Fin n`.
- Each agent `i` has a finite nonempty type set `T i`, with independent priors
  given by PMFs `π i` on `T i`.
- A finite nonempty set `X` of alternatives.
- Private values `v i : X → T i → ℝ`.

### The AGV mechanism

- **Decision rule.** `x* : (∀ i, T i) → X` with
  `x* t ∈ argmax_{x ∈ X} Σ_i v i x (t i)` (ex post efficient; the argmax is
  nonempty since `X` is finite).
- **Transfers.** For a report profile `t̂`,
  `p i t̂ = E_{t_{-i}∼π_{-i}}[Σ_{j≠i} v j (x* (t̂_i, t_{-i})) (t_j)]`
  `        − (1/(n−1)) · Σ_{j≠i} E_{t_{-j}∼π_{-j}}[Σ_{k≠j} v k (x* (t̂_j, t_{-j})) (t_k)]`.
  The first term is `i`'s expected externality: the expected welfare of the
  other agents given `i`'s report. The second term redistributes the other
  agents' receipts back, `1/(n−1)` each, which balances the budget.

### Theorem (d'Aspremont–Gérard-Varet 1979; Arrow 1979)

`(x*, p)` is ex post efficient, Bayesian incentive compatible, and ex post
budget balanced (`Σ_i p i t̂ = 0` for every report profile `t̂`).

### Proof ideas (for the Lean development)

- **Budget balance.** `Σ_i p i t̂ = Σ_j E_j − (1/(n−1))·(n−1)·Σ_j E_j = 0`,
  where `E_j` is agent `j`'s expected-externality receipt. Pure algebra.
- **BIC.** Fix agent `i` with true type `t_i`; others report truthfully.
  The redistribution term is independent of `i`'s report `t̂_i`, so `i`'s
  interim expected utility is
  `E_{t_{-i}}[v i (x* (t̂_i, t_{-i})) (t_i) + Σ_{j≠i} v j (x* (t̂_i, t_{-i})) (t_j)]`
  plus a constant. For each `t_{-i}`, `x* (t̂_i, t_{-i})` maximizes
  `Σ_j v j x (t̂_j)`; at `t̂_i = t_i` this objective coincides with `i`'s true
  payoff, so truth-telling attains the pointwise maximum. Independence is
  used so that `i`'s belief about `t_{-i}` is `π_{-i}` regardless of `t_i`.
- Interim individual rationality is **not** claimed — that is exactly the
  Myerson–Satterthwaite point.

### References

- Claude d'Aspremont and Louis-André Gérard-Varet, "Incentives and
  incomplete information," *Journal of Public Economics* 11(1), 25–45, 1979.
- Kenneth J. Arrow (1979), Bayesian demand revelation (the "dAGVA" naming).
- Textbook formulation: d'Aspremont, "On Bayesian Incentive Compatible
  Mechanisms," with transfers `t_i(a) = g_i(a_i) − g_{−i}(a_{−i})`,
  `g_i(a_i) = E[Σ_{j≠i} U_j(d(a_i,α_{−i}), α_j)]`,
  `g_{−i}(a_{−i}) = (1/(n−1))·Σ_{j≠i} g_j(a_j)`.

### Prior art

Palomar registry search performed 2026-10-02 for "agv", "dagva",
"externality mechanism", "gerard-varet", "expected externality": zero
results. This records only that dated registry search.

## Status

M0 scaffold. Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Module system from day one.

Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. License: BSD-3-Clause.
