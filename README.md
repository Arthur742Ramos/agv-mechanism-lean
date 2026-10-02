# AGV Expected-Externality Mechanism in Lean 4

Lean 4 / Mathlib formalization of the AGV (d'Aspremont–Gérard-Varet–Arrow)
expected-externality mechanism: with independent types, ex post efficiency,
Bayesian incentive compatibility, and budget balance are jointly attainable —
the possibility flip side of the Myerson–Satterthwaite impossibility theorem.

## Setting

All declarations live in namespace `AGV`, over implicit `{n : Nat}`,
`{T : Fin n → Type}`, `{X : Type}` with
`[Fintype X] [Nonempty X] [DecidableEq X]` and
`[∀ i, Fintype (T i)] [∀ i, Nonempty (T i)] [∀ i, DecidableEq (T i)]`,
for values `v : (i : Fin n) → X → T i → ℝ` and independent priors
`π : (i : Fin n) → PMF (T i)`. The capstone theorems all assume `2 ≤ n`.

## Definitions (`AGV/Defs.lean`)

- `welfare v t x = ∑ i, v i x (t i)` — utilitarian welfare at profile `t`.
- `xmax v t` — an alternative maximizing `welfare v t` (via `Classical.choice`
  on the nonempty argmax; `X` is finite).
- `weight π t = ∏ i, ((π i (t i)).toNNReal : ℝ)` — product-prior weight of `t`.
- `splice i r t` — the profile `t` with agent `i`'s component replaced by `r`.
- `extReceipt v π i r` — agent `i`'s expected externality for report `r`:
  `∑ t, weight π t * ∑ j ∈ Finset.univ.erase i, v j (xmax v (splice i r t)) (t j)`.
- `agvTransfer v π i t` — the transfer to agent `i` at report profile `t`:
  `extReceipt v π i (t i) − (1 / ((n : ℝ) − 1)) * ∑ j ∈ Finset.univ.erase i, extReceipt v π j (t j)`.
- `interimUtil x p i s r` — interim expected utility of agent `i` with true
  type `s` reporting `r` while others report truthfully:
  `∑ t, weight π t * (v i (x (splice i r t)) s + p i (splice i r t))`.
- `IsEfficient v x := ∀ t y, welfare v t y ≤ welfare v t (x t)`.
- `IsBudgetBalanced p := ∀ t, ∑ i, p i t = 0`.
- `IsBIC v π x p := ∀ i (s r : T i), interimUtil v π x p i s r ≤ interimUtil v π x p i s s`.

## Theorems

- `AGV.agv_efficient : 2 ≤ n → IsEfficient v (xmax v)` — the argmax rule is
  ex post efficient. (Needs no prior `π`.)
- `AGV.agv_bic : 2 ≤ n → IsBIC v π (xmax v) (agvTransfer v π)` — truth-telling
  maximizes interim utility. The redistribution term is independent of `i`'s
  own report, so interim utility equals expected true welfare plus a constant;
  `xmax_optimal` then gives the pointwise maximum at truthful reporting.
- `AGV.agv_budget_balanced : 2 ≤ n → IsBudgetBalanced (agvTransfer v π)` —
  each receipt is counted `n − 1` times, so transfers sum to zero at every
  report profile.
- `AGV.agv_theorem : 2 ≤ n → IsEfficient v (xmax v) ∧ IsBIC v π (xmax v) (agvTransfer v π) ∧ IsBudgetBalanced (agvTransfer v π)` —
  the capstone conjunction.

Interim individual rationality is **not** claimed — that is exactly the
Myerson–Satterthwaite point. The axiom audit of every declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`. The library contains no
`sorry`.

## Proof development

The proofs were developed with AI assistance and then independently compiled,
audited for placeholders and axioms, and comparator-checked; no separate
independent human review of the proofs was performed.

## References

- Claude d'Aspremont and Louis-André Gérard-Varet, "Incentives and
  incomplete information," *Journal of Public Economics* 11(1), 25–45, 1979.
- Kenneth J. Arrow (1979), Bayesian demand revelation (the "dAGVA" naming).
- Textbook formulation: d'Aspremont, "On Bayesian Incentive Compatible
  Mechanisms," with transfers `t_i(a) = g_i(a_i) − g_{−i}(a_{−i})`,
  `g_i(a_i) = E[Σ_{j≠i} U_j(d(a_i,α_{−i}), α_j)]`,
  `g_{−i}(a_{−i}) = (1/(n−1))·Σ_{j≠i} g_j(a_j)`.

## Prior art

Palomar registry search performed 2026-10-02 for "agv", "dagva",
"externality mechanism", "gerard-varet", "expected externality": zero
results. This records only that dated registry search.

## Status

Complete through M7. Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib pinned
to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Build green, official
`lake comparator` check passes.

Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. License: BSD-3-Clause.
