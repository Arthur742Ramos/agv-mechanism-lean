module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace AGV

/-!
# AGV (expected-externality) mechanism — definitions module.

M1 will define here: finite agent set `Fin n` (n ≥ 2), finite nonempty type
sets `T i` with independent priors (PMFs), a finite nonempty alternative set
`X`, private values `v i : X → T i → ℝ`, the efficient decision rule
`x* : (∀ i, T i) → X`, and the AGV transfers

  p i t̂ = E_{t_{-i}}[Σ_{j≠i} v j (x* (t̂_i, t_{-i})) (t_j)]
          − (1/(n−1)) · Σ_{j≠i} E_{t_{-j}}[Σ_{k≠j} v k (x* (t̂_j, t_{-j})) (t_k)],

together with the statements: ex post efficiency, Bayesian incentive
compatibility, and ex post budget balance.
-/

end AGV
