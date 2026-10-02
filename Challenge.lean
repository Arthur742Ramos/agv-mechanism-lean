module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
Compact comparison surface for the AGV expected-externality mechanism.
All definitions below are genuine, with their exact library bodies, copied
verbatim (including the variable binders) so that declaration types match
the library syntactically.
Only the four comparator-selected theorem proofs are deliberate statement holes.
The complete, mechanically checked proofs are in the AGV library imported by
Solution. The proofs were developed with AI assistance and then independently
compiled, audited for placeholders and axioms, and comparator-checked; no
separate independent human review of the proofs was performed.
The official comparator checks their exact contracts.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace AGV

/-!
# AGV (expected-externality) mechanism — definitions module.

The mechanism has a finite agent set `Fin n` (n ≥ 2), finite nonempty type
sets `T i` with independent priors (PMFs), a finite nonempty alternative set
`X`, private values `v i : X → T i → ℝ`, the efficient decision rule
`x* : (∀ i, T i) → X`, and the AGV transfers

  p i t̂ = E_{t_{-i}}[Σ_{j≠i} v j (x* (t̂_i, t_{-i})) (t_j)]
          − (1/(n−1)) · Σ_{j≠i} E_{t_{-j}}[Σ_{k≠j} v k (x* (t̂_j, t_{-j})) (t_k)],

together with the statements: ex post efficiency, Bayesian incentive
compatibility, and ex post budget balance.
-/

open scoped BigOperators NNReal

noncomputable section

variable {n : Nat} {T : Fin n → Type} {X : Type}
  [Fintype X] [Nonempty X] [DecidableEq X]
  [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)] [∀ i, DecidableEq (T i)]
  (v : (i : Fin n) → X → T i → ℝ) (π : (i : Fin n) → PMF (T i))

/-- Total welfare at a type profile and an alternative. -/
def welfare (t : (i : Fin n) → T i) (x : X) : ℝ :=
  ∑ i, v i x (t i)

/-- Welfare attains a maximum on the finite nonempty alternative set. -/
theorem argmax_nonempty : ∀ t : (i : Fin n) → T i,
    ∃ x : X, ∀ y : X, welfare v t y ≤ welfare v t x := by
  intro t
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image
    (Finset.univ : Finset X) (welfare v t)
    ⟨Classical.choice (inferInstance : Nonempty X), Finset.mem_univ _⟩
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

/-- An ex post efficient alternative, chosen from the subtype of welfare maximizers. -/
noncomputable def xmax (t : (i : Fin n) → T i) : X :=
  (Classical.choice (show Nonempty {x : X // ∀ y : X, welfare v t y ≤ welfare v t x} from by
    obtain ⟨x, hx⟩ := argmax_nonempty v t
    exact ⟨⟨x, hx⟩⟩)).val

/-- Every alternative has welfare at most that of the efficient alternative. -/
theorem xmax_optimal (t : (i : Fin n) → T i) (x : X) :
    welfare v t x ≤ welfare v t (xmax v t) := by
  have hmax : Nonempty {y : X // ∀ z : X, welfare v t z ≤ welfare v t y} := by
    obtain ⟨y, hy⟩ := argmax_nonempty v t
    exact ⟨⟨y, hy⟩⟩
  exact (Classical.choice hmax).property x

/-- Joint probability weight under independent priors.
Mathlib PMFs take values in `ℝ≥0∞`; their finite masses are converted through `ℝ≥0`.
-/
def weight (t : (i : Fin n) → T i) : ℝ :=
  ∏ i, (((π i (t i)).toNNReal : ℝ≥0) : ℝ)

/-- Replace one component of a full type profile. -/
def splice (i : Fin n) (a : T i) (t : (j : Fin n) → T j) : (j : Fin n) → T j :=
  Function.update t i a

/-- Expected total value of the other agents under the efficient rule at the spliced profile.
The sum runs over full profiles. The summand apart from the weight is independent of
the original component `t i`, whose marginal probability sums to one.
-/
def extReceipt (i : Fin n) (r : T i) : ℝ :=
  ∑ t : (j : Fin n) → T j, weight π t *
    ∑ j ∈ Finset.univ.erase i, v j (xmax v (splice i r t)) (t j)

/-- Transfer to an agent: its expected-externality receipt minus an equal share
of the receipts of the other agents. Positive transfers are received by the agent.
-/
def agvTransfer (i : Fin n) (t : (j : Fin n) → T j) : ℝ :=
  extReceipt v π i (t i) - (1 / ((n : ℝ) - 1)) *
    ∑ j ∈ Finset.univ.erase i, extReceipt v π j (t j)

/-- Interim utility for true type `s` and report `r`, with others truthful.
For the AGV mechanism, specialize `x` to `xmax v` and `p` to `agvTransfer v π`.
-/
def interimUtil (x : ((j : Fin n) → T j) → X)
    (p : (i : Fin n) → ((j : Fin n) → T j) → ℝ)
    (i : Fin n) (s r : T i) : ℝ :=
  ∑ t : (j : Fin n) → T j, weight π t *
    (v i (x (splice i r t)) s + p i (splice i r t))

/-- The allocation maximizes welfare at every type profile. -/
def IsEfficient (x : ((j : Fin n) → T j) → X) : Prop :=
  ∀ t y, welfare v t y ≤ welfare v t (x t)

/-- Transfers sum to zero at every report profile. -/
def IsBudgetBalanced (p : (i : Fin n) → ((j : Fin n) → T j) → ℝ) : Prop :=
  ∀ t, ∑ i, p i t = 0

/-- Truthful reporting maximizes interim expected utility for every own type. -/
def IsBIC (x : ((j : Fin n) → T j) → X)
    (p : (i : Fin n) → ((j : Fin n) → T j) → ℝ) : Prop :=
  ∀ i (s r : T i), interimUtil v π x p i s r ≤ interimUtil v π x p i s s

/-- Each prior has total real-valued probability mass one. -/
theorem pmf_sum_one (i : Fin n) :
    (∑ t : T i, (((π i t).toNNReal : ℝ≥0) : ℝ)) = 1 := by
  have hsum : (∑ t : T i, π i t) = 1 :=
    (tsum_eq_sum (s := Finset.univ)
      (fun t ht => absurd (Finset.mem_univ t) ht)).symm.trans (π i).tsum_coe
  change (∑ t : T i, (π i t).toReal) = 1
  rw [← ENNReal.toReal_sum (fun t _ => (π i).apply_ne_top t), hsum,
    ENNReal.toReal_one]

/-- The AGV allocation is ex post efficient. -/

theorem agv_efficient (hn : 2 ≤ n) : IsEfficient v (xmax v) := by
  sorry

theorem agv_bic (hn : 2 ≤ n) : IsBIC v π (xmax v) (agvTransfer v π) := by
  sorry

theorem agv_budget_balanced (hn : 2 ≤ n) : IsBudgetBalanced (agvTransfer v π) := by
  sorry

theorem agv_theorem (hn : 2 ≤ n) :
    IsEfficient v (xmax v) ∧ IsBIC v π (xmax v) (agvTransfer v π) ∧
      IsBudgetBalanced (agvTransfer v π) := by
  sorry

end

end AGV
