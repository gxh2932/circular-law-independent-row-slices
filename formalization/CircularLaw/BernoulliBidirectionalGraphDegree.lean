import CircularLaw.BernoulliAdjointLaw
import CircularLaw.BernoulliGraphDegreeProbability

/-!
# One graph degree event for both insertion directions

Both the actual matrix and its adjoint satisfy the column-degree and
heavy-row budgets in every injective restriction, outside an event of
probability at most 2*N^(-3). This supplies both directions required by
the alternating exposure construction.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def AllRestrictedGraphDegreeBudgets {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (K n d β : ℝ) : Prop :=
  ∀ (m k : ℕ) (r : Fin m ↪ Fin N) (c : Fin k ↪ Fin N),
    MatrixColumnDegreeBudget (A.submatrix r c) K n d ∧
      MatrixHeavyRowBudget (A.submatrix r c) β n d

def BidirectionalGraphDegreeBudgets {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (K n d β : ℝ) : Prop :=
  AllRestrictedGraphDegreeBudgets A K n d β ∧ AllRestrictedGraphDegreeBudgets Aᴴ K n d β

theorem bernoulli_all_restricted_graph_degree_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ}
    (hd : 32 ≤ (N : ℝ) * p) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ AllRestrictedGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) β} ≤
      ((N : ℝ)⁻¹) ^ 3 :=
  bernoulli_square_all_restrictions_graph_degree_budgets_failure hN p hp hd hβ hβOne

theorem bernoulli_adjoint_restricted_graph_degree_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ}
    (hd : 32 ≤ (N : ℝ) * p) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ AllRestrictedGraphDegreeBudgets (bernoulliSquareMatrix x)ᴴ 8 N ((N : ℝ) * p) β} ≤
      ((N : ℝ)⁻¹) ^ 3 := by
  rw [bernoulli_square_adjoint_event_probability p hp
    (fun A => ¬ AllRestrictedGraphDegreeBudgets A 8 N ((N : ℝ) * p) β)]
  exact bernoulli_all_restricted_graph_degree_failure hN p hp hd hβ hβOne

theorem bernoulli_bidirectional_graph_degree_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ}
    (hd : 32 ≤ (N : ℝ) * p) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ BidirectionalGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) β} ≤
      2 * ((N : ℝ)⁻¹) ^ 3 := by
  have hEvent : {x : BernoulliSquareSample N |
      ¬ BidirectionalGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) β} =
      {x | ¬ AllRestrictedGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) β} ∪
      {x | ¬ AllRestrictedGraphDegreeBudgets (bernoulliSquareMatrix x)ᴴ 8 N ((N : ℝ) * p) β} := by
    ext x
    simp only [BidirectionalGraphDegreeBudgets, Set.mem_setOf_eq, Set.mem_union, not_and_or]
  rw [hEvent]
  exact (measureReal_union_le _ _).trans (by
    have hA := bernoulli_all_restricted_graph_degree_failure hN p hp hd hβ hβOne
    have hAdj := bernoulli_adjoint_restricted_graph_degree_failure hN p hp hd hβ hβOne
    linarith)

theorem sparse_bernoulli_bidirectional_graph_degree_failure {N d : ℕ}
    (hN : 0 < N) (hd : 32 ≤ d) (hdN : d ≤ N) {β : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (sparseBernoulliMatrixLaw N d).real {x |
      ¬ BidirectionalGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N d β} ≤
      2 * ((N : ℝ)⁻¹) ^ 3 := by
  rw [sparseBernoulliMatrixLaw_eq hN hdN]
  have hDegree : (d : ℝ) = (N : ℝ) * rowBernoulliParameter N d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  rw [hDegree]
  exact bernoulli_bidirectional_graph_degree_failure hN _ _
    (by rw [← hDegree]; exact_mod_cast hd) hβ hβOne

end CircularLaw
