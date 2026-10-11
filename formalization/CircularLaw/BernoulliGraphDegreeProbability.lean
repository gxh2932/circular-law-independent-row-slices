import CircularLaw.BernoulliColumnDegreeBudget
import CircularLaw.HeavyRowsFromColumnDegree
import CircularLaw.ColumnDegreeRestriction

/-!
# Actual Bernoulli column-degree and heavy-row probabilities

The source degree range implies both graph budgets outside one event of
probability at most N^(-3). Unique-neighbourhood expansion is a separate
condition and is not asserted by these theorems.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem thirty_two_le_exp_four : (32 : ℝ) ≤ Real.exp 4 := by
  have hBase : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) hBase 4
  rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  norm_num at hPower ⊢
  linarith

theorem bernoulli_rectangular_graph_degree_budgets_failure
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (hRows : Fintype.card ρ ≤ N) (hCols : Fintype.card ι ≤ N)
    {d β : ℝ} (hd : 32 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ¬ (MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d ∧
          MatrixHeavyRowBudget (bernoulliRectangularMatrix x) β N d)} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  have hdOne : 1 ≤ d := by linarith
  have hSubset : {x : ρ × ι → Bool |
      ¬ (MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d ∧
          MatrixHeavyRowBudget (bernoulliRectangularMatrix x) β N d)} ⊆
      {x | ¬ MatrixColumnDegreeBudget (bernoulliRectangularMatrix x) 8 N d} := by
    intro x hx hColumn
    apply hx
    refine ⟨hColumn, matrix_heavy_row_budget_of_column_degree (bernoulliRectangularMatrix x)
      (by norm_num) (by exact_mod_cast hN) hdOne (by linarith)
      (by exact_mod_cast hCols) (bernoulli_rectangular_entry_norm_le_one x) hβ hβOne hColumn⟩
  exact (measureReal_mono hSubset (measure_ne_top _ _)).trans
    (bernoulli_rectangular_column_degree_budget_failure p hp hN hRows hCols hdOne hDegree)

theorem bernoulli_square_graph_degree_budgets_failure {N : ℕ} (hN : 0 < N)
    (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ} (hd : 32 ≤ (N : ℝ) * p)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ (MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) ∧
          MatrixHeavyRowBudget (bernoulliSquareMatrix x) β N ((N : ℝ) * p))} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  simpa only [bernoulliSquareMatrixLaw, bernoulli_rectangular_square_eq] using
    bernoulli_rectangular_graph_degree_budgets_failure p hp hN
      (by simp : Fintype.card (Fin N) ≤ N) (by simp : Fintype.card (Fin N) ≤ N)
      hd rfl hβ hβOne

theorem bernoulli_source_graph_degree_budgets_failure {N : ℕ} (hN : 0 < N)
    (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ} (hd : Real.exp 4 ≤ (N : ℝ) * p)
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ (MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p) ∧
          MatrixHeavyRowBudget (bernoulliSquareMatrix x) β N ((N : ℝ) * p))} ≤ ((N : ℝ)⁻¹) ^ 3 :=
  bernoulli_square_graph_degree_budgets_failure hN p hp (thirty_two_le_exp_four.trans hd) hβ hβOne

theorem sparse_bernoulli_graph_degree_budgets_failure {N d : ℕ}
    (hN : 0 < N) (hd : 32 ≤ d) (hdN : d ≤ N) {β : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (sparseBernoulliMatrixLaw N d).real {x |
      ¬ (MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N d ∧
          MatrixHeavyRowBudget (bernoulliSquareMatrix x) β N d)} ≤ ((N : ℝ)⁻¹) ^ 3 := by
  rw [sparseBernoulliMatrixLaw_eq hN hdN]
  have hDegree : (d : ℝ) = (N : ℝ) * rowBernoulliParameter N d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  rw [hDegree]
  exact bernoulli_square_graph_degree_budgets_failure hN _ _
    (by rw [← hDegree]; exact_mod_cast hd) hβ hβOne

theorem bernoulli_square_all_restrictions_graph_degree_budgets_failure
    {N : ℕ} (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) {β : ℝ}
    (hd : 32 ≤ (N : ℝ) * p) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ ∀ (m k : ℕ) (r : Fin m ↪ Fin N) (c : Fin k ↪ Fin N),
        MatrixColumnDegreeBudget ((bernoulliSquareMatrix x).submatrix r c) 8 N ((N : ℝ) * p) ∧
          MatrixHeavyRowBudget ((bernoulliSquareMatrix x).submatrix r c) β N ((N : ℝ) * p)} ≤
      ((N : ℝ)⁻¹) ^ 3 := by
  have hSubset : {x : BernoulliSquareSample N |
      ¬ ∀ (m k : ℕ) (r : Fin m ↪ Fin N) (c : Fin k ↪ Fin N),
        MatrixColumnDegreeBudget ((bernoulliSquareMatrix x).submatrix r c) 8 N ((N : ℝ) * p) ∧
          MatrixHeavyRowBudget ((bernoulliSquareMatrix x).submatrix r c) β N ((N : ℝ) * p)} ⊆
      {x | ¬ MatrixColumnDegreeBudget (bernoulliSquareMatrix x) 8 N ((N : ℝ) * p)} := by
    intro x hx hColumn
    apply hx
    intro m k r c
    exact matrix_graph_degree_budgets_restrict (bernoulliSquareMatrix x) r c
      (by norm_num) (by exact_mod_cast hN) (by linarith) (by linarith)
      (by simp) (bernoulli_rectangular_entry_norm_le_one x) hβ hβOne hColumn
  exact (measureReal_mono hSubset (measure_ne_top _ _)).trans
    (bernoulli_square_column_degree_budget_failure hN p hp (by linarith))

theorem sparse_bernoulli_all_restrictions_graph_degree_budgets_failure
    {N d : ℕ} (hN : 0 < N) (hd : 32 ≤ d) (hdN : d ≤ N) {β : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    (sparseBernoulliMatrixLaw N d).real {x |
      ¬ ∀ (m k : ℕ) (r : Fin m ↪ Fin N) (c : Fin k ↪ Fin N),
        MatrixColumnDegreeBudget ((bernoulliSquareMatrix x).submatrix r c) 8 N d ∧
          MatrixHeavyRowBudget ((bernoulliSquareMatrix x).submatrix r c) β N d} ≤
      ((N : ℝ)⁻¹) ^ 3 := by
  rw [sparseBernoulliMatrixLaw_eq hN hdN]
  have hDegree : (d : ℝ) = (N : ℝ) * rowBernoulliParameter N d := by
    rw [rowBernoulliParameter_coe]
    field_simp
  rw [hDegree]
  exact bernoulli_square_all_restrictions_graph_degree_budgets_failure hN _ _
    (by rw [← hDegree]; exact_mod_cast hd) hβ hβOne

end CircularLaw
