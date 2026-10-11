import CircularLaw.HeavyRowsFromColumnDegree

/-!
# Restriction of the graph degree budgets

Deleting rows and columns preserves the actual column-degree budget with
the ambient size and degree unchanged. Unit-bounded entries then supply
the same heavy-row budget for every restriction.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem matrix_restricted_column_support_card_le {ρ ι σ τ : Type*}
    [Fintype ρ] [Fintype σ] (A : Matrix ρ ι ℂ)
    (r : σ ↪ ρ) (c : τ → ι) (j : τ) :
    (matrixColumnSupport (A.submatrix r c) j).card ≤ (matrixColumnSupport A (c j)).card := by
  have hSubset : (matrixColumnSupport (A.submatrix r c) j).image r ⊆
      matrixColumnSupport A (c j) := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (matrix_column_support_mem A (c j) (r a)).mpr
      ((matrix_column_support_mem (A.submatrix r c) j a).mp ha)
  calc
    _ = ((matrixColumnSupport (A.submatrix r c) j).image r).card :=
      (Finset.card_image_of_injective _ r.injective).symm
    _ ≤ _ := Finset.card_le_card hSubset

theorem matrix_column_degree_budget_restrict {ρ ι σ τ : Type*}
    [Fintype ρ] [Fintype σ] (A : Matrix ρ ι ℂ)
    (r : σ ↪ ρ) (c : τ ↪ ι) {K n d : ℝ}
    (hA : MatrixColumnDegreeBudget A K n d) :
    MatrixColumnDegreeBudget (A.submatrix r c) K n d := by
  intro T
  calc
    _ ≤ ∑ j ∈ T, ((matrixColumnSupport A (c j)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast matrix_restricted_column_support_card_le A r c j
    _ = ∑ j ∈ T.map c, ((matrixColumnSupport A j).card : ℝ) :=
      (Finset.sum_map T c (fun j => ((matrixColumnSupport A j).card : ℝ))).symm
    _ ≤ _ := hA (T.map c)
    _ = _ := by rw [Finset.card_map]

theorem matrix_graph_degree_budgets_restrict {ρ ι σ τ : Type*}
    [Fintype ρ] [Fintype ι] [Fintype σ] [Fintype τ]
    (A : Matrix ρ ι ℂ) (r : σ ↪ ρ) (c : τ ↪ ι) {K n d β : ℝ}
    (hK : 0 ≤ K) (hn : 0 < n) (hd : 1 ≤ d) (hDegree : 4 * K ≤ d)
    (hCols : (Fintype.card ι : ℝ) ≤ n) (hNorm : ∀ i j, ‖A i j‖ ≤ 1)
    (hβ : 0 < β) (hβOne : β ≤ 1) (hA : MatrixColumnDegreeBudget A K n d) :
    MatrixColumnDegreeBudget (A.submatrix r c) K n d ∧
      MatrixHeavyRowBudget (A.submatrix r c) β n d := by
  have hColumn := matrix_column_degree_budget_restrict A r c hA
  refine ⟨hColumn, matrix_heavy_row_budget_of_column_degree (A.submatrix r c)
    hK hn hd hDegree ?_ (fun i j => hNorm (r i) (c j)) hβ hβOne hColumn⟩
  have hCard : Fintype.card τ ≤ Fintype.card ι := Fintype.card_le_of_injective c c.injective
  exact (by exact_mod_cast hCard : (Fintype.card τ : ℝ) ≤ Fintype.card ι).trans hCols

end CircularLaw
