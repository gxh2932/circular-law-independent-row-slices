import CircularLaw.RowAdditionLogIncrement
import CircularLaw.PrefixNegativeDeviation
import CircularLaw.SquareLogPrefixComparison

/-!
# Identifying the retained row quantities on a square matrix

Both ordered singular-value interfaces use the same decreasing row Gram
eigenvalues. The retained log is the literal finite square-prefix sum,
and its product is positive exactly when that prefix has no zero value.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators NNReal

namespace CircularLaw

theorem leading_row_square_log_prefix_eq_range_sum {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hr : r ≤ n) :
    leadingRowLogPrefix A hr = ∑ j ∈ Finset.range r, squareNegativeLogAt A j := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [squareNegativeLogAt, dif_pos (lt_of_lt_of_le j.isLt hr)]
  rfl

theorem leading_row_square_full_log_prefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    leadingRowLogPrefix A (le_refl n) = -∑ j, Real.log (orderedSquareSingularValues A j) := by
  rw [leading_row_square_log_prefix_eq_range_sum, squareNegativeLogAt_full_sum]

theorem leading_row_square_product_pos_iff_prefix_no_zero {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hr : r ≤ n) :
    0 < leadingRowSingularProduct A hr ↔ ¬ empiricalPrefixHasZero (squareSingularValuesNNReal A) r := by
  constructor
  · intro hPositive hZero
    rcases hZero with ⟨j, hj, hZero⟩
    have hFactor := Finset.prod_ne_zero_iff.mp hPositive.ne' ⟨j.val, hj⟩ (Finset.mem_univ _)
    have hValue := congrArg (fun t : ℝ≥0 => (t : ℝ)) hZero
    change orderedSquareSingularValues A j = 0 at hValue
    exact hFactor hValue
  · intro hNoZero
    apply Finset.prod_pos
    intro j _
    have hNonzero : orderedMatrixSingularValues A (leadingSingularIndex hr j) ≠ 0 := by
      intro hZero
      have hZeroNN : squareSingularValuesNNReal A (Fin.castLE hr j) = 0 := by
        apply Subtype.ext
        exact hZero
      exact hNoZero ⟨Fin.castLE hr j, j.isLt, hZeroNN⟩
    exact lt_of_le_of_ne (ordered_matrix_singular_values_nonneg _ _) (Ne.symm hNonzero)

theorem leading_row_square_product_zero_iff_prefix_zero {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hr : r ≤ n) :
    leadingRowSingularProduct A hr = 0 ↔ empiricalPrefixHasZero (squareSingularValuesNNReal A) r := by
  have hPositive := leading_row_square_product_pos_iff_prefix_no_zero A hr
  constructor
  · intro hProduct
    by_contra hNoZero
    exact (hPositive.mpr hNoZero).ne' hProduct
  · intro hZero
    by_contra hNonzero
    have hPos := lt_of_le_of_ne (leading_row_singular_product_nonneg A hr) (Ne.symm hNonzero)
    exact hPositive.mp hPos hZero

theorem leading_row_square_full_product_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    leadingRowSingularProduct A (le_refl n) = 0 ↔ empiricalHasZero (squareSingularValuesNNReal A) := by
  rw [leading_row_square_product_zero_iff_prefix_zero]
  constructor
  · rintro ⟨j, _, hZero⟩
    exact ⟨j, hZero⟩
  · rintro ⟨j, hZero⟩
    exact ⟨j, j.isLt, hZero⟩

end CircularLaw
