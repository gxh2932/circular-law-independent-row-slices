import CircularLaw.ColumnAdditionSingularProducts

/-!
# The column-insertion logarithmic exposure step

The actual ordered log sums are preserved by taking the adjoint.
The large-singular-value and projection branches therefore give the
column-step logarithmic increment. The left projection has the checked
dimension and near-kernel bound inherited from the row-kernel geometry.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators

namespace CircularLaw

def insertedColumnLeadingLogPrefix {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hNext : r + 1 ≤ n) (c : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ j : Fin (r + 1), -Real.log (orderedMatrixSingularValues (hybridInsertedColumns A c)
    (leadingSingularIndex hNext j))

theorem inserted_column_log_prefix_eq_adjoint_row_prefix {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (c : EuclideanSpace ℂ (Fin n)) :
    insertedColumnLeadingLogPrefix A hNext c =
      insertedLeadingLogPrefix A.conjTranspose hCol (rowAdjointVector c) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [← hybrid_inserted_columns_conjTranspose,
    ordered_matrix_singular_values_conjTranspose (hybridInsertedColumns A c)
      (leadingSingularIndex hNext j) (insertedLeadingSingularIndex hCol j) rfl]

theorem column_addition_normalized_log_increment_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (c : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {N δ : ℝ} (hN : 0 < N)
    (hProjection : Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection c‖) :
    insertedColumnLeadingLogPrefix A hNext c / N ≤ leadingRowLogPrefix A hRow / N + δ := by
  rw [inserted_column_log_prefix_eq_adjoint_row_prefix A hCol hNext c,
    leading_row_log_prefix_conjTranspose A hRow hCol]
  apply row_addition_normalized_log_increment_of_projection A.conjTranspose hCol
    (rowAdjointVector c) (by rwa [← leading_row_singular_product_conjTranspose A hRow hCol]) hN
  simpa only [row_adjoint_vector_involutive] using hProjection

theorem column_addition_normalized_log_increment_of_next_singular_value {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m)
    (hNextRow : r + 1 ≤ n) (hNextCol : r + 1 ≤ m)
    (c : EuclideanSpace ℂ (Fin n)) (hOld : 0 < leadingRowSingularProduct A hRow)
    {N δ : ℝ} (hN : 0 < N)
    (hThreshold : Real.exp (-N * δ) ≤ orderedMatrixSingularValues A
      ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    insertedColumnLeadingLogPrefix A hNextRow c / N ≤ leadingRowLogPrefix A hRow / N + δ := by
  rw [inserted_column_log_prefix_eq_adjoint_row_prefix A hCol hNextRow c,
    leading_row_log_prefix_conjTranspose A hRow hCol]
  apply row_addition_normalized_log_increment_of_next_singular_value A.conjTranspose hCol hNextCol
    (rowAdjointVector c) (by rwa [← leading_row_singular_product_conjTranspose A hRow hCol]) hN
  rwa [← ordered_matrix_singular_values_conjTranspose A
    ⟨r, by simp only [Fintype.card_fin]; omega⟩
    ⟨r, by simp only [Fintype.card_fin]; omega⟩ rfl]

theorem column_addition_log_failure_probability_le_projection_small
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m)
    (hNext : r + 1 ≤ n) (X : Ω → EuclideanSpace ℂ (Fin n))
    (hOld : 0 < leadingRowSingularProduct A hRow) {N δ : ℝ} (hN : 0 < N) :
    μ.real {ω | leadingRowLogPrefix A hRow / N + δ < insertedColumnLeadingLogPrefix A hNext (X ω) / N} ≤
      μ.real {ω | ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection
        (X ω)‖ < Real.exp (-N * δ)} := by
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hFailure
  by_contra hNotSmall
  exact not_lt_of_ge (column_addition_normalized_log_increment_of_projection A hRow hCol hNext
    (X ω) hOld hN (le_of_not_gt hNotSmall)) hFailure

theorem column_leading_kernel_dimension {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m)
    (hProd : leadingRowSingularProduct A hRow ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) = n - r := by
  apply leading_row_kernel_dimension
  rwa [← leading_row_singular_product_conjTranspose A hRow hCol]

theorem column_leading_kernel_near_kernel_bound {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hCol : r ≤ m) (hrRow : r < n) (hrCol : r < m)
    (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin) :
    ‖A.conjTranspose.toEuclideanLin v‖ ≤
      orderedMatrixSingularValues A ⟨r, by simpa only [Fintype.card_fin] using hrRow⟩ * ‖v‖ := by
  have hBound := leading_row_kernel_near_kernel_bound A.conjTranspose hCol hrCol v hv
  rwa [← ordered_matrix_singular_values_conjTranspose A
    ⟨r, by simpa only [Fintype.card_fin] using hrRow⟩
    ⟨r, by simpa only [Fintype.card_fin] using hrCol⟩ rfl] at hBound

end CircularLaw
