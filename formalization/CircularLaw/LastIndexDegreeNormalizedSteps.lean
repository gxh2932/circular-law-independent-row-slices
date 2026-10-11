import CircularLaw.LastIndexMatrixInsertion
import CircularLaw.NormalizedInsertionLogIncrement

/-!
# Degree-normalized steps for the literal last row and column

The checked normalized insertion steps apply to the manuscript's actual
last-index matrix views. New-product positivity is retained. Keeping the
same rank preserves positivity and cannot increase the normalized prefix.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem last_row_vector_smul {n m : ℕ} (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (c : ℂ) :
    lastRowVector (c • B) = c • lastRowVector B := by
  ext j
  rfl

theorem last_column_vector_smul {n m : ℕ} (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (c : ℂ) :
    lastColumnVector (c • B) = c • lastColumnVector B := by
  ext j
  rfl

theorem last_row_leading_singular_product {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1) :
    leadingRowSingularProduct B hNew =
      insertedLeadingSingularProduct (B.submatrix Fin.castSucc id) hOld (lastRowVector B) := by
  apply Finset.prod_congr rfl
  intro j _
  have hSing := ordered_matrix_singular_values_reindex B (insertedIndexToLast n).symm (Equiv.refl (Fin m))
    (leadingSingularIndex hNew j) (insertedLeadingSingularIndex hOld j) rfl
  rw [last_row_matrix_decomposition] at hSing
  exact hSing

theorem last_column_leading_singular_product {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hNew : r + 1 ≤ n) :
    leadingRowSingularProduct B hNew =
      insertedColumnLeadingSingularProduct (B.submatrix id Fin.castSucc) hNew (lastColumnVector B) := by
  apply Finset.prod_congr rfl
  intro j _
  have hSing := ordered_matrix_singular_values_reindex B (Equiv.refl (Fin n)) (insertedIndexToLast m).symm
    (leadingSingularIndex hNew j) (leadingSingularIndex hNew j) rfl
  rw [last_column_matrix_decomposition] at hSing
  exact hSing

theorem last_row_degree_normalized_log_prefix {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1) (d : ℝ) :
    degreeNormalizedLeadingLogPrefix d B hNew =
      degreeNormalizedInsertedRowLogPrefix d (B.submatrix Fin.castSucc id) hOld (lastRowVector B) := by
  unfold degreeNormalizedLeadingLogPrefix degreeNormalizedInsertedRowLogPrefix
  rw [last_row_leading_log_prefix _ hOld hNew, Matrix.submatrix_smul, last_row_vector_smul]
  rfl

theorem last_column_degree_normalized_log_prefix {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hNew : r + 1 ≤ n) (d : ℝ) :
    degreeNormalizedLeadingLogPrefix d B hNew =
      degreeNormalizedInsertedColumnLogPrefix d (B.submatrix id Fin.castSucc) hNew (lastColumnVector B) := by
  unfold degreeNormalizedLeadingLogPrefix degreeNormalizedInsertedColumnLogPrefix
  rw [last_column_leading_log_prefix _ hNew, Matrix.submatrix_smul, last_column_vector_smul]
  rfl

theorem last_row_degree_normalized_success_of_projection {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hProjection : Real.sqrt d * Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows (B.submatrix Fin.castSucc id) hOld).toEuclideanLin).starProjection
        (rowAdjointVector (lastRowVector B))‖) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew ∧
      degreeNormalizedLeadingLogPrefix d B hNew / N ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix Fin.castSucc id) hOld / N + δ := by
  have hSuccess := row_addition_degree_normalized_success_of_projection
    (B.submatrix Fin.castSucc id) hOld (lastRowVector B) hProd hd hN hProjection
  rw [last_row_leading_singular_product _ hOld hNew, Matrix.submatrix_smul, last_row_vector_smul,
    last_row_degree_normalized_log_prefix B hOld hNew]
  exact hSuccess

theorem last_column_degree_normalized_success_of_projection {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hOldRow : r ≤ n) (hOldCol : r ≤ m) (hNew : r + 1 ≤ n)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix id Fin.castSucc) hOldRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hProjection : Real.sqrt d * Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows (B.submatrix id Fin.castSucc).conjTranspose hOldCol).toEuclideanLin).starProjection
        (lastColumnVector B)‖) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew ∧
      degreeNormalizedLeadingLogPrefix d B hNew / N ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix id Fin.castSucc) hOldRow / N + δ := by
  have hSuccess := column_addition_degree_normalized_success_of_projection
    (B.submatrix id Fin.castSucc) hOldRow hOldCol hNew (lastColumnVector B) hProd hd hN hProjection
  rw [last_column_leading_singular_product _ hNew, Matrix.submatrix_smul, last_column_vector_smul,
    last_column_degree_normalized_log_prefix B hNew]
  exact hSuccess

theorem last_row_degree_normalized_success_of_next_singular_value {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNext : r + 1 ≤ n) (hNew : r + 1 ≤ n + 1)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues
      (B.submatrix Fin.castSucc id) ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew ∧
      degreeNormalizedLeadingLogPrefix d B hNew / N ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix Fin.castSucc id) hOld / N + δ := by
  have hSuccess := row_addition_degree_normalized_success_of_next_singular_value
    (B.submatrix Fin.castSucc id) hOld hNext (lastRowVector B) hProd hd hN hThreshold
  rw [last_row_leading_singular_product _ hOld hNew, Matrix.submatrix_smul, last_row_vector_smul,
    last_row_degree_normalized_log_prefix B hOld hNew]
  exact hSuccess

theorem last_column_degree_normalized_success_of_next_singular_value {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hOldRow : r ≤ n) (hOldCol : r ≤ m)
    (hNew : r + 1 ≤ n) (hNextCol : r + 1 ≤ m)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix id Fin.castSucc) hOldRow)
    {d N δ : ℝ} (hd : 0 < d) (hN : 0 < N)
    (hThreshold : Real.sqrt d * Real.exp (-N * δ) ≤ orderedMatrixSingularValues
      (B.submatrix id Fin.castSucc) ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew ∧
      degreeNormalizedLeadingLogPrefix d B hNew / N ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix id Fin.castSucc) hOldRow / N + δ := by
  have hSuccess := column_addition_degree_normalized_success_of_next_singular_value
    (B.submatrix id Fin.castSucc) hOldRow hOldCol hNew hNextCol (lastColumnVector B) hProd hd hN hThreshold
  rw [last_column_leading_singular_product _ hNew, Matrix.submatrix_smul, last_column_vector_smul,
    last_column_degree_normalized_log_prefix B hNew]
  exact hSuccess

theorem last_row_degree_normalized_same_rank_success {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r ≤ n + 1)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld)
    {d : ℝ} (hd : 0 < d) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) hNew ∧
      degreeNormalizedLeadingLogPrefix d B hNew ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix Fin.castSucc id) hOld := by
  have hOldNorm : 0 < leadingRowSingularProduct ((degreeNormalizingScalar d • B).submatrix Fin.castSucc id) hOld := by
    rw [Matrix.submatrix_smul]
    exact (leading_row_singular_product_degree_normalization_pos_iff _ hOld hd).mpr hProd
  refine ⟨hOldNorm.trans_le (last_row_same_prefix_product_le _ hOld hNew), ?_⟩
  have hLog := last_row_same_prefix_log_le (degreeNormalizingScalar d • B) hOld hNew hOldNorm
  simpa only [degreeNormalizedLeadingLogPrefix, Matrix.submatrix_smul] using hLog

theorem last_column_degree_normalized_same_rank_success {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (h : r ≤ n)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix id Fin.castSucc) h)
    {d : ℝ} (hd : 0 < d) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • B) h ∧
      degreeNormalizedLeadingLogPrefix d B h ≤
        degreeNormalizedLeadingLogPrefix d (B.submatrix id Fin.castSucc) h := by
  have hOldNorm : 0 < leadingRowSingularProduct ((degreeNormalizingScalar d • B).submatrix id Fin.castSucc) h := by
    rw [Matrix.submatrix_smul]
    exact (leading_row_singular_product_degree_normalization_pos_iff _ h hd).mpr hProd
  refine ⟨hOldNorm.trans_le (last_column_same_prefix_product_le _ h), ?_⟩
  have hLog := last_column_same_prefix_log_le (degreeNormalizingScalar d • B) h hOldNorm
  simpa only [degreeNormalizedLeadingLogPrefix, Matrix.submatrix_smul] using hLog

end CircularLaw
