import CircularLaw.LeadingRowKernelGeometry

/-!
# Interlacing branch for the incremental singular product

Deleting the newly inserted row is a coisometry. Hence each old ordered
singular value is at most the corresponding new value. If the next old
singular value exceeds a threshold, the leading product grows by that
threshold without needing a projection estimate.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

def insertedRowDeletion {n : ℕ} : Matrix (Fin n) (Unit ⊕ Fin n) ℂ :=
  Matrix.fromCols 0 1

theorem inserted_row_deletion_coisometry {n : ℕ} :
    insertedRowDeletion (n := n) * (insertedRowDeletion (n := n)).conjTranspose = 1 := by
  simp only [insertedRowDeletion, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    Matrix.zero_mul, Matrix.one_mul, zero_add]

theorem inserted_row_deletion_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (x : EuclideanSpace ℂ (Fin m)) :
    insertedRowDeletion * hybridInsertedRows A x = A := by
  simp only [insertedRowDeletion, hybridInsertedRows, Matrix.fromCols_mul_fromRows,
    Matrix.zero_mul, Matrix.one_mul, zero_add]

theorem inserted_row_singular_value_le {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (x : EuclideanSpace ℂ (Fin m)) (i : Fin (Fintype.card (Fin n)))
    (j : Fin (Fintype.card (Unit ⊕ Fin n))) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues A i ≤ orderedMatrixSingularValues (hybridInsertedRows A x) j := by
  have hBound := orthonormal_row_compression_singular_value_le
    (insertedRowDeletion (n := n)) inserted_row_deletion_coisometry (hybridInsertedRows A x)
    i j hIndex
  rwa [inserted_row_deletion_apply] at hBound

theorem leading_row_singular_product_succ {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hNext : r + 1 ≤ n) :
    leadingRowSingularProduct A hNext = leadingRowSingularProduct A h *
      orderedMatrixSingularValues A ⟨r, by simp only [Fintype.card_fin]; omega⟩ := by
  rw [leadingRowSingularProduct, Fin.prod_univ_castSucc]
  rfl

theorem inserted_row_leading_product_le {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin m)) :
    leadingRowSingularProduct A hNext ≤ insertedLeadingSingularProduct A h x := by
  apply Finset.prod_le_prod
  · intro j _
    exact ordered_matrix_singular_values_nonneg A (leadingSingularIndex hNext j)
  · intro j _
    exact inserted_row_singular_value_le A x (leadingSingularIndex hNext j)
      (insertedLeadingSingularIndex h j) rfl

theorem row_addition_product_bound_of_next_singular_value {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (hNext : r + 1 ≤ n)
    (x : EuclideanSpace ℂ (Fin m)) {η : ℝ}
    (hThreshold : η ≤ orderedMatrixSingularValues A
      ⟨r, by simp only [Fintype.card_fin]; omega⟩) :
    η * leadingRowSingularProduct A h ≤ insertedLeadingSingularProduct A h x := by
  have hProduct := inserted_row_leading_product_le A h hNext x
  rw [leading_row_singular_product_succ A h hNext] at hProduct
  exact (mul_le_mul_of_nonneg_right hThreshold (leading_row_singular_product_nonneg A h)).trans
    (by simpa only [mul_comm] using hProduct)

theorem row_addition_product_bound_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) {η : ℝ}
    (hThreshold : η ≤ ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
      (rowAdjointVector x)‖) :
    η * leadingRowSingularProduct A h ≤ insertedLeadingSingularProduct A h x :=
  (mul_le_mul_of_nonneg_right hThreshold (leading_row_singular_product_nonneg A h)).trans
    (row_addition_leading_singular_product_bound A h x)

end CircularLaw
