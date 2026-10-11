import CircularLaw.LeadingRowSingularCompression

/-!
# Leading singular products after inserting a row

A block coisometry retains the new row and the leading r left singular
directions of the old matrix. The exact inserted Gram determinant and
the compression bound give the base-times-height singular-product
inequality. The zero leading-product case is included.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

def insertedLeadingRowCompression {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 (leadingRowCompression A h)

def insertedLeadingSingularIndex {r n : ℕ} (h : r ≤ n) (j : Fin (r + 1)) :
    Fin (Fintype.card (Unit ⊕ Fin n)) :=
  ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]; omega⟩

def insertedLeadingSingularProduct {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) : ℝ :=
  ∏ j : Fin (r + 1), orderedMatrixSingularValues (hybridInsertedRows A x)
    (insertedLeadingSingularIndex h j)

theorem inserted_leading_row_compression_coisometry {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    insertedLeadingRowCompression A h * (insertedLeadingRowCompression A h).conjTranspose = 1 := by
  simp only [insertedLeadingRowCompression, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    leading_row_compression_coisometry, Matrix.fromBlocks_one]

theorem inserted_leading_row_compression_apply {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    insertedLeadingRowCompression A h * hybridInsertedRows A x =
      hybridInsertedRows (leadingCompressedRows A h) x := by
  simp only [insertedLeadingRowCompression, hybridInsertedRows, Matrix.fromBlocks_mul_fromRows,
    Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, leadingCompressedRows]

theorem inserted_leading_singular_product_nonneg {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    0 ≤ insertedLeadingSingularProduct A h x :=
  Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)

theorem inserted_leading_compressed_gram_det_bound {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    (hybridInsertedRows (leadingCompressedRows A h) x *
      (hybridInsertedRows (leadingCompressedRows A h) x).conjTranspose).det.re ≤
        insertedLeadingSingularProduct A h x ^ 2 := by
  have hCard : Fintype.card (Unit ⊕ Fin r) ≤ Fintype.card (Unit ⊕ Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
    omega
  have hBound := orthonormal_row_compression_gram_det_bound
    (insertedLeadingRowCompression A h) (inserted_leading_row_compression_coisometry A h)
    (hybridInsertedRows A x) hCard
  rw [inserted_leading_row_compression_apply] at hBound
  have hProd : (∏ j : Fin (Fintype.card (Unit ⊕ Fin r)),
      orderedMatrixSingularValues (hybridInsertedRows A x) (Fin.castLE hCard j)) =
      insertedLeadingSingularProduct A h x := by
    let e : Fin (Fintype.card (Unit ⊕ Fin r)) ≃ Fin (r + 1) := finCongr (by
      simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
      omega)
    calc
      _ = ∏ j : Fin (Fintype.card (Unit ⊕ Fin r)),
          orderedMatrixSingularValues (hybridInsertedRows A x)
            (insertedLeadingSingularIndex h (e j)) := by
        apply Finset.prod_congr rfl
        intro j _
        exact congrArg (orderedMatrixSingularValues (hybridInsertedRows A x)) (Fin.ext rfl)
      _ = _ := e.prod_comp (fun j => orderedMatrixSingularValues (hybridInsertedRows A x)
          (insertedLeadingSingularIndex h j))
  rwa [hProd] at hBound

theorem row_addition_leading_singular_product_bound {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
      (rowAdjointVector x)‖ * leadingRowSingularProduct A h ≤
        insertedLeadingSingularProduct A h x := by
  by_cases hProd : leadingRowSingularProduct A h = 0
  · rw [hProd, mul_zero]
    exact inserted_leading_singular_product_nonneg A h x
  · have hDet := inserted_row_gram_det_real_kernel_projection (leadingCompressedRows A h)
      (leading_compressed_rows_gram_invertible A h hProd) x
    rw [leading_compressed_rows_gram_det] at hDet
    have hBound := inserted_leading_compressed_gram_det_bound A h x
    rw [hDet] at hBound
    have hLeft : 0 ≤ ‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
        (rowAdjointVector x)‖ * leadingRowSingularProduct A h :=
      mul_nonneg (norm_nonneg _) (leading_row_singular_product_nonneg A h)
    have hSq : (‖(LinearMap.ker (leadingCompressedRows A h).toEuclideanLin).starProjection
        (rowAdjointVector x)‖ * leadingRowSingularProduct A h) ^ 2 ≤
        insertedLeadingSingularProduct A h x ^ 2 := by
      simpa only [mul_pow, mul_comm] using hBound
    exact (sq_le_sq₀ hLeft (inserted_leading_singular_product_nonneg A h x)).mp hSq

end CircularLaw
