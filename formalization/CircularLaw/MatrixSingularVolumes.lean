import CircularLaw.RectangularSingularInterlacing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Singular volumes under orthonormal row compression

The row index may be any finite type, including the disjoint union used
when adding a row. A coisometric row compression has a checked adjoint
isometry, so ordered eigenvalue comparison bounds its Gram determinant
by the squared product of the corresponding leading singular values.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace CircularLaw

variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

def orderedMatrixSingularValues (A : Matrix ι τ ℂ) : Fin (Fintype.card ι) → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ j)

omit [DecidableEq τ] in
theorem ordered_matrix_singular_values_nonneg (A : Matrix ι τ ℂ)
    (j : Fin (Fintype.card ι)) : 0 ≤ orderedMatrixSingularValues A j := Real.sqrt_nonneg _

omit [DecidableEq τ] in
theorem ordered_matrix_gram_eigenvalues_nonneg (A : Matrix ι τ ℂ)
    (j : Fin (Fintype.card ι)) :
    0 ≤ (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ j := by
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (by simp)
  have h := (Matrix.posSemidef_self_mul_conjTranspose A).eigenvalues_nonneg (e j)
  change 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ (e.symm (e j)) at h
  simpa only [Equiv.symm_apply_apply] using h

omit [DecidableEq τ] in
theorem ordered_matrix_singular_values_sq (A : Matrix ι τ ℂ)
    (j : Fin (Fintype.card ι)) :
    orderedMatrixSingularValues A j ^ 2 =
      (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ j :=
  Real.sq_sqrt (ordered_matrix_gram_eigenvalues_nonneg A j)

omit [DecidableEq τ] in
theorem matrix_gram_det_eq_singular_product_sq (A : Matrix ι τ ℂ) :
    (A * A.conjTranspose).det.re = (∏ j, orderedMatrixSingularValues A j) ^ 2 := by
  let hA := Matrix.isHermitian_mul_conjTranspose_self A
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (by simp)
  have hDet : (A * A.conjTranspose).det.re = ∏ j : Fin (Fintype.card ι), hA.eigenvalues₀ j := by
    rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    simp only [Matrix.IsHermitian.eigenvalues]
    exact e.symm.prod_comp hA.eigenvalues₀
  rw [hDet, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  exact (ordered_matrix_singular_values_sq A j).symm

theorem matrix_row_gram_quadratic_eq_adjoint_norm (A : Matrix ι τ ℂ)
    (v : EuclideanSpace ℂ ι) :
    (⟪(A * A.conjTranspose).toEuclideanLin v, v⟫_ℂ).re =
      ‖A.conjTranspose.toEuclideanLin v‖ ^ 2 := by
  have h := LinearMap.adjoint_inner_right A.toEuclideanLin (A.conjTranspose.toEuclideanLin v) v
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [← h]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A.conjTranspose.toEuclideanLin v)).symm

def matrixCoisometryEmbedding (Q : Matrix κ ι ℂ) (hQ : Q * Q.conjTranspose = 1) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toLinearMap := Q.conjTranspose.toEuclideanLin
  norm_map' v := by
    have h := matrix_row_gram_quadratic_eq_adjoint_norm Q v
    rw [hQ] at h
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    norm_cast at h
    change ‖v‖ ^ 2 = ‖Q.conjTranspose.toEuclideanLin v‖ ^ 2 at h
    nlinarith [norm_nonneg (Q.conjTranspose.toEuclideanLin v), norm_nonneg v]

theorem matrix_coisometry_dimension_le (Q : Matrix κ ι ℂ) (hQ : Q * Q.conjTranspose = 1) :
    Fintype.card κ ≤ Fintype.card ι := by
  have h := LinearMap.finrank_le_finrank_of_injective (matrixCoisometryEmbedding Q hQ).injective
  simpa only [finrank_euclideanSpace] using h

theorem matrix_row_compression_quadratic (Q : Matrix κ ι ℂ) (A : Matrix ι τ ℂ)
    (v : EuclideanSpace ℂ κ) :
    (⟪((Q * A) * (Q * A).conjTranspose).toEuclideanLin v, v⟫_ℂ).re =
      (⟪(A * A.conjTranspose).toEuclideanLin (Q.conjTranspose.toEuclideanLin v),
        Q.conjTranspose.toEuclideanLin v⟫_ℂ).re := by
  rw [matrix_row_gram_quadratic_eq_adjoint_norm, matrix_row_gram_quadratic_eq_adjoint_norm]
  simp only [Matrix.conjTranspose_mul, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]

theorem orthonormal_row_compression_singular_value_le
    (Q : Matrix κ ι ℂ) (hQ : Q * Q.conjTranspose = 1) (A : Matrix ι τ ℂ)
    (i : Fin (Fintype.card κ)) (j : Fin (Fintype.card ι)) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues (Q * A) i ≤ orderedMatrixSingularValues A j := by
  apply Real.sqrt_le_sqrt
  apply symmetric_ordered_eigenvalues_le_under_isometry
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self (Q * A)))
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A))
    finrank_euclideanSpace finrank_euclideanSpace (matrixCoisometryEmbedding Q hQ)
    _ i j hIndex
  intro v
  exact (matrix_row_compression_quadratic Q A v).le

theorem orthonormal_row_compression_gram_det_bound
    (Q : Matrix κ ι ℂ) (hQ : Q * Q.conjTranspose = 1) (A : Matrix ι τ ℂ)
    (hCard : Fintype.card κ ≤ Fintype.card ι) :
    ((Q * A) * (Q * A).conjTranspose).det.re ≤
      (∏ j : Fin (Fintype.card κ), orderedMatrixSingularValues A (Fin.castLE hCard j)) ^ 2 := by
  rw [matrix_gram_det_eq_singular_product_sq]
  have hProd : (∏ j : Fin (Fintype.card κ), orderedMatrixSingularValues (Q * A) j) ≤
      ∏ j : Fin (Fintype.card κ), orderedMatrixSingularValues A (Fin.castLE hCard j) := by
    apply Finset.prod_le_prod
    · intro j _
      exact ordered_matrix_singular_values_nonneg (Q * A) j
    · intro j _
      exact orthonormal_row_compression_singular_value_le Q hQ A j (Fin.castLE hCard j) rfl
  have hLeft : 0 ≤ ∏ j : Fin (Fintype.card κ), orderedMatrixSingularValues (Q * A) j :=
    Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
  have hRight : 0 ≤ ∏ j : Fin (Fintype.card κ), orderedMatrixSingularValues A (Fin.castLE hCard j) :=
    Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
  exact (sq_le_sq₀ hLeft hRight).mpr hProd

end CircularLaw
