import CircularLaw.GaussianMatrixBilinearTail
import CircularLaw.MatrixColumnRestriction

/-!
# Euclidean matrix operator algebra and singular-value bounds

The actual operator is linear in the matrix entries. Adjoint preserves
its norm, and each ordered singular value is bounded by this operator
norm through a unit Gram eigenvector.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace Matrix

namespace CircularLaw

theorem complex_matrix_operator_smul {m n : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    complexMatrixOperator (c • A) = c • complexMatrixOperator A := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  change (∑ j, (c * A i j) * v j) = c * ∑ j, A i j * v j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem complex_matrix_operator_sub {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    complexMatrixOperator (A - B) = complexMatrixOperator A - complexMatrixOperator B := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  change (∑ j, (A i j - B i j) * v j) = (∑ j, A i j * v j) - ∑ j, B i j * v j
  simp only [sub_mul, Finset.sum_sub_distrib]

theorem complex_matrix_operator_one (n : ℕ) :
    complexMatrixOperator (1 : Matrix (Fin n) (Fin n) ℂ) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  simp only [complex_matrix_operator_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ContinuousLinearMap.id_apply]

theorem complex_matrix_operator_shift_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    ‖complexMatrixOperator (A - z • 1)‖ ≤ ‖complexMatrixOperator A‖ + ‖z‖ := by
  rw [complex_matrix_operator_sub, complex_matrix_operator_smul, complex_matrix_operator_one]
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg z)

theorem complex_matrix_operator_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    complexMatrixOperator A.conjTranspose = (complexMatrixOperator A).adjoint := by
  rw [complexMatrixOperator, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]
  rfl

theorem complex_matrix_operator_conjTranspose_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖complexMatrixOperator A.conjTranspose‖ = ‖complexMatrixOperator A‖ := by
  rw [complex_matrix_operator_conjTranspose, LinearIsometryEquiv.norm_map]

theorem ordered_square_singular_value_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    orderedSquareSingularValues A j ≤ ‖complexMatrixOperator A‖ := by
  let H := Matrix.isHermitian_mul_conjTranspose_self A
  let T := (A * A.conjTranspose).toEuclideanLin
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp H
  let i : Fin (Fintype.card (Fin n)) := ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
  let v := hT.eigenvectorBasis finrank_euclideanSpace i
  have hNorm : ‖v‖ = 1 := (hT.eigenvectorBasis finrank_euclideanSpace).norm_eq_one i
  have hEigen : T v = (H.eigenvalues₀ i : ℂ) • v := hT.apply_eigenvectorBasis finrank_euclideanSpace i
  have hSquare : orderedSquareSingularValues A j ^ 2 =
      ‖A.conjTranspose.toEuclideanLin v‖ ^ 2 := by
    rw [orderedSquareSingularValues_sq]
    have h := row_gram_quadratic_eq_adjoint_norm A v
    change (⟪T v, v⟫_ℂ).re = _ at h
    rw [hEigen, inner_smul_left, inner_self_eq_norm_sq_to_K, hNorm] at h
    simpa only [i, map_one, one_pow, mul_one, Complex.conj_ofReal, Complex.ofReal_re] using h
  have hBound := (complexMatrixOperator A.conjTranspose).le_opNorm v
  rw [complex_matrix_operator_conjTranspose_norm, hNorm, mul_one] at hBound
  have hNonneg := orderedSquareSingularValues_nonneg A j
  have hOpNonneg := norm_nonneg (complexMatrixOperator A)
  change ‖A.conjTranspose.toEuclideanLin v‖ ≤ _ at hBound
  have hBoundSq := (sq_le_sq₀ (norm_nonneg _) hOpNonneg).mpr hBound
  rw [← hSquare] at hBoundSq
  exact (sq_le_sq₀ hNonneg hOpNonneg).mp hBoundSq

end CircularLaw
