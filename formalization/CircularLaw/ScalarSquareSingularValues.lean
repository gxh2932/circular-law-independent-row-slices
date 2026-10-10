import CircularLaw.SquareSingularSecondMoment

/-!
# Singular values of a scalar identity matrix

The Gram matrix is `|c|^2 I`. Its actual ordered eigenvectors identify
every Gram eigenvalue with `|c|^2`, including repeated eigenvalues and
the zero scalar. Every ordered singular value is therefore `|c|`.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem scalar_square_gram (n : ℕ) (c : ℂ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *
        (c • (1 : Matrix (Fin n) (Fin n) ℂ)).conjTranspose =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have hScalar : c * star c = (‖c‖ ^ 2 : ℝ) := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  rw [mul_comm, hScalar]

theorem scalar_square_gram_eigenvalues (n : ℕ) (c : ℂ)
    (j : Fin (Fintype.card (Fin n))) :
    (Matrix.isHermitian_mul_conjTranspose_self
      (c • (1 : Matrix (Fin n) (Fin n) ℂ))).eigenvalues₀ j = ‖c‖ ^ 2 := by
  let A := c • (1 : Matrix (Fin n) (Fin n) ℂ)
  let hA := Matrix.isHermitian_mul_conjTranspose_self A
  let hT := Matrix.isHermitian_iff_isSymmetric.mp hA
  let v := hT.eigenvectorBasis finrank_euclideanSpace j
  have hv : v ≠ 0 := (hT.eigenvectorBasis finrank_euclideanSpace).toBasis.ne_zero j
  have hAction : (A * A.conjTranspose).toEuclideanLin v = ((‖c‖ ^ 2 : ℝ) : ℂ) • v := by
    rw [scalar_square_gram]
    simp only [Matrix.toEuclideanLin, map_smul, Matrix.toLpLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hEigen := hT.apply_eigenvectorBasis finrank_euclideanSpace j
  change (A * A.conjTranspose).toEuclideanLin v = (hA.eigenvalues₀ j : ℂ) • v at hEigen
  rw [hAction] at hEigen
  have hScalar := smul_left_injective ℂ hv hEigen
  exact (Complex.ofReal_injective hScalar).symm

theorem scalar_square_singular_values (n : ℕ) (c : ℂ) (j : Fin n) :
    orderedSquareSingularValues (c • (1 : Matrix (Fin n) (Fin n) ℂ)) j = ‖c‖ := by
  rw [orderedSquareSingularValues, scalar_square_gram_eigenvalues, Real.sqrt_sq (norm_nonneg c)]

end CircularLaw
