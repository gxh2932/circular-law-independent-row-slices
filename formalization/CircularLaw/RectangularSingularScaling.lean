import CircularLaw.MatrixSingularVolumes
import CircularLaw.SquareSingularPerturbationBounds

/-!
# Scaling actual rectangular singular values

The row index is any finite type, including the disjoint union used by
row insertion. Adjoint norm comparison gives homogeneity at every index,
including zero scalars and singular matrices. Positive degree scaling
then divides every actual singular value by the square root of the degree.
-/

noncomputable section
open Classical
open scoped InnerProductSpace Matrix

namespace CircularLaw

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

theorem ordered_matrix_singular_le_of_adjoint_bound
    (A B : Matrix ι τ ℂ) {r delta : ℝ} (hr : 0 ≤ r)
    (hBound : ∀ v : EuclideanSpace ℂ ι,
      ‖A.conjTranspose.toEuclideanLin v‖ ≤
        r * ‖B.conjTranspose.toEuclideanLin v‖ + delta * ‖v‖)
    (j : Fin (Fintype.card ι)) :
    orderedMatrixSingularValues A j ≤ r * orderedMatrixSingularValues B j + delta := by
  let hA := Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A)
  let hB := Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self B)
  let W := spectralLeadingSubspace hA finrank_euclideanSpace j
  let V := LinearMap.ker (spectralHeadCoordinateMap hB finrank_euclideanSpace j)
  have hW : Module.finrank ℂ W = j.val + 1 :=
    spectral_leading_subspace_dimension hA finrank_euclideanSpace j
  have hV : Fintype.card ι ≤ Module.finrank ℂ V + j.val :=
    spectral_head_kernel_dimension hB finrank_euclideanSpace j
  have hIntersection : ∃ v : EuclideanSpace ℂ ι, v ∈ W ∧ v ∈ V ∧ v ≠ 0 := by
    by_contra! hAll
    have hDisjoint : Disjoint W V := Submodule.disjoint_def.mpr hAll
    have hRanks := Submodule.finrank_add_finrank_le_of_disjoint hDisjoint
    rw [finrank_euclideanSpace, hW] at hRanks
    omega
  obtain ⟨v, hvW, hvV, hv0⟩ := hIntersection
  have hLower : orderedMatrixSingularValues A j ^ 2 * ‖v‖ ^ 2 ≤
      ‖A.conjTranspose.toEuclideanLin v‖ ^ 2 := by
    rw [ordered_matrix_singular_values_sq]
    exact (spectral_leading_subspace_rayleigh hA finrank_euclideanSpace j v hvW).trans_eq
      (matrix_row_gram_quadratic_eq_adjoint_norm A v)
  have hUpper : ‖B.conjTranspose.toEuclideanLin v‖ ^ 2 ≤
      orderedMatrixSingularValues B j ^ 2 * ‖v‖ ^ 2 := by
    rw [ordered_matrix_singular_values_sq, ← matrix_row_gram_quadratic_eq_adjoint_norm B v]
    exact symmetric_quadratic_le_tail hB finrank_euclideanSpace j v
      (spectral_head_kernel_vanishes hB finrank_euclideanSpace j v hvV)
  have hLA : orderedMatrixSingularValues A j * ‖v‖ ≤ ‖A.conjTranspose.toEuclideanLin v‖ := by
    nlinarith [ordered_matrix_singular_values_nonneg A j, norm_nonneg v,
      norm_nonneg (A.conjTranspose.toEuclideanLin v)]
  have hUB : ‖B.conjTranspose.toEuclideanLin v‖ ≤ orderedMatrixSingularValues B j * ‖v‖ := by
    nlinarith [mul_nonneg (ordered_matrix_singular_values_nonneg B j) (norm_nonneg v),
      norm_nonneg (B.conjTranspose.toEuclideanLin v)]
  have hCompare := (hBound v).trans
    (add_le_add (mul_le_mul_of_nonneg_left hUB hr) (le_refl (delta * ‖v‖)))
  have hNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  nlinarith

omit [Fintype τ] [DecidableEq τ] in
theorem matrix_adjoint_smul_apply (A : Matrix ι τ ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ ι) :
    (c • A).conjTranspose.toEuclideanLin v = star c • A.conjTranspose.toEuclideanLin v := by
  simp only [Matrix.conjTranspose_smul, Matrix.toEuclideanLin, map_smul, LinearMap.smul_apply]

theorem ordered_matrix_singular_smul_le (A : Matrix ι τ ℂ)
    (c : ℂ) (j : Fin (Fintype.card ι)) :
    orderedMatrixSingularValues (c • A) j ≤ ‖c‖ * orderedMatrixSingularValues A j := by
  apply (ordered_matrix_singular_le_of_adjoint_bound (c • A) A (r := ‖c‖)
    (delta := 0) (norm_nonneg c) ?_ j).trans_eq (by simp)
  intro v
  simp only [matrix_adjoint_smul_apply, norm_smul, norm_star, zero_mul, add_zero, le_refl]

theorem ordered_matrix_singular_smul (A : Matrix ι τ ℂ)
    (c : ℂ) (j : Fin (Fintype.card ι)) :
    orderedMatrixSingularValues (c • A) j = ‖c‖ * orderedMatrixSingularValues A j := by
  apply le_antisymm (ordered_matrix_singular_smul_le A c j)
  by_cases hc : c = 0
  · subst c
    simpa only [norm_zero, zero_mul] using
      ordered_matrix_singular_values_nonneg ((0 : ℂ) • A) j
  · have hInverse := ordered_matrix_singular_smul_le (c • A) c⁻¹ j
    rw [inv_smul_smul₀ hc, norm_inv] at hInverse
    have hNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h := mul_le_mul_of_nonneg_left hInverse hNorm.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hNorm.ne', one_mul] using h

def degreeNormalizingScalar (d : ℝ) : ℂ := (Real.sqrt d : ℂ)⁻¹

theorem degree_normalizing_scalar_norm {d : ℝ} (hd : 0 < d) :
    ‖degreeNormalizingScalar d‖ = (Real.sqrt d)⁻¹ := by
  rw [degreeNormalizingScalar, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hd)]

theorem degree_normalizing_scalar_ne_zero {d : ℝ} (hd : 0 < d) :
    degreeNormalizingScalar d ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_pos.mpr hd).ne'

theorem ordered_matrix_singular_degree_normalization (A : Matrix ι τ ℂ)
    {d : ℝ} (hd : 0 < d) (j : Fin (Fintype.card ι)) :
    orderedMatrixSingularValues (degreeNormalizingScalar d • A) j =
      orderedMatrixSingularValues A j / Real.sqrt d := by
  rw [ordered_matrix_singular_smul, degree_normalizing_scalar_norm hd]
  ring

end CircularLaw
