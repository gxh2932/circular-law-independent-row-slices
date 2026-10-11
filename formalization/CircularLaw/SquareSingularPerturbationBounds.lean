import CircularLaw.BernoulliCenteringInterlacing
import CircularLaw.ScalarSquareSingularValues

/-!
# Ordered singular values under scaling and scalar shifts

Intersecting a leading Gram subspace with the other Gram's tail kernel
gives the singular-value comparison directly from adjoint norm bounds.
Scalar shifts change each ordered singular value by at most the shift
norm. Scalar multiplication scales every singular value by its norm.
-/

noncomputable section
open Classical
open scoped InnerProductSpace Matrix

namespace CircularLaw

theorem ordered_square_singular_le_of_adjoint_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) {r delta : ℝ} (hr : 0 ≤ r)
    (hBound : ∀ v : EuclideanSpace ℂ (Fin n),
      ‖A.conjTranspose.toEuclideanLin v‖ ≤
        r * ‖B.conjTranspose.toEuclideanLin v‖ + delta * ‖v‖) (j : Fin n) :
    orderedSquareSingularValues A j ≤ r * orderedSquareSingularValues B j + delta := by
  let hA := Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A)
  let hB := Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self B)
  let j' : Fin (Fintype.card (Fin n)) := ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
  let W := spectralLeadingSubspace hA finrank_euclideanSpace j'
  let V := LinearMap.ker (spectralHeadCoordinateMap hB finrank_euclideanSpace j')
  have hW : Module.finrank ℂ W = j.val + 1 :=
    spectral_leading_subspace_dimension hA finrank_euclideanSpace j'
  have hV : Fintype.card (Fin n) ≤ Module.finrank ℂ V + j.val :=
    spectral_head_kernel_dimension hB finrank_euclideanSpace j'
  have hIntersection : ∃ v : EuclideanSpace ℂ (Fin n), v ∈ W ∧ v ∈ V ∧ v ≠ 0 := by
    by_contra! hAll
    have hDisjoint : Disjoint W V := Submodule.disjoint_def.mpr hAll
    have hRanks := Submodule.finrank_add_finrank_le_of_disjoint hDisjoint
    rw [finrank_euclideanSpace, hW] at hRanks
    omega
  obtain ⟨v, hvW, hvV, hv0⟩ := hIntersection
  have hLower : orderedSquareSingularValues A j ^ 2 * ‖v‖ ^ 2 ≤
      ‖A.conjTranspose.toEuclideanLin v‖ ^ 2 := by
    rw [orderedSquareSingularValues_sq]
    exact (spectral_leading_subspace_rayleigh hA finrank_euclideanSpace j' v hvW).trans_eq
      (row_gram_quadratic_eq_adjoint_norm A v)
  have hUpper : ‖B.conjTranspose.toEuclideanLin v‖ ^ 2 ≤
      orderedSquareSingularValues B j ^ 2 * ‖v‖ ^ 2 := by
    rw [orderedSquareSingularValues_sq, ← row_gram_quadratic_eq_adjoint_norm B v]
    exact symmetric_quadratic_le_tail hB finrank_euclideanSpace j' v
      (spectral_head_kernel_vanishes hB finrank_euclideanSpace j' v hvV)
  have hLA : orderedSquareSingularValues A j * ‖v‖ ≤ ‖A.conjTranspose.toEuclideanLin v‖ := by
    nlinarith [orderedSquareSingularValues_nonneg A j, norm_nonneg v,
      norm_nonneg (A.conjTranspose.toEuclideanLin v)]
  have hUB : ‖B.conjTranspose.toEuclideanLin v‖ ≤ orderedSquareSingularValues B j * ‖v‖ := by
    nlinarith [mul_nonneg (orderedSquareSingularValues_nonneg B j) (norm_nonneg v),
      norm_nonneg (B.conjTranspose.toEuclideanLin v)]
  have hCompare := (hBound v).trans
    (add_le_add (mul_le_mul_of_nonneg_left hUB hr) (le_refl (delta * ‖v‖)))
  have hNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  nlinarith

theorem square_adjoint_scalar_shift_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    (A + c • 1).conjTranspose.toEuclideanLin v = A.conjTranspose.toEuclideanLin v + star c • v := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.toEuclideanLin, map_add, map_smul, Matrix.toLpLin_one,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem ordered_square_singular_scalar_shift_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (j : Fin n) :
    orderedSquareSingularValues (A + c • 1) j ≤ orderedSquareSingularValues A j + ‖c‖ := by
  apply (ordered_square_singular_le_of_adjoint_bound (A + c • 1) A (r := 1)
    (delta := ‖c‖) (by norm_num) ?_ j).trans_eq (by simp)
  intro v
  rw [square_adjoint_scalar_shift_apply, one_mul]
  simpa only [norm_smul, norm_star] using norm_add_le (A.conjTranspose.toEuclideanLin v) (star c • v)

theorem ordered_square_singular_scalar_shift_abs_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (j : Fin n) :
    |orderedSquareSingularValues (A + c • 1) j - orderedSquareSingularValues A j| ≤ ‖c‖ := by
  have hUpper := ordered_square_singular_scalar_shift_le A c j
  have hEq : (A + c • 1) + (-c) • 1 = A := by module
  have hLower := ordered_square_singular_scalar_shift_le (A + c • 1) (-c) j
  rw [hEq, norm_neg] at hLower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem square_adjoint_smul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    (c • A).conjTranspose.toEuclideanLin v = star c • A.conjTranspose.toEuclideanLin v := by
  simp only [Matrix.conjTranspose_smul, Matrix.toEuclideanLin, map_smul, LinearMap.smul_apply]

theorem ordered_square_singular_smul_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (j : Fin n) :
    orderedSquareSingularValues (c • A) j ≤ ‖c‖ * orderedSquareSingularValues A j := by
  apply (ordered_square_singular_le_of_adjoint_bound (c • A) A (r := ‖c‖)
    (delta := 0) (norm_nonneg c) ?_ j).trans_eq (by simp)
  intro v
  simp only [square_adjoint_smul_apply, norm_smul, norm_star, zero_mul, add_zero, le_refl]

theorem ordered_square_singular_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (j : Fin n) :
    orderedSquareSingularValues (c • A) j = ‖c‖ * orderedSquareSingularValues A j := by
  by_cases hc : c = 0
  · subst c
    simpa only [zero_smul, norm_zero, zero_mul] using scalar_square_singular_values n (0 : ℂ) j
  · apply le_antisymm (ordered_square_singular_smul_le A c j)
    have hInverse := ordered_square_singular_smul_le (c • A) c⁻¹ j
    rw [inv_smul_smul₀ hc, norm_inv] at hInverse
    have hNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h := mul_le_mul_of_nonneg_left hInverse hNorm.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hNorm.ne', one_mul] using h

end CircularLaw
