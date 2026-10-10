import CircularLaw.LeaveOneOutUnitNormal
import CircularLaw.SmallestSingularDistanceReduction

/-!
# The actual leave-one-out normal for a shifted row-slice matrix

The chosen unit normal depends only on the other rows. Its scalar form
is the raw row-slice sum minus the diagonal shift. An almost-constant
normal is an actual unit almost-constant kernel vector for the matrix
with the omitted row removed.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem complex_conjugate_row_inner_eq_matrix_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (x : EuclideanSpace ℂ (Fin n)) :
    ⟪complexConjugateRows A i, x⟫_ℂ = A.toEuclideanLin x i := by
  rw [PiLp.inner_apply]
  change (∑ j, x j * star (star (A i j))) = ∑ j, A i j * x j
  simp only [star_star, mul_comm]

theorem shifted_slice_matrix_apply_eq_row_form {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    (fullShiftedSliceMatrix ζ rows).toEuclideanLin x i =
      rowLinearForm (rows i) (fun j => x j) - ζ * x i := by
  change (∑ j, fullShiftedSliceMatrix ζ rows i j * x j) = _
  simp only [fullShiftedSliceMatrix_apply, sub_mul, Finset.sum_sub_distrib,
    rowLinearForm]
  congr 1
  simp

def shiftedSliceUnitNormal {n d : ℕ} (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
  leaveOneOutUnitNormal (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i

theorem shifted_slice_unit_normal_norm {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    ‖shiftedSliceUnitNormal ζ rows i‖ = 1 := leave_one_out_unit_normal_norm _ _

theorem shifted_slice_unit_normal_update {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (s : RowSlice n d) :
    shiftedSliceUnitNormal ζ (Function.update rows i s) i = shiftedSliceUnitNormal ζ rows i := by
  apply leave_one_out_unit_normal_congr
  intro j hji
  ext k
  simp only [complexConjugateRows, PiLp.toLp_apply, fullShiftedSliceMatrix_apply,
    Function.update_of_ne hji]

theorem shifted_slice_unit_normal_other_kernel {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i j : Fin n) (hji : j ≠ i) :
    (fullShiftedSliceMatrix ζ rows).toEuclideanLin (shiftedSliceUnitNormal ζ rows i) j = 0 := by
  rw [← complex_conjugate_row_inner_eq_matrix_apply]
  apply inner_eq_zero_symm.mpr
  exact leave_one_out_unit_normal_inner_other _ hji

theorem shifted_slice_unit_normal_row_form_le_distance {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) :
    ‖rowLinearForm (rows i) (fun j => shiftedSliceUnitNormal ζ rows i j) -
      ζ * shiftedSliceUnitNormal ζ rows i i‖ ≤
        finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i := by
  rw [← shifted_slice_matrix_apply_eq_row_form, ← complex_conjugate_row_inner_eq_matrix_apply,
    norm_inner_symm]
  exact leave_one_out_unit_normal_inner_le_distance _ _

def sourceLeaveOneOutAlmostConstantKernelFailure {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (δ ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedSliceMatrix ζ rows).toEuclideanLin x j = 0

theorem shifted_slice_unit_normal_almost_implies_kernel_failure {n d : ℕ}
    (ζ : ℂ) (rows : RowSliceMatrix n d) (i : Fin n) (δ ρ : ℝ)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ (shiftedSliceUnitNormal ζ rows i)) :
    sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ :=
  ⟨_, shifted_slice_unit_normal_norm ζ rows i, hAlmost,
    shifted_slice_unit_normal_other_kernel ζ rows i⟩

theorem shifted_slice_unit_normal_almost_probability_le_kernel_failure {n d : ℕ}
    (ζ : ℂ) (i : Fin n) (δ ρ : ℝ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬sourceNonAlmostConstant δ ρ (shiftedSliceUnitNormal ζ rows i)) ≤
      uniformProbability (fun rows : RowSliceMatrix n d =>
        sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) := by
  apply uniformProbability_mono
  intro rows hRows
  exact shifted_slice_unit_normal_almost_implies_kernel_failure ζ rows i δ ρ hRows

end CircularLaw
