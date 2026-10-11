import CircularLaw.ShiftedSliceUnitNormal
import CircularLaw.BernoulliSquareMatrixLaw
import CircularLaw.NonAlmostBernoulliSmallBall

/-!
# Leave-one-out unit normals for the actual Bernoulli matrix

The chosen normal depends only on the other rows. The fresh-row scalar
form is the actual Bernoulli sum, with its diagonal shift retained.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def fullShiftedBernoulliMatrix {n : ℕ} (ζ : ℂ) (sample : BernoulliSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ := bernoulliSquareMatrix sample - ζ • 1

theorem shifted_bernoulli_matrix_apply_eq_row_form {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x i =
      (∑ j, weightedBernoulliValue (x j) (sample (i, j))) - ζ * x i := by
  change (∑ j, (bernoulliSquareMatrix sample - ζ • 1) i j * x j) = _
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    cases h : sample (i, j) <;> simp [bernoulliSquareMatrix, weightedBernoulliValue, h]
  · simp [Matrix.one_apply]

def shiftedBernoulliUnitNormal {n : ℕ} (ζ : ℂ)
    (sample : BernoulliSquareSample n) (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
  leaveOneOutUnitNormal (complexConjugateRows (fullShiftedBernoulliMatrix ζ sample)) i

theorem shifted_bernoulli_unit_normal_norm {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n) :
    ‖shiftedBernoulliUnitNormal ζ sample i‖ = 1 := leave_one_out_unit_normal_norm _ _

theorem shifted_bernoulli_unit_normal_congr {n : ℕ}
    (ζ : ℂ) (sample sample' : BernoulliSquareSample n) (i : Fin n)
    (hOther : ∀ j : Fin n, j ≠ i → ∀ k, sample (j, k) = sample' (j, k)) :
    shiftedBernoulliUnitNormal ζ sample i = shiftedBernoulliUnitNormal ζ sample' i := by
  apply leave_one_out_unit_normal_congr
  intro j hji
  ext k
  simp only [complexConjugateRows, PiLp.toLp_apply, fullShiftedBernoulliMatrix,
    Matrix.sub_apply, bernoulliSquareMatrix, hOther j hji k]

theorem shifted_bernoulli_unit_normal_other_kernel {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i j : Fin n) (hji : j ≠ i) :
    (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin
      (shiftedBernoulliUnitNormal ζ sample i) j = 0 := by
  rw [← complex_conjugate_row_inner_eq_matrix_apply]
  apply inner_eq_zero_symm.mpr
  exact leave_one_out_unit_normal_inner_other _ hji

theorem shifted_bernoulli_unit_normal_row_form_le_distance {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n) :
    ‖(∑ j, weightedBernoulliValue (shiftedBernoulliUnitNormal ζ sample i j)
        (sample (i, j))) - ζ * shiftedBernoulliUnitNormal ζ sample i i‖ ≤
      finiteRowDistance (complexConjugateRows (fullShiftedBernoulliMatrix ζ sample)) i := by
  rw [← shifted_bernoulli_matrix_apply_eq_row_form,
    ← complex_conjugate_row_inner_eq_matrix_apply, norm_inner_symm]
  exact leave_one_out_unit_normal_inner_le_distance _ _

def bernoulliLeaveOneOutAlmostConstantKernelFailure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n) (δ ρ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    ∀ j : Fin n, j ≠ i → (fullShiftedBernoulliMatrix ζ sample).toEuclideanLin x j = 0

theorem shifted_bernoulli_unit_normal_almost_implies_kernel_failure {n : ℕ}
    (ζ : ℂ) (sample : BernoulliSquareSample n) (i : Fin n) (δ ρ : ℝ)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ (shiftedBernoulliUnitNormal ζ sample i)) :
    bernoulliLeaveOneOutAlmostConstantKernelFailure ζ sample i δ ρ :=
  ⟨_, shifted_bernoulli_unit_normal_norm ζ sample i, hAlmost,
    shifted_bernoulli_unit_normal_other_kernel ζ sample i⟩

end CircularLaw
