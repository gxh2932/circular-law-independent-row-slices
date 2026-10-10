import CircularLaw.HybridRidgeGram

/-!
# The hybrid comparison matrix is a positive contraction

The literal matrix `I-K* (K K*+eta^2 I)^(-1) K` equals the positive
matrix `eta^2 (K* K+eta^2 I)^(-1)`. Its complement is a positive
sandwich. No spectral or contraction bound is assumed.
-/

noncomputable section
open Classical
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def hybridComparisonMatrix (K : Matrix m n ℂ) (η : ℝ) : Matrix n n ℂ :=
  1 - Kᴴ * (hybridRowRidgeGram K η)⁻¹ * K

theorem hybridComparisonMatrix_inverse_form (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    hybridComparisonMatrix K η = (η ^ 2) • (hybridColumnRidgeGram K η)⁻¹ := by
  have hGram : Kᴴ * K = hybridColumnRidgeGram K η - (η ^ 2) • 1 := by
    dsimp [hybridColumnRidgeGram]
    abel
  rw [hybridComparisonMatrix, Matrix.mul_assoc, hybridRidgeGram_inverse_intertwine K hη,
    ← Matrix.mul_assoc, hGram, Matrix.sub_mul,
    Matrix.mul_nonsing_inv _ (hybridColumnRidgeGram_isUnit_det K hη), Matrix.smul_mul, Matrix.one_mul]
  abel

theorem hybridComparisonMatrix_positive_contraction (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    IsPositiveMatrixContraction (hybridComparisonMatrix K η) := by
  constructor
  · rw [hybridComparisonMatrix_inverse_form K hη]
    exact (hybridColumnRidgeGram_posDef K hη).inv.posSemidef.smul (sq_nonneg η)
  · have h := (hybridRowRidgeGram_posDef K hη).inv.posSemidef.conjTranspose_mul_mul_same K
    simpa only [hybridComparisonMatrix, sub_sub_cancel] using h

theorem hybridComparisonMatrix_identity_on_kernel (K : Matrix m n ℂ) (η : ℝ)
    (x : n → ℂ) (hx : K.mulVec x = 0) :
    (hybridComparisonMatrix K η).mulVec x = x := by
  simp only [hybridComparisonMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

def hybridConjugateComparisonMatrix (K : Matrix m n ℂ) (η : ℝ) : Matrix n n ℂ :=
  (hybridComparisonMatrix K η).map (starRingEnd ℂ)

theorem hybridConjugateComparisonMatrix_eq_transpose (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    hybridConjugateComparisonMatrix K η = (hybridComparisonMatrix K η)ᵀ := by
  have hHerm := (hybridComparisonMatrix_positive_contraction K hη).1.isHermitian
  change (hybridComparisonMatrix K η).map star = (hybridComparisonMatrix K η)ᵀ
  rw [← Matrix.conjTranspose_transpose, hHerm.eq]

theorem hybridConjugateComparisonMatrix_positive_contraction (K : Matrix m n ℂ)
    {η : ℝ} (hη : 0 < η) :
    IsPositiveMatrixContraction (hybridConjugateComparisonMatrix K η) := by
  rw [hybridConjugateComparisonMatrix_eq_transpose K hη]
  have h := hybridComparisonMatrix_positive_contraction K hη
  exact ⟨h.1.transpose, by simpa only [Matrix.transpose_sub, Matrix.transpose_one] using h.2.transpose⟩

end CircularLaw
