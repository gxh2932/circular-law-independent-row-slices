import CircularLaw.PositiveContractionGeometry

/-!
# Literal row and column ridge Gram matrices for a hybrid

Positive regularization makes both matrices positive definite. Their
intertwining identity transports the inverse through the rectangular
matrix without any invertibility premise on that rectangular matrix.
-/

noncomputable section
open Classical
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def hybridRowRidgeGram (K : Matrix m n ℂ) (η : ℝ) : Matrix m m ℂ :=
  K * Kᴴ + (η ^ 2) • 1

def hybridColumnRidgeGram (K : Matrix m n ℂ) (η : ℝ) : Matrix n n ℂ :=
  Kᴴ * K + (η ^ 2) • 1

omit [DecidableEq n] in
theorem hybridRowRidgeGram_posDef (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridRowRidgeGram K η).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_self_mul_conjTranspose K)
    (Matrix.PosDef.one.smul (sq_pos_of_pos hη))

omit [DecidableEq m] in
theorem hybridColumnRidgeGram_posDef (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridColumnRidgeGram K η).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self K)
    (Matrix.PosDef.one.smul (sq_pos_of_pos hη))

omit [DecidableEq n] in
theorem hybridRowRidgeGram_isUnit_det (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    IsUnit (hybridRowRidgeGram K η).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (hybridRowRidgeGram_posDef K hη).isUnit

omit [DecidableEq m] in
theorem hybridColumnRidgeGram_isUnit_det (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    IsUnit (hybridColumnRidgeGram K η).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (hybridColumnRidgeGram_posDef K hη).isUnit

theorem hybridRidgeGram_intertwine (K : Matrix m n ℂ) (η : ℝ) :
    hybridRowRidgeGram K η * K = K * hybridColumnRidgeGram K η := by
  simp only [hybridRowRidgeGram, hybridColumnRidgeGram, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem hybridRidgeGram_inverse_intertwine (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    (hybridRowRidgeGram K η)⁻¹ * K = K * (hybridColumnRidgeGram K η)⁻¹ := by
  have hR := hybridRowRidgeGram_isUnit_det K hη
  have hC := hybridColumnRidgeGram_isUnit_det K hη
  calc
    _ = (hybridRowRidgeGram K η)⁻¹ * K *
        (hybridColumnRidgeGram K η * (hybridColumnRidgeGram K η)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hC, Matrix.mul_one]
    _ = (hybridRowRidgeGram K η)⁻¹ *
        (K * hybridColumnRidgeGram K η) * (hybridColumnRidgeGram K η)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = (hybridRowRidgeGram K η)⁻¹ *
        (hybridRowRidgeGram K η * K) * (hybridColumnRidgeGram K η)⁻¹ := by
      rw [hybridRidgeGram_intertwine]
    _ = K * (hybridColumnRidgeGram K η)⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hR, Matrix.one_mul]

end CircularLaw
