import CircularLaw.HybridLogPotential
import CircularLaw.MatrixSingularVolumes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The literal ridge potential as a singular-value logarithmic sum

Unitary diagonalization of the actual row Gram gives its ridge determinant
as the product of eta squared plus each squared row singular value.
Positive regularization permits taking the logarithm without a rank premise.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem hermitian_scalar_shift_det {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (a : ℝ) :
    (A + a • 1).det = ∏ i, ((hA.eigenvalues i + a : ℝ) : ℂ) := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hSpectral : A = (U : Matrix ι ι ℂ) * D * (star U : Matrix ι ι ℂ) := hA.spectral_theorem
  have hUnitMatrix : (U : Matrix ι ι ℂ) * (star U : Matrix ι ι ℂ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
  have hShift : A + a • 1 = (U : Matrix ι ι ℂ) * (D + a • 1) * (star U : Matrix ι ι ℂ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hUnitMatrix, ← hSpectral]
  have hDiagonal : D + a • 1 = Matrix.diagonal (fun i => ((hA.eigenvalues i + a : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · simp [D, hij]
    · simp [D, hij]
  have hUnitDet : (U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det = 1 := by
    rw [← Matrix.det_mul, hUnitMatrix, Matrix.det_one]
  rw [hShift, Matrix.det_mul, Matrix.det_mul, hDiagonal, Matrix.det_diagonal]
  calc
    _ = (∏ i, ((hA.eigenvalues i + a : ℝ) : ℂ)) *
      ((U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det) := by ring
    _ = _ := by rw [hUnitDet, mul_one]

theorem hybrid_row_ridge_gram_det_eq_singular_product (A : Matrix ι κ ℂ) (η : ℝ) :
    (hybridRowRidgeGram A η).det.re =
      ∏ j : Fin (Fintype.card ι), (η ^ 2 + orderedMatrixSingularValues A j ^ 2) := by
  have h := congrArg Complex.re
    (hermitian_scalar_shift_det (Matrix.isHermitian_mul_conjTranspose_self A) (η ^ 2))
  simp only [← Complex.ofReal_prod, Complex.ofReal_re] at h
  change (hybridRowRidgeGram A η).det.re =
    ∏ i, ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i + η ^ 2) at h
  rw [h]
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (by simp)
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro j _
  rw [ordered_matrix_singular_values_sq]
  change (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ (e.symm (e j)) + η ^ 2 = _
  rw [Equiv.symm_apply_apply]
  ring

def matrixRowLogVolume (A : Matrix ι κ ℂ) : ℝ :=
  ∑ j : Fin (Fintype.card ι), Real.log (orderedMatrixSingularValues A j)

theorem regularized_row_potential_eq_singular_log_sum (A : Matrix ι κ ℂ)
    {η : ℝ} (hη : 0 < η) :
    regularizedRowPotential A η =
      ∑ j : Fin (Fintype.card ι), (1 / 2 : ℝ) * Real.log (η ^ 2 + orderedMatrixSingularValues A j ^ 2) := by
  rw [regularizedRowPotential, hybrid_row_ridge_gram_det_eq_singular_product]
  rw [Real.log_prod (fun _ _ => (add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) (sq_nonneg _)).ne')]
  rw [Finset.mul_sum]

theorem matrix_row_log_volume_eq_log_gram_det (A : Matrix ι κ ℂ)
    (hPositive : ∀ j, 0 < orderedMatrixSingularValues A j) :
    matrixRowLogVolume A = (1 / 2 : ℝ) * Real.log (A * A.conjTranspose).det.re := by
  rw [matrix_gram_det_eq_singular_product_sq, Real.log_pow,
    Real.log_prod (fun j _ => (hPositive j).ne')]
  dsimp [matrixRowLogVolume]
  ring

end CircularLaw
