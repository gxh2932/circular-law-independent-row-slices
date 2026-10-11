import CircularLaw.GaussianRowExposure
import CircularLaw.SquareSingularDeterminant
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full rank of actual Gaussian matrices at every deterministic shift

Almost sure row independence implies a nonzero determinant. The exact
row-to-entry product law transfers this to the actual matrix samples.
Nonzero scaling and arbitrary deterministic matrix shifts are allowed,
including the normalization and scalar shift used in hermitization.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix

namespace CircularLaw

theorem complex_matrix_det_ne_zero_of_linearIndependent_rows {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hLI : LinearIndependent ℂ A) :
    A.det ≠ 0 := by
  have hSpan := hLI.span_eq_top_of_card_eq_finrank'
    (Module.finrank_fintype_fun_eq_card ℂ).symm
  have hUnit := (Module.Basis.is_basis_iff_det (Pi.basisFun ℂ ι)).mp ⟨hLI, hSpan⟩
  simpa only [Pi.basisFun_det_apply, Matrix.of_apply] using hUnit.ne_zero

theorem gaussian_rows_shift_det_ne_zero_ae (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᵐ x ∂gaussianRowsLaw n n, Matrix.det (fun i j => x i j + B i j) ≠ 0 := by
  let w : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (B i)
  filter_upwards [gaussian_shifted_rows_linearIndependent_ae w (le_refl n)] with x hx
  apply complex_matrix_det_ne_zero_of_linearIndependent_rows
  exact hx.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap (by simp)

theorem gaussian_matrix_shift_det_ne_zero_ae (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᵐ x ∂gaussianSquareMatrixLaw n, (gaussianSquareMatrix x + B).det ≠ 0 := by
  have hUncurry : Measurable (fun x : GaussianRowsSample n n => fun p : Fin n × Fin n => x p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  have hMatrix : Continuous (fun x : GaussianSquareSample n => gaussianSquareMatrix x + B) := by
    unfold gaussianSquareMatrix
    fun_prop
  rw [← gaussian_square_rows_uncurry_law]
  exact (ae_map_iff hUncurry.aemeasurable
    (measurableSet_eq_fun hMatrix.matrix_det.measurable measurable_const).compl).mpr
      (gaussian_rows_shift_det_ne_zero_ae n B)

theorem gaussian_scaled_matrix_shift_det_ne_zero_ae (n : ℕ) (c : ℂ) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᵐ x ∂gaussianSquareMatrixLaw n, (c • gaussianSquareMatrix x + B).det ≠ 0 := by
  filter_upwards [gaussian_matrix_shift_det_ne_zero_ae n (c⁻¹ • B)] with x hx
  have hEq : c • gaussianSquareMatrix x + B = c • (gaussianSquareMatrix x + c⁻¹ • B) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [hEq, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hx

theorem gaussian_normalized_shift_det_ne_zero_ae {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ∀ᵐ x ∂gaussianSquareMatrixLaw n, (normalizedShiftedGaussianMatrix z x).det ≠ 0 := by
  have hScale : (Real.sqrt (n : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne')
  simpa only [normalizedShiftedGaussianMatrix, sub_eq_add_neg] using
    gaussian_scaled_matrix_shift_det_ne_zero_ae n (Real.sqrt (n : ℝ) : ℂ)⁻¹ hScale (-(z • 1))

theorem gaussian_normalized_shift_singular_values_pos_ae {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ∀ᵐ x ∂gaussianSquareMatrixLaw n, ∀ j,
      0 < orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j := by
  filter_upwards [gaussian_normalized_shift_det_ne_zero_ae hn z] with x hx
  exact square_singular_values_pos_of_det_ne_zero _ hx

theorem gaussian_normalized_shift_singular_event_null {n : ℕ} (hn : 0 < n) (z : ℂ) :
    gaussianSquareMatrixLaw n {x | (normalizedShiftedGaussianMatrix z x).det = 0} = 0 := by
  have h := gaussian_normalized_shift_det_ne_zero_ae hn z
  simpa only [ae_iff, not_not] using h

end CircularLaw
