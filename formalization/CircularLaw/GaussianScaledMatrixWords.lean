import CircularLaw.GaussianMatrixWords

/-!
# Matrix-word cancellation after Gaussian normalization

Scaling a Gaussian matrix by a complex scalar scales each direct factor
by that scalar and each adjoint factor by its actual conjugate. The
complete word retains its noncommuting order; its scalar coefficient is
the product of those factors. Unbalanced trace expectations still vanish.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

def gaussianScaledMatrixWord {n : ℕ} (c : ℂ) (w : List Bool) (x : GaussianSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (w.map (fun b => if b then (c • gaussianSquareMatrix x).conjTranspose
    else c • gaussianSquareMatrix x)).prod

def gaussianMatrixWordScale (c : ℂ) (w : List Bool) : ℂ :=
  (w.map (fun b => if b then star c else c)).prod

theorem gaussian_scaled_matrix_word_eq {n : ℕ} (c : ℂ) (w : List Bool)
    (x : GaussianSquareSample n) :
    gaussianScaledMatrixWord c w x = gaussianMatrixWordScale c w • gaussianMatrixWord w x := by
  induction w with
  | nil => simp [gaussianScaledMatrixWord, gaussianMatrixWordScale, gaussianMatrixWord]
  | cons b w ih =>
    cases b <;>
      simp only [gaussianScaledMatrixWord, List.map_cons, List.prod_cons,
        gaussianMatrixWordScale, gaussianMatrixWord, Bool.false_eq_true, if_false, if_true,
        Matrix.conjTranspose_smul] at ih ⊢
    · rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul]
    · rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem gaussian_scaled_matrix_word_trace_eq {n : ℕ} (c : ℂ) (w : List Bool)
    (x : GaussianSquareSample n) :
    (gaussianScaledMatrixWord c w x).trace =
      gaussianMatrixWordScale c w * (gaussianMatrixWord w x).trace := by
  rw [gaussian_scaled_matrix_word_eq, Matrix.trace_smul, smul_eq_mul]

theorem gaussian_scaled_matrix_word_trace_integrable (n : ℕ) (c : ℂ) (w : List Bool) :
    Integrable (fun x => (gaussianScaledMatrixWord c w x).trace) (gaussianSquareMatrixLaw n) := by
  simp only [gaussian_scaled_matrix_word_trace_eq]
  exact (gaussian_matrix_word_trace_integrable n w).const_mul _

theorem gaussian_scaled_matrix_word_trace_integral (n : ℕ) (c : ℂ) (w : List Bool) :
    (∫ x, (gaussianScaledMatrixWord c w x).trace ∂gaussianSquareMatrixLaw n) =
      gaussianMatrixWordScale c w * gaussianPolynomialMean (gaussianSymbolicMatrixWord n w).trace := by
  simp only [gaussian_scaled_matrix_word_trace_eq]
  rw [integral_const_mul, gaussian_matrix_word_trace_integral]

theorem gaussian_scaled_matrix_word_trace_integral_zero (n : ℕ) (c : ℂ) (w : List Bool)
    (hw : gaussianMatrixWordImbalance w ≠ 0) :
    (∫ x, (gaussianScaledMatrixWord c w x).trace ∂gaussianSquareMatrixLaw n) = 0 := by
  simp only [gaussian_scaled_matrix_word_trace_eq]
  rw [integral_const_mul, gaussian_matrix_word_trace_integral_zero n w hw, mul_zero]

theorem gaussian_scaled_matrix_word_count_mismatch_zero (n : ℕ) (c : ℂ) (w : List Bool)
    (hw : w.count false ≠ w.count true) :
    (∫ x, (gaussianScaledMatrixWord c w x).trace ∂gaussianSquareMatrixLaw n) = 0 := by
  simp only [gaussian_scaled_matrix_word_trace_eq]
  rw [integral_const_mul, gaussian_matrix_word_trace_count_mismatch_zero n w hw, mul_zero]

end CircularLaw
