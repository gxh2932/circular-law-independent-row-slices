import CircularLaw.MatrixGramShiftTrace
import CircularLaw.GaussianScaledMatrixWords

/-!
# Balanced Gaussian Gram traces after arbitrary scaling

The actual first and second Gram traces have expectations `|c|^2*n^2`
and `2*|c|^4*n^3`. Integrability follows from the checked matrix-word
polynomial construction, including the empty dimension.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_scaled_gram_trace_integrable (n : ℕ) (c : ℂ) :
    Integrable (fun x : GaussianSquareSample n =>
      ((c • gaussianSquareMatrix x) * (c • gaussianSquareMatrix x).conjTranspose).trace)
      (gaussianSquareMatrixLaw n) := by
  simpa [gaussianScaledMatrixWord] using
    gaussian_scaled_matrix_word_trace_integrable n c [false, true]

theorem gaussian_scaled_gram_trace_integral (n : ℕ) (c : ℂ) :
    (∫ x : GaussianSquareSample n,
      ((c • gaussianSquareMatrix x) * (c • gaussianSquareMatrix x).conjTranspose).trace
      ∂gaussianSquareMatrixLaw n) = (‖c‖ ^ 2 : ℝ) * (n : ℂ) ^ 2 := by
  have hScale (x : GaussianSquareSample n) :
      ((c • gaussianSquareMatrix x) * (c • gaussianSquareMatrix x).conjTranspose).trace =
        (‖c‖ ^ 2 : ℝ) * (squareMatrixEnergy (gaussianSquareMatrix x) : ℂ) := by
    simpa only [pow_one, Nat.mul_one, square_gram_trace_eq_energy] using
      square_gram_trace_pow_smul_complex c (gaussianSquareMatrix x) 1
  simp only [hScale]
  rw [integral_const_mul,
    integral_complex_ofReal (f := fun x : GaussianSquareSample n =>
      squareMatrixEnergy (gaussianSquareMatrix x)), gaussian_square_energy_integral]
  norm_cast

theorem gaussian_scaled_gram_trace_square_integrable (n : ℕ) (c : ℂ) :
    Integrable (fun x : GaussianSquareSample n =>
      (((c • gaussianSquareMatrix x) * (c • gaussianSquareMatrix x).conjTranspose) ^ 2).trace)
      (gaussianSquareMatrixLaw n) := by
  simpa [gaussianScaledMatrixWord, pow_two, Matrix.mul_assoc] using
    gaussian_scaled_matrix_word_trace_integrable n c [false, true, false, true]

theorem gaussian_scaled_gram_trace_square_integral (n : ℕ) (c : ℂ) :
    (∫ x : GaussianSquareSample n,
      (((c • gaussianSquareMatrix x) * (c • gaussianSquareMatrix x).conjTranspose) ^ 2).trace
      ∂gaussianSquareMatrixLaw n) = 2 * (‖c‖ ^ 4 : ℝ) * (n : ℂ) ^ 3 := by
  simp only [square_gram_trace_pow_smul_complex, Nat.reduceMul]
  rw [integral_const_mul, gaussian_gram_trace_square_integral]
  ring

end CircularLaw
