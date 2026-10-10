import CircularLaw.GaussianScaledGramMoments
import CircularLaw.GaussianTracePolynomials

/-!
# Exact shifted Gaussian fourth singular moment

The deterministic Gram-square expansion is integrated under the actual
independent complex Gaussian matrix law. All six unbalanced words vanish.
The normalized fourth singular moment has mean `2+4*|z|^2+|z|^4` at every
positive dimension. This is a finite mean identity, not a limit assertion.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

theorem gaussian_scaled_shifted_gram_trace_square_integral (n : ℕ) (c z : ℂ) :
    (∫ x : GaussianSquareSample n,
      ((((c • gaussianSquareMatrix x) - z • 1) *
        ((c • gaussianSquareMatrix x) - z • 1).conjTranspose) ^ 2).trace
      ∂gaussianSquareMatrixLaw n) =
      2 * (‖c‖ ^ 4 : ℝ) * (n : ℂ) ^ 3 +
      4 * (z * star z) * (‖c‖ ^ 2 : ℝ) * (n : ℂ) ^ 2 +
      (z * star z) ^ 2 * n := by
  let words : Fin 9 → List Bool :=
    ![[false, true, false, true], [false, false], [true, true], [],
      [false, true, false], [false, true, true], [false, true], [false], [true]]
  let coeff : Fin 9 → ℂ :=
    ![1, star z ^ 2, z ^ 2, (z * star z) ^ 2, -2 * star z, -2 * z,
      4 * (z * star z), -2 * (z * star z) * star z, -2 * (z * star z) * z]
  have hExpand (x : GaussianSquareSample n) :
      ((((c • gaussianSquareMatrix x) - z • 1) *
        ((c • gaussianSquareMatrix x) - z • 1).conjTranspose) ^ 2).trace =
      ∑ i : Fin 9, coeff i * (gaussianScaledMatrixWord c (words i) x).trace := by
    rw [square_gram_shift_trace_square]
    simp [words, coeff, Fin.sum_univ_succ, gaussianScaledMatrixWord,
      pow_two, Matrix.mul_assoc]
    ring
  have hInt (i : Fin 9) : Integrable (fun x : GaussianSquareSample n =>
      coeff i * (gaussianScaledMatrixWord c (words i) x).trace) (gaussianSquareMatrixLaw n) :=
    (gaussian_scaled_matrix_word_trace_integrable n c (words i)).const_mul (coeff i)
  have hBalancedFour :
      (∫ x : GaussianSquareSample n,
        (gaussianScaledMatrixWord c [false, true, false, true] x).trace
        ∂gaussianSquareMatrixLaw n) = 2 * (‖c‖ ^ 4 : ℝ) * (n : ℂ) ^ 3 := by
    simpa [gaussianScaledMatrixWord, pow_two, Matrix.mul_assoc] using
      gaussian_scaled_gram_trace_square_integral n c
  have hBalancedTwo :
      (∫ x : GaussianSquareSample n, (gaussianScaledMatrixWord c [false, true] x).trace
        ∂gaussianSquareMatrixLaw n) = (‖c‖ ^ 2 : ℝ) * (n : ℂ) ^ 2 := by
    simpa [gaussianScaledMatrixWord] using gaussian_scaled_gram_trace_integral n c
  have hEmpty :
      (∫ x : GaussianSquareSample n, (gaussianScaledMatrixWord c [] x).trace
        ∂gaussianSquareMatrixLaw n) = n := by
    simp [gaussianScaledMatrixWord, Matrix.trace_one]
  have hZero (w : List Bool) (hw : gaussianMatrixWordImbalance w ≠ 0) :
      (∫ x : GaussianSquareSample n, (gaussianScaledMatrixWord c w x).trace
        ∂gaussianSquareMatrixLaw n) = 0 :=
    gaussian_scaled_matrix_word_trace_integral_zero n c w hw
  simp only [hExpand]
  rw [integral_finset_sum _ (fun i _ => hInt i)]
  simp only [integral_const_mul]
  simp only [Fin.sum_univ_succ, words, coeff, Matrix.cons_val_zero,
    Matrix.cons_val_succ, hBalancedFour, hBalancedTwo, hEmpty,
    hZero [false, false] (by norm_num [gaussianMatrixWordImbalance]),
    hZero [true, true] (by norm_num [gaussianMatrixWordImbalance]),
    hZero [false, true, false] (by norm_num [gaussianMatrixWordImbalance]),
    hZero [false, true, true] (by norm_num [gaussianMatrixWordImbalance]),
    hZero [false] (by norm_num [gaussianMatrixWordImbalance]),
    hZero [true] (by norm_num [gaussianMatrixWordImbalance])]
  ring

theorem gaussian_shifted_gram_trace_square_integral {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∫ x : GaussianSquareSample n,
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ 2).trace
      ∂gaussianSquareMatrixLaw n) =
      (n : ℂ) * (2 + 4 * (‖z‖ ^ 2 : ℝ) + (‖z‖ ^ 4 : ℝ)) := by
  simp only [normalizedShiftedGaussianMatrix]
  rw [gaussian_scaled_shifted_gram_trace_square_integral]
  have hz : z * star z = (‖z‖ ^ 2 : ℝ) := by
    simpa using complex_balanced_power_eq_norm_power z 1
  have hNorm : ‖(Real.sqrt (n : ℝ) : ℂ)⁻¹‖ ^ 4 = (1 / (n : ℝ)) ^ 2 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, inverse_sqrt_dimension_norm_sq]
  rw [hNorm, inverse_sqrt_dimension_norm_sq, hz]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

theorem gaussian_shifted_singular_fourth_moment_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun x => ∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure z x)
      (gaussianSquareMatrixLaw n) := by
  simpa using gaussian_shifted_singular_even_moment_integrable n z 2

theorem gaussian_shifted_singular_fourth_moment_integral {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∫ x, (∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure z x) ∂gaussianSquareMatrixLaw n) =
      2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4 := by
  have hMoment (x : GaussianSquareSample n) := gaussian_shifted_singular_even_moment_trace z 2 x
  norm_num only [Nat.reduceMul] at hMoment
  simp only [hMoment]
  rw [integral_div]
  change (∫ x, RCLike.re ((normalizedShiftedGaussianMatrix z x *
    (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ 2).trace
    ∂gaussianSquareMatrixLaw n) / n = _
  rw [integral_re (gaussian_shifted_gram_trace_pow_integrable n z 2),
    gaussian_shifted_gram_trace_square_integral hn z]
  change ((n : ℂ) * (2 + 4 * (‖z‖ ^ 2 : ℝ) + (‖z‖ ^ 4 : ℝ))).re / n = _
  norm_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end CircularLaw
