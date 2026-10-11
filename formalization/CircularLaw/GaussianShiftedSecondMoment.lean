import CircularLaw.GaussianEnergyConvergence
import CircularLaw.GaussianLinearSecondMoment
import CircularLaw.MatrixEnergyShiftIdentity

/-!
# Shifted Gaussian singular second moments converge

The exact matrix energy identity separates normalized raw energy from
a diagonal Gaussian linear form. Its real cross term has square mean
at most `4*|z|^2/n^2`. Thus every fixed complex shift has actual empirical
singular second moment converging to `1+|z|^2` in probability.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Matrix Topology

namespace CircularLaw

def gaussianShiftCoefficients (n : ℕ) (z : ℂ) (ij : Fin n × Fin n) : ℂ :=
  if ij.1 = ij.2 then (Real.sqrt (n : ℝ) : ℂ)⁻¹ * star z else 0

def gaussianShiftLinearForm {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) : ℂ :=
  gaussianLinearForm (gaussianShiftCoefficients n z) x

theorem gaussian_shift_linear_form_trace {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) :
    gaussianShiftLinearForm z x =
      ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x).trace * star z := by
  rw [Matrix.trace_smul]
  simp only [gaussianShiftLinearForm, gaussianLinearForm, gaussianShiftCoefficients,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, smul_eq_mul,
    Matrix.trace, Matrix.diag, gaussianSquareMatrix]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gaussian_shift_coefficient_square_sum {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∑ ij : Fin n × Fin n, ‖gaussianShiftCoefficients n z ij‖ ^ 2) = ‖z‖ ^ 2 := by
  have hCoeff (i j : Fin n) : ‖gaussianShiftCoefficients n z (i, j)‖ ^ 2 =
      if i = j then (1 / (n : ℝ)) * ‖z‖ ^ 2 else 0 := by
    by_cases hij : i = j
    · simp only [gaussianShiftCoefficients, if_pos hij, norm_mul, norm_star, mul_pow,
        inverse_sqrt_dimension_norm_sq]
    · simp [gaussianShiftCoefficients, hij]
  simp only [Fintype.sum_prod_type, hCoeff, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem gaussian_shift_linear_norm_square_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun x => ‖gaussianShiftLinearForm z x‖ ^ 2) (gaussianSquareMatrixLaw n) :=
  gaussian_linear_form_norm_square_integrable _

theorem gaussian_shift_linear_norm_square_integral {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (∫ x, ‖gaussianShiftLinearForm z x‖ ^ 2 ∂gaussianSquareMatrixLaw n) = ‖z‖ ^ 2 := by
  change (∫ x, ‖gaussianLinearForm (gaussianShiftCoefficients n z) x‖ ^ 2
    ∂standardComplexGaussianProductLaw (Fin n × Fin n)) = _
  rw [gaussian_linear_form_norm_square_integral, gaussian_shift_coefficient_square_sum hn z]

def gaussianShiftTraceCorrection {n : ℕ} (z : ℂ) (x : GaussianSquareSample n) : ℝ :=
  (2 / (n : ℝ)) * (gaussianShiftLinearForm z x).re

theorem gaussian_shift_trace_correction_square_bound {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) :
    gaussianShiftTraceCorrection z x ^ 2 ≤
      (4 / (n : ℝ) ^ 2) * ‖gaussianShiftLinearForm z x‖ ^ 2 := by
  have hRe := (sq_le_sq₀ (abs_nonneg (gaussianShiftLinearForm z x).re)
    (norm_nonneg _)).mpr (Complex.abs_re_le_norm (gaussianShiftLinearForm z x))
  rw [sq_abs] at hRe
  calc
    _ = (2 / (n : ℝ)) ^ 2 * (gaussianShiftLinearForm z x).re ^ 2 := by
      rw [gaussianShiftTraceCorrection, mul_pow]
    _ ≤ (2 / (n : ℝ)) ^ 2 * ‖gaussianShiftLinearForm z x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hRe (sq_nonneg _)
    _ = _ := by ring

theorem gaussian_shift_trace_correction_square_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun x => gaussianShiftTraceCorrection z x ^ 2) (gaussianSquareMatrixLaw n) := by
  have hMeas : Measurable (fun x : GaussianSquareSample n => gaussianShiftTraceCorrection z x ^ 2) := by
    unfold gaussianShiftTraceCorrection gaussianShiftLinearForm gaussianLinearForm
    fun_prop
  apply ((gaussian_shift_linear_norm_square_integrable n z).const_mul
    (4 / (n : ℝ) ^ 2)).mono' hMeas.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact gaussian_shift_trace_correction_square_bound z x

theorem gaussian_shift_trace_correction_square_integral_bound {n : ℕ}
    (hn : 0 < n) (z : ℂ) :
    (∫ x, gaussianShiftTraceCorrection z x ^ 2 ∂gaussianSquareMatrixLaw n) ≤
      4 * ‖z‖ ^ 2 / (n : ℝ) ^ 2 := by
  calc
    _ ≤ ∫ x, (4 / (n : ℝ) ^ 2) * ‖gaussianShiftLinearForm z x‖ ^ 2
        ∂gaussianSquareMatrixLaw n :=
      integral_mono (gaussian_shift_trace_correction_square_integrable n z)
        ((gaussian_shift_linear_norm_square_integrable n z).const_mul _)
        (gaussian_shift_trace_correction_square_bound z)
    _ = _ := by
      rw [integral_const_mul, gaussian_shift_linear_norm_square_integral hn z]
      ring

theorem gaussian_shift_trace_correction_deviation_bound {n : ℕ} (hn : 0 < n)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (gaussianSquareMatrixLaw n).real {x | ε < |gaussianShiftTraceCorrection z x|} ≤
      4 * ‖z‖ ^ 2 / ((n : ℝ) ^ 2 * ε ^ 2) := by
  let μ := gaussianSquareMatrixLaw n
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => sq_nonneg (gaussianShiftTraceCorrection z x)))
    (gaussian_shift_trace_correction_square_integrable n z) (ε ^ 2)
  have hSubset : {x : GaussianSquareSample n | ε < |gaussianShiftTraceCorrection z x|} ⊆
      {x | ε ^ 2 ≤ gaussianShiftTraceCorrection z x ^ 2} := by
    intro x hx
    change ε < |gaussianShiftTraceCorrection z x| at hx
    change ε ^ 2 ≤ gaussianShiftTraceCorrection z x ^ 2
    simpa only [sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg _)).mpr hx.le
  have hBound := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset)
    (sq_nonneg ε)).trans (hMark.trans (gaussian_shift_trace_correction_square_integral_bound hn z))
  have hεSq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hN) hεSq)).mpr
  have hScaled := mul_le_mul_of_nonneg_left hBound (sq_nonneg (n : ℝ))
  have hnR : (n : ℝ) ≠ 0 := hN.ne'
  field_simp at hScaled
  nlinarith

theorem gaussian_shift_trace_correction_converges_in_probability (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianShiftTraceCorrection z) 0 := by
  intro ε hε
  have hLimit : Tendsto (fun n : ℕ => 4 * ‖z‖ ^ 2 / ((n : ℝ) ^ 2 * ε ^ 2)) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul
      (4 * ‖z‖ ^ 2 / ε ^ 2)
    convert h using 1
    · funext n
      ring
    · simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [sub_zero] using gaussian_shift_trace_correction_deviation_bound hn z hε

theorem gaussian_shifted_second_moment_decomposition {n : ℕ} (hn : 0 < n)
    (z : ℂ) (x : GaussianSquareSample n) :
    gaussianSingularSecondMoment z x =
      gaussianNormalizedEnergy x + ‖z‖ ^ 2 - gaussianShiftTraceCorrection z x := by
  rw [gaussian_singular_second_moment_eq, normalizedShiftedGaussianMatrix,
    square_matrix_energy_shift_identity, squareMatrixEnergy_sqrt_normalization,
    ← gaussian_shift_linear_form_trace]
  unfold gaussianNormalizedEnergy gaussianShiftTraceCorrection
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem gaussian_shifted_second_moment_converges_in_probability (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianSingularSecondMoment z) (1 + ‖z‖ ^ 2) := by
  have hCentered := varying_probability_sub gaussianSquareMatrixLaw
    gaussian_normalized_energy_converges_in_probability
    (gaussian_shift_trace_correction_converges_in_probability z)
  simp only [sub_zero] at hCentered
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hCentered ε hε)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply measureReal_mono (μ := gaussianSquareMatrixLaw n)
  intro x hx
  change ε < |gaussianNormalizedEnergy x - gaussianShiftTraceCorrection z x - 1|
  change ε < |gaussianSingularSecondMoment z x - (1 + ‖z‖ ^ 2)| at hx
  rw [gaussian_shifted_second_moment_decomposition hn z x] at hx
  convert hx using 2
  ring

end CircularLaw
