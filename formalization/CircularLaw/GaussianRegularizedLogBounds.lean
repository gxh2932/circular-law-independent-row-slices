import CircularLaw.GaussianRegularizedLogDerivative

/-!
# Normalization of the actual regularized logarithm at infinity

The exact logarithmic factorization gives a nonnegative difference from
log(t), bounded by the squared support radius divided by 2*t^2. Thus the
actual regularized logarithmic integral minus log(t) tends to zero. The
actual Hermitized resolvent also tends to zero at infinity.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem regularized_singular_log_kernel_difference {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    regularizedSingularLogKernel t s - Real.log t =
      (1 / 2 : ℝ) * Real.log (1 + (s : ℝ) ^ 2 / t ^ 2) := by
  have hFactor : t ^ 2 + (s : ℝ) ^ 2 = t ^ 2 * (1 + (s : ℝ) ^ 2 / t ^ 2) := by
    field_simp [ne_of_gt ht]
  have hPos : 0 < 1 + (s : ℝ) ^ 2 / t ^ 2 := by positivity
  rw [regularizedSingularLogKernel, hFactor,
    Real.log_mul (ne_of_gt (sq_pos_of_pos ht)) (ne_of_gt hPos), Real.log_pow]
  ring

theorem regularized_singular_log_kernel_difference_bounds {t : ℝ} (ht : 0 < t) (s : ℝ≥0) :
    0 ≤ regularizedSingularLogKernel t s - Real.log t ∧
      regularizedSingularLogKernel t s - Real.log t ≤ (s : ℝ) ^ 2 / (2 * t ^ 2) := by
  rw [regularized_singular_log_kernel_difference ht s]
  have hRatio : 0 ≤ (s : ℝ) ^ 2 / t ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  · have hLog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (s : ℝ) ^ 2 / t ^ 2)
    calc
      _ ≤ (1 / 2 : ℝ) * ((s : ℝ) ^ 2 / t ^ 2) := by linarith
      _ = _ := by ring

theorem gaussian_regularized_log_difference_bounds (r : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gaussianRegularizedLog r t - Real.log t ∧
      gaussianRegularizedLog r t - Real.log t ≤ (128 + ‖(r : ℂ)‖) ^ 2 / (2 * t ^ 2) := by
  have hInt := regularized_singular_log_kernel_integrable (gaussianShiftedSingularLimit (r : ℂ))
    (128 + ‖(r : ℂ)‖) (gaussian_shifted_limit_support_ae (r : ℂ)) ht
  have hDiff : (∫ s, (regularizedSingularLogKernel t s - Real.log t)
      ∂gaussianShiftedSingularLimit (r : ℂ)) = gaussianRegularizedLog r t - Real.log t := by
    rw [integral_sub hInt (integrable_const _)]
    simp [gaussianRegularizedLog]
  rw [← hDiff]
  constructor
  · exact integral_nonneg (fun s => (regularized_singular_log_kernel_difference_bounds ht s).1)
  · calc
      _ ≤ ∫ _ : ℝ≥0, (128 + ‖(r : ℂ)‖) ^ 2 / (2 * t ^ 2)
          ∂gaussianShiftedSingularLimit (r : ℂ) := by
        apply integral_mono_ae (hInt.sub (integrable_const _)) (integrable_const _)
        exact (gaussian_shifted_limit_support_ae (r : ℂ)).mono (fun s hs =>
          (regularized_singular_log_kernel_difference_bounds ht s).2.trans
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ s.property hs 2) (by positivity)))
      _ = _ := by simp

theorem gaussian_regularized_log_normalization_atTop (r : ℝ) :
    Tendsto (fun t : ℝ => gaussianRegularizedLog r t - Real.log t) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun t : ℝ => (128 + ‖(r : ℂ)‖) ^ 2 / (2 * t ^ 2)) atTop (𝓝 0) := by
    have hInv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => (128 + ‖(r : ℂ)‖) ^ 2 / 2) atTop
      (𝓝 ((128 + ‖(r : ℂ)‖) ^ 2 / 2))).mul (hInv.pow 2)
    have hFun : (fun t : ℝ => ((128 + ‖(r : ℂ)‖) ^ 2 / 2) * (t⁻¹) ^ 2) =
        (fun t : ℝ => (128 + ‖(r : ℂ)‖) ^ 2 / (2 * t ^ 2)) := by
      funext t
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    rw [hFun] at h
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using h
  apply squeeze_zero'
    ((eventually_gt_atTop 0).mono (fun t ht => (gaussian_regularized_log_difference_bounds r ht).1))
    ((eventually_gt_atTop 0).mono (fun t ht => (gaussian_regularized_log_difference_bounds r ht).2)) hUpper

theorem gaussian_hermitized_resolvent_tendsto_atTop (r : ℝ) :
    Tendsto (gaussianHermitizedResolvent r) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  exact squeeze_zero'
    ((eventually_gt_atTop 0).mono (fun t ht => (gaussian_hermitized_resolvent_pos r ht).le))
    ((eventually_gt_atTop 0).mono (fun t ht => gaussian_hermitized_resolvent_bound r ht)) hUpper

end CircularLaw
