import CircularLaw.GaussianRegularizedLogValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing logarithmic regularization at the actual Gaussian limit

Finite logarithmic integrability includes no mass at zero. Compact
support and that integrability give a fixed bound by the absolute
ordinary logarithm plus a constant. Dominated convergence recovers the
actual logarithmic integral as the positive regularization tends to zero.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

theorem regularized_singular_log_kernel_small_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {R : ℝ} {s : ℝ≥0} (hs0 : 0 < (s : ℝ)) (hsR : (s : ℝ) ≤ R) :
    ‖regularizedSingularLogKernel t s‖ ≤
      |Real.log (s : ℝ)| + (1 / 2 : ℝ) * Real.log (1 + R ^ 2) := by
  have hLower : Real.log (s : ℝ) ≤ regularizedSingularLogKernel t s := by
    have h := Real.log_le_log (sq_pos_of_pos hs0)
      (by nlinarith [sq_nonneg t] : (s : ℝ) ^ 2 ≤ t ^ 2 + (s : ℝ) ^ 2)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    dsimp [regularizedSingularLogKernel]
    linarith
  have hUpper : regularizedSingularLogKernel t s ≤ (1 / 2 : ℝ) * Real.log (1 + R ^ 2) := by
    have ht2 : t ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ ht.le ht1 2
    have hs2 : (s : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ s.property hsR 2
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (add_le_add ht2 hs2))
      (by norm_num)
  have hConst : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + R ^ 2) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg R]))
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (s : ℝ))]
  · linarith [abs_nonneg (Real.log (s : ℝ))]

theorem regularized_singular_log_kernel_tendsto {s : ℝ≥0} (hs : 0 < (s : ℝ)) :
    Tendsto (fun t : ℝ => regularizedSingularLogKernel t s) (𝓝[>] 0) (𝓝 (Real.log (s : ℝ))) := by
  have hId : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hSquare : Tendsto (fun t : ℝ => t ^ 2 + (s : ℝ) ^ 2)
      (𝓝[>] 0) (𝓝 ((s : ℝ) ^ 2)) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using (hId.pow 2).add_const ((s : ℝ) ^ 2)
  have hLog := (Real.continuousAt_log (ne_of_gt (sq_pos_of_pos hs))).tendsto.comp hSquare
  have hHalf : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log (t ^ 2 + (s : ℝ) ^ 2))
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * Real.log ((s : ℝ) ^ 2))) := tendsto_const_nhds.mul hLog
  have hValue : (1 / 2 : ℝ) * Real.log ((s : ℝ) ^ 2) = Real.log (s : ℝ) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rwa [hValue] at hHalf

theorem regularized_log_integral_tendsto_zero (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (R : ℝ) (hSupport : ∀ᵐ (s : ℝ≥0) ∂ν, (s : ℝ) ≤ R)
    (hLog : FiniteLogarithmicIntegral ν) :
    Tendsto (fun t : ℝ => ∫ s, regularizedSingularLogKernel t s ∂ν) (𝓝[>] 0)
      (𝓝 (∫ s, Real.log (s : ℝ) ∂ν)) := by
  have hPos : ∀ᵐ (s : ℝ≥0) ∂ν, 0 < (s : ℝ) := by
    simpa only [NNReal.coe_pos] using finiteLogarithmicIntegral_ae_pos hLog
  apply tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ≥0 => |Real.log (s : ℝ)| + (1 / 2 : ℝ) * Real.log (1 + R ^ 2))
  · exact Eventually.of_forall (fun t =>
      (regularized_singular_log_kernel_measurable t).aestronglyMeasurable)
  · filter_upwards [eventually_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with t ht ht1
    exact (hPos.and hSupport).mono (fun s hs =>
      regularized_singular_log_kernel_small_bound ht ht1.le hs.1 hs.2)
  · simpa only [Real.norm_eq_abs] using hLog.2.norm.add (integrable_const _)
  · exact hPos.mono (fun _ hs => regularized_singular_log_kernel_tendsto hs)

theorem gaussian_regularized_log_tendsto_zero (r : ℝ) :
    Tendsto (gaussianRegularizedLog r) (𝓝[>] 0)
      (𝓝 (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit (r : ℂ))) :=
  regularized_log_integral_tendsto_zero (gaussianShiftedSingularLimit (r : ℂ))
    (128 + ‖(r : ℂ)‖) (gaussian_shifted_limit_support_ae (r : ℂ))
    (gaussian_shifted_limit_finite_logarithmic_integral (r : ℂ))

end CircularLaw
