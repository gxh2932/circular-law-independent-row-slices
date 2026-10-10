import CircularLaw.GaussianRegularizedLogRemoval
import CircularLaw.GaussianHermitizedZeroLimit
import CircularLaw.GaussianShiftRotation
import CircularLaw.CircularLogPotential

/-!
# The actual Gaussian logarithmic integral at every complex shift

The positive-regularization identity and the checked zero-regularization
resolvent limits evaluate the actual limiting-measure logarithmic integral.
Rotation invariance extends the real nonnegative computation to every
complex shift. The result equals the independently computed potential of
the uniform probability measure on the unit disk.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_regularized_log_formula_tendsto_zero_outside {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (gaussianRegularizedLogFormula r) (𝓝[>] 0) (𝓝 (Real.log r)) := by
  have hId : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg := gaussian_hermitized_resolvent_tendsto_zero_outside hr
  have hDen : Tendsto (fun t : ℝ => (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2)
      (𝓝[>] 0) (𝓝 (r ^ 2)) := by
    simpa using ((hId.add hg).pow 2).add_const (r ^ 2)
  have hrPos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hLog := (Real.continuousAt_log (ne_of_gt (sq_pos_of_pos hrPos))).tendsto.comp hDen
  have hF : Tendsto (gaussianRegularizedLogFormula r) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * Real.log (r ^ 2) - (1 / 2 : ℝ) * (0 : ℝ) ^ 2)) :=
    (tendsto_const_nhds.mul hLog).sub (tendsto_const_nhds.mul (hg.pow 2))
  have hValue : (1 / 2 : ℝ) * Real.log (r ^ 2) - (1 / 2 : ℝ) * (0 : ℝ) ^ 2 = Real.log r := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
    ring
  simpa only [hValue] using hF

theorem gaussian_regularized_log_formula_tendsto_zero_inside {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (gaussianRegularizedLogFormula r) (𝓝[>] 0) (𝓝 ((r ^ 2 - 1) / 2)) := by
  let a := Real.sqrt (1 - r ^ 2)
  have hRad : 0 ≤ 1 - r ^ 2 := by nlinarith
  have haSq : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hRad
  have hId : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (gaussianHermitizedResolvent r) (𝓝[>] 0) (𝓝 a) :=
    gaussian_hermitized_resolvent_tendsto_zero_inside hr0 hr1
  have hDen : Tendsto (fun t : ℝ => (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2)
      (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => (t + gaussianHermitizedResolvent r t) ^ 2 + r ^ 2)
        (𝓝[>] 0) (𝓝 ((0 + a) ^ 2 + r ^ 2)) := ((hId.add hg).pow 2).add_const (r ^ 2)
    rwa [zero_add, haSq, sub_add_cancel] at h
  have hLog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hDen
  have hF : Tendsto (gaussianRegularizedLogFormula r) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * Real.log 1 - (1 / 2 : ℝ) * a ^ 2)) :=
    (tendsto_const_nhds.mul hLog).sub (tendsto_const_nhds.mul (hg.pow 2))
  have hValue : (1 / 2 : ℝ) * Real.log 1 - (1 / 2 : ℝ) * a ^ 2 = (r ^ 2 - 1) / 2 := by
    rw [Real.log_one, haSq]
    ring
  simpa only [hValue] using hF

theorem gaussian_real_shift_log_integral_value_inside {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit (r : ℂ)) = (r ^ 2 - 1) / 2 := by
  apply tendsto_nhds_unique (gaussian_regularized_log_tendsto_zero r)
  apply (gaussian_regularized_log_formula_tendsto_zero_inside hr0 hr1).congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact (gaussian_regularized_log_value r ht).symm

theorem gaussian_real_shift_log_integral_value_outside {r : ℝ} (hr : 1 ≤ r) :
    (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit (r : ℂ)) = Real.log r := by
  apply tendsto_nhds_unique (gaussian_regularized_log_tendsto_zero r)
  apply (gaussian_regularized_log_formula_tendsto_zero_outside hr).congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact (gaussian_regularized_log_value r ht).symm

theorem gaussian_real_shift_log_integral_value {r : ℝ} (hr : 0 ≤ r) :
    (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit (r : ℂ)) =
      if r ≤ 1 then (r ^ 2 - 1) / 2 else Real.log r := by
  by_cases hlt : r < 1
  · rw [if_pos hlt.le]
    exact gaussian_real_shift_log_integral_value_inside hr hlt
  · have hge : 1 ≤ r := le_of_not_gt hlt
    rw [gaussian_real_shift_log_integral_value_outside hge]
    by_cases heq : r = 1
    · subst r
      norm_num
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne hge (Ne.symm heq)))]

theorem gaussian_shifted_log_integral_value (z : ℂ) :
    (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit z) =
      if ‖z‖ ≤ 1 then (‖z‖ ^ 2 - 1) / 2 else Real.log ‖z‖ := by
  rw [gaussian_shifted_limit_eq_real_norm z]
  exact gaussian_real_shift_log_integral_value (norm_nonneg z)

theorem gaussian_shifted_log_integral_eq_circular (z : ℂ) :
    (∫ s, Real.log (s : ℝ) ∂gaussianShiftedSingularLimit z) = circularLogPotential z := by
  rw [gaussian_shifted_log_integral_value, circular_log_potential_formula]

end CircularLaw
