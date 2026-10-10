import CircularLaw.LogarithmicNetCost

/-!
# Iterated logarithms compared with powers of the dimension logarithm

The little-o estimate is composed with the actual dimension logarithm.
The resulting dimension threshold is uniform in a degree bounded above
by that dimension.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_loglog_power_dimension_budget {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (B b : ℝ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, B + b * Real.log (Real.log (n : ℝ)) ≤
      r * (Real.log (n : ℝ)) ^ κ := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hGrowth : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ κ) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp hLog
  have hRatio : Tendsto (fun n : ℕ =>
      Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ κ) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero.comp hLog
  filter_upwards [hLog.eventually_ge_atTop 1, hGrowth.eventually_ge_atTop (2 * B / r),
    hRatio.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / (2 * b)))]
      with n hLogOne hLarge hSmall
  change 1 ≤ Real.log (n : ℝ) at hLogOne
  have hPower : 0 < (Real.log (n : ℝ)) ^ κ := Real.rpow_pos_of_pos (by linarith) _
  have hConst := (div_le_iff₀ hr).mp hLarge
  have hScaled := (div_lt_iff₀ hPower).mp hSmall
  have hScaled' := mul_le_mul_of_nonneg_left hScaled.le hb.le
  field_simp at hScaled'
  nlinarith only [hConst, hScaled', hr, hb]

end CircularLaw
