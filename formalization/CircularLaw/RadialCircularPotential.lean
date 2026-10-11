import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The radial integral of the unit disk logarithmic potential

The primitive is continuous at zero. This proves the inside and outside
formulas without omitting the origin or the unit-circle boundary.
-/

noncomputable section
open MeasureTheory Set

namespace CircularLaw

theorem radial_log_primitive_continuous :
    Continuous (fun r : ℝ => (r / 2) * (r * Real.log r) - r ^ 2 / 4) := by
  exact ((continuous_id.div_const 2).mul Real.continuous_mul_log).sub
    ((continuous_id.pow 2).div_const 4)

theorem radial_log_primitive_hasDerivAt {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => (s / 2) * (s * Real.log s) - s ^ 2 / 4)
      (r * Real.log r) r := by
  convert (((hasDerivAt_id r).div_const 2).mul (Real.hasDerivAt_mul_log hr)).sub
    (((hasDerivAt_id r).pow 2).div_const 4) using 1
  simp only [id_eq]
  ring

theorem radial_log_integral_from_zero {b : ℝ} (hb : 0 ≤ b) :
    (∫ r : ℝ in (0 : ℝ)..b, r * Real.log r) =
      (b ^ 2 / 2) * Real.log b - b ^ 2 / 4 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    radial_log_primitive_continuous.continuousOn
    (fun r hr => radial_log_primitive_hasDerivAt hr.1.ne')
    (Real.continuous_mul_log.intervalIntegrable (μ := volume) 0 b)
  simp only [zero_div, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at h
  convert h using 1
  ring

theorem radial_log_integral_between {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ r : ℝ in a..b, r * Real.log r) =
      ((b ^ 2 / 2) * Real.log b - b ^ 2 / 4) -
        ((a ^ 2 / 2) * Real.log a - a ^ 2 / 4) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (Real.continuous_mul_log.intervalIntegrable (μ := volume) 0 a)
    (Real.continuous_mul_log.intervalIntegrable (μ := volume) a b)
  rw [radial_log_integral_from_zero ha, radial_log_integral_from_zero hb] at h
  linarith

theorem radial_log_max_integral_inside {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ r : ℝ in Ioc 0 1, r * Real.log (max r a)) = (a ^ 2 - 1) / 4 := by
  by_cases ha0 : a = 0
  · subst a
    calc
      _ = ∫ r : ℝ in Ioc 0 1, r * Real.log r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        dsimp only
        rw [max_eq_left hr.1.le]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          radial_log_integral_from_zero (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hCont : Continuous (fun r : ℝ => r * Real.log (max r a)) :=
    continuous_id.mul ((continuous_id.max continuous_const).log
      (fun r => (haPos.trans_le (le_max_right r a)).ne'))
  have hLower : (∫ r : ℝ in (0 : ℝ)..a, r * Real.log (max r a)) =
      (a ^ 2 / 2) * Real.log a := by
    calc
      _ = ∫ r : ℝ in (0 : ℝ)..a, r * Real.log a := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc 0 a := by simpa only [uIcc_of_le ha] using hr
        dsimp only
        rw [max_eq_right hr'.2]
      _ = _ := by rw [intervalIntegral.integral_mul_const, integral_id]; simp
  have hUpper : (∫ r : ℝ in a..1, r * Real.log (max r a)) =
      (-1 / 4 : ℝ) - ((a ^ 2 / 2) * Real.log a - a ^ 2 / 4) := by
    calc
      _ = ∫ r : ℝ in a..1, r * Real.log r := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc a 1 := by simpa only [uIcc_of_le ha1] using hr
        dsimp only
        rw [max_eq_left hr'.1]
      _ = _ := by
        rw [radial_log_integral_between ha (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
  have hSum := intervalIntegral.integral_add_adjacent_intervals
    (hCont.intervalIntegrable (μ := volume) 0 a) (hCont.intervalIntegrable (μ := volume) a 1)
  rw [hLower, hUpper, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hSum
  linarith

theorem radial_log_max_integral_outside {a : ℝ} (ha : 1 ≤ a) :
    (∫ r : ℝ in Ioc 0 1, r * Real.log (max r a)) = (1 / 2) * Real.log a := by
  calc
    _ = ∫ r : ℝ in Ioc 0 1, r * Real.log a := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      dsimp only
      rw [max_eq_right (hr.2.trans ha)]
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_mul_const, integral_id]
      norm_num

end CircularLaw
