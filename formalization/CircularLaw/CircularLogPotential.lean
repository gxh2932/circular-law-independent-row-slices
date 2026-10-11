import CircularLaw.CircularPotentialPolar
import CircularLaw.RadialCircularPotential

/-!
# The actual logarithmic potential of the circular measure

The integral is taken against the paper's uniform area measure on the
closed unit disk. The formulas hold at every point, including the origin
and unit circle. The manuscript uses the negative of this logarithmic
potential, so its sign is recorded separately.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CircularLaw

instance circularMeasureProbability : IsProbabilityMeasure circularMeasure :=
  ⟨circularMeasure_univ⟩

theorem circular_measure_ae_unit_disk :
    ∀ᵐ w : ℂ ∂circularMeasure, w ∈ Metric.closedBall 0 1 := by
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

def circularLogPotential (z : ℂ) : ℝ :=
  ∫ w : ℂ, Real.log ‖z - w‖ ∂circularMeasure

/-- `U^circ` in Section 9 of the manuscript. -/
def circularPaperPotential (z : ℂ) : ℝ := -circularLogPotential z

theorem circular_log_kernel_integrable (z : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖z - w‖) circularMeasure := by
  have hInt : IntegrableOn (fun w : ℂ => Real.log ‖z - w‖)
      (Metric.closedBall 0 1) volume := by
    simpa only [norm_sub_rev] using
      planar_log_kernel_integrableOn_closedBall z (by norm_num : (0 : ℝ) < 1)
  exact hInt.smul_measure (by
    rw [ENNReal.inv_ne_top]
    exact (ENNReal.ofReal_pos.mpr Real.pi_pos).ne')

theorem circular_log_potential_radial (z : ℂ) :
    circularLogPotential z =
      2 * ∫ r : ℝ in Ioc 0 1, r * Real.log (max r ‖z‖) := by
  rw [circularLogPotential, circularMeasure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul,
    unit_disk_log_kernel_integral_polar]
  field_simp

theorem circular_log_potential_inside {z : ℂ} (hz : ‖z‖ ≤ 1) :
    circularLogPotential z = (‖z‖ ^ 2 - 1) / 2 := by
  rw [circular_log_potential_radial,
    radial_log_max_integral_inside (norm_nonneg z) hz]
  ring

theorem circular_log_potential_outside {z : ℂ} (hz : 1 ≤ ‖z‖) :
    circularLogPotential z = Real.log ‖z‖ := by
  rw [circular_log_potential_radial, radial_log_max_integral_outside hz]
  ring

theorem circular_log_potential_formula (z : ℂ) :
    circularLogPotential z =
      if ‖z‖ ≤ 1 then (‖z‖ ^ 2 - 1) / 2 else Real.log ‖z‖ := by
  split_ifs with hz
  · exact circular_log_potential_inside hz
  · exact circular_log_potential_outside (le_of_lt (lt_of_not_ge hz))

theorem circular_paper_potential_formula (z : ℂ) :
    circularPaperPotential z =
      if ‖z‖ ≤ 1 then (1 - ‖z‖ ^ 2) / 2 else -Real.log ‖z‖ := by
  rw [circularPaperPotential, circular_log_potential_formula]
  split_ifs <;> ring

theorem circular_log_potential_global_expression (z : ℂ) :
    circularLogPotential z =
      ((min ‖z‖ 1) ^ 2 - 1) / 2 + Real.log (max ‖z‖ 1) := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [circular_log_potential_inside hz, min_eq_left hz, max_eq_right hz,
      Real.log_one, add_zero]
  · have hz' : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
    rw [circular_log_potential_outside hz', min_eq_right hz', max_eq_left hz']
    norm_num

theorem circular_log_potential_continuous : Continuous circularLogPotential := by
  have hFormula : circularLogPotential = fun z : ℂ =>
      ((min ‖z‖ 1) ^ 2 - 1) / 2 + Real.log (max ‖z‖ 1) :=
    funext circular_log_potential_global_expression
  rw [hFormula]
  apply (((continuous_norm.min continuous_const).pow 2).sub continuous_const).div_const _ |>.add
  exact (continuous_norm.max continuous_const).log
    (fun z => (zero_lt_one.trans_le (le_max_right ‖z‖ 1)).ne')

theorem circular_paper_potential_continuous : Continuous circularPaperPotential :=
  circular_log_potential_continuous.neg

theorem circular_log_potential_locallyIntegrable :
    LocallyIntegrable circularLogPotential volume :=
  circular_log_potential_continuous.locallyIntegrable

theorem circular_log_potential_squared_locallyIntegrable :
    LocallyIntegrable (fun z : ℂ => (circularLogPotential z) ^ 2) volume :=
  (circular_log_potential_continuous.pow 2).locallyIntegrable

theorem circular_log_potential_absolute_bound (z : ℂ) :
    |circularLogPotential z| ≤ ‖z‖ + 1 := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [circular_log_potential_inside hz]
    have hzSq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [abs_of_nonpos (by linarith : (‖z‖ ^ 2 - 1) / 2 ≤ 0)]
    nlinarith [sq_nonneg ‖z‖, norm_nonneg z]
  · have hz' : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
    rw [circular_log_potential_outside hz', abs_of_nonneg (Real.log_nonneg hz')]
    linarith [Real.log_le_self (norm_nonneg z)]

theorem circular_log_potential_square_bound (z : ℂ) :
    (circularLogPotential z) ^ 2 ≤ 2 * (‖z‖ ^ 2 + 1) := by
  have h := pow_le_pow_left₀ (abs_nonneg (circularLogPotential z))
    (circular_log_potential_absolute_bound z) 2
  rw [sq_abs] at h
  nlinarith [sq_nonneg (‖z‖ - 1)]

theorem circular_log_potential_squared_integral_disk_bound (R : ℝ) :
    (∫ z : ℂ in Metric.closedBall 0 R, (circularLogPotential z) ^ 2) ≤
      2 * (R ^ 2 + 1) * volume.real (Metric.closedBall (0 : ℂ) R) := by
  have hConst : IntegrableOn (fun _ : ℂ => 2 * (R ^ 2 + 1))
      (Metric.closedBall 0 R) volume :=
    integrableOn_const ((isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne)
  have hBound : (∫ z : ℂ in Metric.closedBall 0 R, (circularLogPotential z) ^ 2) ≤
      ∫ _ : ℂ in Metric.closedBall 0 R, 2 * (R ^ 2 + 1) := by
    apply setIntegral_mono_on
      (circular_log_potential_squared_locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R)) hConst measurableSet_closedBall
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hzSq := pow_le_pow_left₀ (norm_nonneg z) hzR 2
    exact (circular_log_potential_square_bound z).trans (by linarith)
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hBound

end CircularLaw
