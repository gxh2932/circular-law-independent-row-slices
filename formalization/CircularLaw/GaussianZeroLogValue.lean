import CircularLaw.GaussianZeroBetaProperties
import CircularLaw.BetaHalfLogMoment
import CircularLaw.CircularLogPotential

/-!
# The actual zero-shift Gaussian logarithmic value

The identified beta law has logarithmic integral -1/2, which agrees with
the circular logarithmic potential at zero. Both existing constructions
of the actual Gaussian singular limit have this value.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem beta_half_log_integral_value :
    (∫ x, Real.log x ∂gaussianZeroBetaBase) = -2 * Real.log 2 - 1 :=
  beta_half_log_measure_integral

theorem gaussian_zero_shift_log_integral_value :
    (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) = -(1 / 2 : ℝ) := by
  rw [gaussian_zero_shift_log_integral_beta_log_moment, beta_half_log_integral_value]
  ring

theorem gaussian_previous_zero_log_integral_value :
    (∫ t, Real.log (t : ℝ) ∂gaussianZeroShiftSingularLimit) = -(1 / 2 : ℝ) := by
  rw [← gaussian_shifted_limit_at_zero]
  exact gaussian_zero_shift_log_integral_value

theorem gaussian_zero_shift_log_integral_eq_circular :
    (∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) = circularLogPotential 0 := by
  rw [gaussian_zero_shift_log_integral_value, circular_log_potential_inside (by simp)]
  norm_num

theorem gaussian_zero_shift_negative_log_integral_eq_circular :
    -(∫ t, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit 0) = circularPaperPotential 0 := by
  rw [circularPaperPotential, gaussian_zero_shift_log_integral_eq_circular]

end CircularLaw
