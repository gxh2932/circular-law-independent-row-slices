import CircularLaw.GaussianWeakLimitSmallValues
import CircularLaw.GaussianWeakLimitSupport
import CircularLaw.GaussianZeroWeakLimit
import CircularLaw.SmallValueLogIntegrability

/-!
# Actual Gaussian weak limits have finite logarithmic integrals

The proved linear small-value mass bound excludes an atom at zero and
gives an integrable negative logarithm. The proved upper support bound
gives an integrable positive logarithm. At zero shift the constructed
weak law supplies every input, so its finite logarithmic integral is
unconditional. Identification with the circular potential is still open.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

theorem gaussian_shifted_weak_limit_zero_atom (z : ℂ) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν) :
    ν {0} = 0 := zero_mass_of_linear_small_value_bound ν (by norm_num : (0 : ℝ) < 48)
      (fun _ ht => gaussian_shifted_weak_limit_small_mass z ν hWeak ht)

theorem gaussian_shifted_weak_limit_negative_log_integrable (z : ℂ) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν) :
    Integrable hermitizationNegativeLog ν ∧ (∫ t, hermitizationNegativeLog t ∂ν) ≤ 96 := by
  simpa only [show (2 : ℝ) * 48 = 96 from by norm_num] using
    negative_log_integrable_of_linear_mass ν (by norm_num : (0 : ℝ) < 48)
      (fun _ ht => gaussian_shifted_weak_limit_small_mass z ν hWeak ht)

theorem gaussian_shifted_weak_limit_finite_logarithmic_integral (z : ℂ) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν) :
    FiniteLogarithmicIntegral ν := finite_logarithmic_integral_of_mass_and_support ν
      (by norm_num : (0 : ℝ) < 48)
      (fun _ ht => gaussian_shifted_weak_limit_small_mass z ν hWeak ht)
      (128 + ‖z‖) (gaussian_shifted_weak_limit_support z ν hWeak)

theorem gaussian_zero_shift_limit_small_mass {t : ℝ} (ht : 0 < t) :
    gaussianZeroShiftSingularLimit.real {r : ℝ≥0 | (r : ℝ) < t} ≤ 48 * t :=
  gaussian_shifted_weak_limit_small_mass 0 gaussianZeroShiftSingularLimit
    gaussian_zero_shift_weak_convergence ht

theorem gaussian_zero_shift_limit_zero_atom : gaussianZeroShiftSingularLimit {0} = 0 :=
  gaussian_shifted_weak_limit_zero_atom 0 gaussianZeroShiftSingularLimit gaussian_zero_shift_weak_convergence

theorem gaussian_zero_shift_limit_negative_log_integrable :
    Integrable hermitizationNegativeLog gaussianZeroShiftSingularLimit ∧
      (∫ t, hermitizationNegativeLog t ∂gaussianZeroShiftSingularLimit) ≤ 96 :=
  gaussian_shifted_weak_limit_negative_log_integrable 0 gaussianZeroShiftSingularLimit
    gaussian_zero_shift_weak_convergence

theorem gaussian_zero_shift_limit_finite_logarithmic_integral :
    FiniteLogarithmicIntegral gaussianZeroShiftSingularLimit :=
  gaussian_shifted_weak_limit_finite_logarithmic_integral 0 gaussianZeroShiftSingularLimit
    gaussian_zero_shift_weak_convergence

end CircularLaw
