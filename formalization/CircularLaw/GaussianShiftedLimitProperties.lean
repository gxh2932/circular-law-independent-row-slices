import CircularLaw.GaussianShiftedWeakLimit
import CircularLaw.GaussianWeakLimitLogIntegrability
import CircularLaw.GaussianShiftedSecondMoment
import CircularLaw.GaussianShiftedFourthMoment

/-!
# Unconditional properties of every actual shifted Gaussian limit

The constructed weak law supplies the missing input to the checked
quantile and logarithmic-integrability consequences. Thus every shift
has a unique probability limit with linear mass near zero, no zero atom,
finite logarithmic integral and the exact second moment `1 + norm z^2`.
Identification of that logarithmic integral with the circular potential
is still a distinct obligation.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_shifted_limit_small_mass (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (gaussianShiftedSingularLimit z).real {r : ℝ≥0 | (r : ℝ) < t} ≤ 48 * t :=
  gaussian_shifted_weak_limit_small_mass z (gaussianShiftedSingularLimit z)
    (gaussian_shifted_weak_convergence z) ht

theorem gaussian_shifted_limit_zero_atom (z : ℂ) :
    gaussianShiftedSingularLimit z {0} = 0 :=
  gaussian_shifted_weak_limit_zero_atom z (gaussianShiftedSingularLimit z)
    (gaussian_shifted_weak_convergence z)

theorem gaussian_shifted_limit_negative_log_integrable (z : ℂ) :
    Integrable hermitizationNegativeLog (gaussianShiftedSingularLimit z) ∧
      (∫ t, hermitizationNegativeLog t ∂gaussianShiftedSingularLimit z) ≤ 96 :=
  gaussian_shifted_weak_limit_negative_log_integrable z (gaussianShiftedSingularLimit z)
    (gaussian_shifted_weak_convergence z)

theorem gaussian_shifted_limit_finite_logarithmic_integral (z : ℂ) :
    FiniteLogarithmicIntegral (gaussianShiftedSingularLimit z) :=
  gaussian_shifted_weak_limit_finite_logarithmic_integral z (gaussianShiftedSingularLimit z)
    (gaussian_shifted_weak_convergence z)

theorem gaussian_shifted_limit_log_integrable (z : ℂ) :
    Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) (gaussianShiftedSingularLimit z) :=
  (gaussian_shifted_limit_finite_logarithmic_integral z).2

theorem gaussian_shifted_squared_moment_limit_one (z : ℂ) :
    gaussianShiftedSquaredMomentLimit z 1 = 1 + ‖z‖ ^ 2 := by
  have hMom := gaussian_shifted_singular_moment_converges_in_probability z 1
  have hEq : (fun n : ℕ => gaussianShiftedSingularMoment (n := n) z 1) =
      fun n : ℕ => gaussianSingularSecondMoment (n := n) z := by
    funext n x
    simp only [gaussianShiftedSingularMoment, gaussianSingularSecondMoment, Nat.mul_one]
  rw [hEq] at hMom
  exact varying_probability_limit_unique gaussianSquareMatrixLaw hMom
    (gaussian_shifted_second_moment_converges_in_probability z)

theorem gaussian_shifted_limit_second_moment (z : ℂ) :
    (∫ t, (t : ℝ) ^ 2 ∂gaussianShiftedSingularLimit z) = 1 + ‖z‖ ^ 2 := by
  simpa only [Nat.mul_one, gaussian_shifted_squared_moment_limit_one] using
    gaussian_shifted_limit_even_moments z 1

theorem gaussian_shifted_squared_moment_limit_two (z : ℂ) :
    gaussianShiftedSquaredMomentLimit z 2 = 2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4 := by
  have hConst : Tendsto (fun n : ℕ => ∫ x, gaussianShiftedSingularMoment z 2 x
      ∂gaussianSquareMatrixLaw n) Filter.atTop (𝓝 (2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4)
      Filter.atTop (𝓝 (2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4))).congr'
      ((Filter.eventually_gt_atTop 0).mono (fun n hn => by
        simpa only [gaussianShiftedSingularMoment, show 2 * 2 = 4 from rfl] using
          (gaussian_shifted_singular_fourth_moment_integral hn z).symm))
  exact tendsto_nhds_unique (gaussian_shifted_even_moment_mean_tendsto z 2) hConst

theorem gaussian_shifted_limit_fourth_moment (z : ℂ) :
    (∫ t, (t : ℝ) ^ 4 ∂gaussianShiftedSingularLimit z) = 2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4 := by
  simpa only [show 2 * 2 = 4 from rfl, gaussian_shifted_squared_moment_limit_two] using
    gaussian_shifted_limit_even_moments z 2

theorem gaussian_shifted_fourth_moment_converges_in_probability (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => ∫ t, (t : ℝ) ^ 4 ∂gaussianSingularMeasure z x)
      (2 + 4 * ‖z‖ ^ 2 + ‖z‖ ^ 4) := by
  have h := gaussian_shifted_singular_moment_converges_in_probability z 2
  change VaryingConvergesInProbability _ _ (gaussianShiftedSquaredMomentLimit z 2) at h
  simpa only [gaussianShiftedSingularMoment, show 2 * 2 = 4 from rfl,
    gaussian_shifted_squared_moment_limit_two] using h

theorem gaussian_shifted_weak_law_finite_log_exists (z : ℂ) :
    ∃ ν : Measure ℝ≥0, IsProbabilityMeasure ν ∧
      EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
        (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν ∧
      FiniteLogarithmicIntegral ν :=
  ⟨gaussianShiftedSingularLimit z, inferInstance, gaussian_shifted_weak_convergence z,
    gaussian_shifted_limit_finite_logarithmic_integral z⟩

end CircularLaw
