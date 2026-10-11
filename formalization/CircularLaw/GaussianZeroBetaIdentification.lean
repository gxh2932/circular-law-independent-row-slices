import CircularLaw.GaussianZeroBetaCandidate

/-!
# The actual zero-shift singular limit is the square root of a scaled beta law

The beta candidate supplies every actual compact squared-moment limit.
Polynomial approximation proves actual weak convergence to its square-root
image, and uniqueness identifies this image with both Gaussian limits.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_zero_shift_beta_weak_convergence :
    EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
      gaussianZeroBetaSingularCandidate := by
  intro f hf _
  let F : ℝ → ℝ := fun r => f (nonnegativeRealSquareRoot r)
  have hF : Continuous F := hf.comp continuous_nonnegative_real_square_root
  have hLimit := varying_probability_continuous_of_compact_moments gaussianSquareMatrixLaw
    (fun _ => gaussianSquaredSingularValues) gaussianZeroShiftMomentLimit ((128 : ℝ) ^ 2)
    (fun _ => gaussian_squared_singular_values_nonneg)
    gaussian_squared_singular_value_bound_failure_tendsto gaussian_squared_singular_moments_converge
    gaussianZeroBetaSquaredCandidate gaussian_zero_beta_squared_candidate_actual_moments F hF.continuousOn
  have hIntegral : (∫ t, f t ∂gaussianZeroBetaSingularCandidate) =
      ∫ t, F (t : ℝ)
        ∂(gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))) :=
    integral_map_of_stronglyMeasurable
      (μ := (gaussianZeroBetaSquaredCandidate : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))))
      (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
      hf.measurable.stronglyMeasurable
  rw [← hIntegral] at hLimit
  simpa only [F, gaussianSquaredSingularValues, nonnegative_real_square_root_sq,
    empiricalNonnegativeMean] using hLimit

theorem gaussian_zero_shift_limit_eq_beta_candidate :
    gaussianZeroShiftSingularLimit = gaussianZeroBetaSingularCandidate :=
  empirical_weak_limit_unique gaussianSquareMatrixLaw
    (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
    gaussianZeroShiftSingularLimit gaussianZeroBetaSingularCandidate
    gaussian_zero_shift_weak_convergence gaussian_zero_shift_beta_weak_convergence

theorem gaussian_shifted_zero_limit_eq_beta_candidate :
    gaussianShiftedSingularLimit 0 = gaussianZeroBetaSingularCandidate := by
  rw [gaussian_shifted_limit_at_zero, gaussian_zero_shift_limit_eq_beta_candidate]

theorem gaussian_zero_beta_candidate_eq_sqrt_beta :
    gaussianZeroBetaSingularCandidate =
      gaussianZeroBetaBase.map (fun x => nonnegativeRealSquareRoot (4 * x)) := by
  change (gaussianZeroBetaBase.map gaussianZeroBetaSquaredMap).map
    (nonnegativeRealSquareRoot ∘
      (Subtype.val : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2) → ℝ)) = _
  rw [Measure.map_map (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
    continuous_gaussian_zero_beta_squared_map.measurable]
  apply Measure.map_congr
  exact gaussian_zero_beta_squared_map_ae.mono (fun _ h => congrArg nonnegativeRealSquareRoot h)

theorem gaussian_zero_shift_limit_eq_sqrt_beta :
    gaussianShiftedSingularLimit 0 =
      (ProbabilityTheory.betaMeasure (1 / 2) (3 / 2)).map
        (fun x => nonnegativeRealSquareRoot (4 * x)) := by
  rw [gaussian_shifted_zero_limit_eq_beta_candidate, gaussian_zero_beta_candidate_eq_sqrt_beta]
  rfl

end CircularLaw
