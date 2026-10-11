import CircularLaw.GaussianShiftedSquaredMoments
import CircularLaw.CompactMomentConvergence
import CircularLaw.GaussianZeroWeakLimit
import CircularLaw.EmpiricalWeakLimitUnique

/-!
# Actual Gaussian singular laws converge at every complex shift

All squared singular moments converge in probability and all samples
lie in a fixed compact interval outside a vanishing norm event. These
proved facts construct a compact probability law with the actual moment
limits and prove convergence for continuous tests. Mapping through the
nonnegative square root gives the actual shifted singular law. Its
existence is proved here, rather than assumed by hermitization.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem gaussian_shifted_squared_law_exists (z : ℂ) :
    ∃ ν : ProbabilityMeasure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2)),
      ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2)))) =
        gaussianShiftedSquaredMomentLimit z m :=
  supported_probability_measure_of_varying_moments gaussianSquareMatrixLaw
    (fun _ => gaussianShiftedSquaredSingularValues z) (gaussianShiftedSquaredMomentLimit z)
    ((128 + ‖z‖) ^ 2) (fun _ => gaussian_shifted_squared_singular_values_nonneg z)
    (gaussian_shifted_squared_singular_bound_failure_tendsto z)
    (gaussian_shifted_squared_singular_moments_converge z)

def gaussianShiftedSquaredLimit (z : ℂ) :
    ProbabilityMeasure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2)) :=
  Classical.choose (gaussian_shifted_squared_law_exists z)

theorem gaussian_shifted_squared_limit_moments (z : ℂ) (m : ℕ) :
    (∫ t, (t : ℝ) ^ m
      ∂(gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2)))) =
        gaussianShiftedSquaredMomentLimit z m :=
  Classical.choose_spec (gaussian_shifted_squared_law_exists z) m

def gaussianShiftedSingularLimit (z : ℂ) : Measure ℝ≥0 :=
  (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))).map
    (fun t : Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2) => nonnegativeRealSquareRoot (t : ℝ))

instance gaussianShiftedSingularLimit_probability (z : ℂ) :
    IsProbabilityMeasure (gaussianShiftedSingularLimit z) :=
  (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))).isProbabilityMeasure_map
    (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable.aemeasurable

theorem gaussian_shifted_weak_convergence (z : ℂ) :
    EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
      (gaussianShiftedSingularLimit z) := by
  intro f hf _
  let F : ℝ → ℝ := fun r => f (nonnegativeRealSquareRoot r)
  have hF : Continuous F := hf.comp continuous_nonnegative_real_square_root
  have hLimit := varying_probability_continuous_of_compact_moments gaussianSquareMatrixLaw
    (fun _ => gaussianShiftedSquaredSingularValues z) (gaussianShiftedSquaredMomentLimit z)
    ((128 + ‖z‖) ^ 2) (fun _ => gaussian_shifted_squared_singular_values_nonneg z)
    (gaussian_shifted_squared_singular_bound_failure_tendsto z)
    (gaussian_shifted_squared_singular_moments_converge z)
    (gaussianShiftedSquaredLimit z) (gaussian_shifted_squared_limit_moments z) F hF.continuousOn
  have hIntegral : (∫ t, f t ∂gaussianShiftedSingularLimit z) =
      ∫ t, F (t : ℝ)
        ∂(gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))) :=
    integral_map_of_stronglyMeasurable
      (μ := (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))))
      (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
      hf.measurable.stronglyMeasurable
  rw [← hIntegral] at hLimit
  simpa only [F, gaussianShiftedSquaredSingularValues, nonnegative_real_square_root_sq,
    empiricalNonnegativeMean] using hLimit

theorem gaussian_shifted_limit_even_moments (z : ℂ) (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianShiftedSingularLimit z) =
      gaussianShiftedSquaredMomentLimit z k := by
  rw [gaussianShiftedSingularLimit, integral_map_of_stronglyMeasurable
    (μ := (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))))
    (φ := fun t : Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2) => nonnegativeRealSquareRoot (t : ℝ))
    (f := fun t : ℝ≥0 => (t : ℝ) ^ (2 * k))
    (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
    (NNReal.continuous_coe.pow _).measurable.stronglyMeasurable]
  have hEq (t : Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2)) :
      (nonnegativeRealSquareRoot (t : ℝ) : ℝ) ^ (2 * k) = (t : ℝ) ^ k := by
    change Real.sqrt (t : ℝ) ^ (2 * k) = _
    rw [pow_mul, Real.sq_sqrt t.property.1]
  simp only [hEq]
  exact gaussian_shifted_squared_limit_moments z k

theorem gaussian_shifted_limit_unique (z : ℂ) (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) ν) :
    ν = gaussianShiftedSingularLimit z :=
  empirical_weak_limit_unique gaussianSquareMatrixLaw
    (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
    ν (gaussianShiftedSingularLimit z) hWeak (gaussian_shifted_weak_convergence z)

theorem gaussian_shifted_limit_at_zero :
    gaussianShiftedSingularLimit 0 = gaussianZeroShiftSingularLimit :=
  empirical_weak_limit_unique gaussianSquareMatrixLaw
    (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
    (gaussianShiftedSingularLimit 0) gaussianZeroShiftSingularLimit
    (gaussian_shifted_weak_convergence 0) gaussian_zero_shift_weak_convergence

theorem gaussian_shifted_limit_support (z : ℂ) :
    gaussianShiftedSingularLimit z {t : ℝ≥0 | 128 + ‖z‖ < (t : ℝ)} = 0 :=
  gaussian_shifted_weak_limit_support z (gaussianShiftedSingularLimit z)
    (gaussian_shifted_weak_convergence z)

end CircularLaw
