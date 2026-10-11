import CircularLaw.GaussianSquaredMomentLimits
import CircularLaw.CompactMomentConvergence
import CircularLaw.GaussianWeakLimitSupport

/-!
# The actual zero-shift Gaussian singular law converges weakly in probability

The checked even moment limits and matrix norm event construct a probability
measure on the compact interval of squared singular values. Polynomial
approximation proves the actual test-function convergence. Pushing the
measure through the nonnegative square root gives the limiting singular
law. Its moments are the exact leading pairing counts. Their Catalan
enumeration and the general shifted law are proved in later modules.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def nonnegativeRealSquareRoot (t : ℝ) : ℝ≥0 := ⟨Real.sqrt t, Real.sqrt_nonneg t⟩

theorem continuous_nonnegative_real_square_root : Continuous nonnegativeRealSquareRoot :=
  Real.continuous_sqrt.subtype_mk _

theorem nonnegative_real_square_root_sq (t : ℝ≥0) :
    nonnegativeRealSquareRoot ((t : ℝ) ^ 2) = t := by
  apply NNReal.eq
  exact Real.sqrt_sq t.property

theorem gaussian_zero_shift_squared_law_exists :
    ∃ ν : ProbabilityMeasure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)),
      ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)))) =
        gaussianZeroShiftMomentLimit m :=
  supported_probability_measure_of_varying_moments gaussianSquareMatrixLaw
    (fun _ => gaussianSquaredSingularValues) gaussianZeroShiftMomentLimit ((128 : ℝ) ^ 2)
    (fun _ => gaussian_squared_singular_values_nonneg)
    gaussian_squared_singular_value_bound_failure_tendsto gaussian_squared_singular_moments_converge

def gaussianZeroShiftSquaredLimit : ProbabilityMeasure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)) :=
  Classical.choose gaussian_zero_shift_squared_law_exists

theorem gaussian_zero_shift_squared_limit_moments (m : ℕ) :
    (∫ t, (t : ℝ) ^ m
      ∂(gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)))) =
        gaussianZeroShiftMomentLimit m :=
  Classical.choose_spec gaussian_zero_shift_squared_law_exists m

def gaussianZeroShiftSingularLimit : Measure ℝ≥0 :=
  (gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))).map
    (fun t : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2) => nonnegativeRealSquareRoot (t : ℝ))

instance gaussianZeroShiftSingularLimit_probability : IsProbabilityMeasure gaussianZeroShiftSingularLimit :=
  (gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))).isProbabilityMeasure_map
    (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable.aemeasurable

theorem gaussian_zero_shift_weak_convergence :
    EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw
      (fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix 0 x))
      gaussianZeroShiftSingularLimit := by
  intro f hf _
  let F : ℝ → ℝ := fun r => f (nonnegativeRealSquareRoot r)
  have hF : Continuous F := hf.comp continuous_nonnegative_real_square_root
  have hLimit := varying_probability_continuous_of_compact_moments gaussianSquareMatrixLaw
    (fun _ => gaussianSquaredSingularValues) gaussianZeroShiftMomentLimit ((128 : ℝ) ^ 2)
    (fun _ => gaussian_squared_singular_values_nonneg)
    gaussian_squared_singular_value_bound_failure_tendsto gaussian_squared_singular_moments_converge
    gaussianZeroShiftSquaredLimit gaussian_zero_shift_squared_limit_moments F hF.continuousOn
  have hIntegral : (∫ t, f t ∂gaussianZeroShiftSingularLimit) =
      ∫ t, F (t : ℝ)
        ∂(gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))) :=
    integral_map_of_stronglyMeasurable
      (μ := (gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))))
      (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
      hf.measurable.stronglyMeasurable
  rw [← hIntegral] at hLimit
  simpa only [F, gaussianSquaredSingularValues, nonnegative_real_square_root_sq,
    empiricalNonnegativeMean] using hLimit

theorem gaussian_zero_shift_limit_even_moments (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * (k + 1)) ∂gaussianZeroShiftSingularLimit) =
      (gaussianLeadingMomentCount k : ℝ) := by
  rw [gaussianZeroShiftSingularLimit, integral_map_of_stronglyMeasurable
    (μ := (gaussianZeroShiftSquaredLimit : Measure (Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2))))
    (φ := fun t : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2) => nonnegativeRealSquareRoot (t : ℝ))
    (f := fun t : ℝ≥0 => (t : ℝ) ^ (2 * (k + 1)))
    (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
    (NNReal.continuous_coe.pow _).measurable.stronglyMeasurable]
  have hEq (t : Set.Icc (0 : ℝ) ((128 : ℝ) ^ 2)) :
      (nonnegativeRealSquareRoot (t : ℝ) : ℝ) ^ (2 * (k + 1)) = (t : ℝ) ^ (k + 1) := by
    change Real.sqrt (t : ℝ) ^ (2 * (k + 1)) = _
    rw [pow_mul, Real.sq_sqrt t.property.1]
  simp only [hEq]
  rw [gaussian_zero_shift_squared_limit_moments, gaussian_zero_shift_moment_limit_succ]

theorem gaussian_zero_shift_weak_limit_support :
    gaussianZeroShiftSingularLimit {t : ℝ≥0 | (128 : ℝ) < (t : ℝ)} = 0 := by
  simpa only [norm_zero, add_zero] using gaussian_shifted_weak_limit_support 0
    gaussianZeroShiftSingularLimit gaussian_zero_shift_weak_convergence

end CircularLaw
