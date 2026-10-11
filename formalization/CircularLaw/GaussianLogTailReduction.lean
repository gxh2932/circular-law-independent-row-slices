import CircularLaw.GaussianLogConvergence
import CircularLaw.NegativeLogUniformIntegrability

/-!
# Unconditional logarithmic tails of the actual shifted Gaussian law

Both source tail conclusions now follow with every Gaussian hypothesis
discharged. Extended negative logarithms retain infinity at zero.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CircularLaw

def gaussianSingularArray (z : ℂ) : ∀ n, GaussianSquareSample n → Fin n → ℝ≥0 :=
  fun _ x => squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)

theorem gaussianSingularArray_antitone (z : ℂ) (n : ℕ) (x : GaussianSquareSample n) :
    Antitone (gaussianSingularArray z n x) := by
  intro i j hij
  exact orderedSquareSingularValues_antitone _ hij

theorem gaussian_negative_log_tail_threshold (z : ℂ) {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T →
      Tendsto (fun n => (gaussianSquareMatrixLaw n).real {x | ENNReal.ofReal epsilon <
        ∫⁻ t, extendedNegativeLogTail T t ∂gaussianSingularMeasure z x}) atTop (𝓝 0) :=
  negative_log_tail_measure_threshold gaussianSquareMatrixLaw (gaussianSingularArray z)
    (gaussianShiftedSingularLimit z) (gaussian_shifted_weak_convergence z)
    (gaussian_empirical_log_convergence z) (gaussian_shifted_limit_finite_logarithmic_integral z)
    (gaussian_empirical_second_moment_bounded z) hEpsilon

theorem gaussian_negative_log_uniform_integrability (z : ℂ)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    Tendsto (fun T : ℝ => limsup (fun n => (gaussianSquareMatrixLaw n).real
      {x | ENNReal.ofReal epsilon <
        ∫⁻ t, extendedNegativeLogTail T t ∂gaussianSingularMeasure z x}) atTop) atTop (𝓝 0) :=
  negative_log_tail_measure_limsup gaussianSquareMatrixLaw (gaussianSingularArray z)
    (gaussianShiftedSingularLimit z) (gaussian_shifted_weak_convergence z)
    (gaussian_empirical_log_convergence z) (gaussian_shifted_limit_finite_logarithmic_integral z)
    (gaussian_empirical_second_moment_bounded z) hEpsilon

theorem gaussian_bottom_negative_log_extended_convergence (z : ℂ) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real {x | ENNReal.ofReal epsilon <
      empiricalExtendedBottomNegativeLog (gaussianSingularArray z n x) (r n)}) atTop (𝓝 0) :=
  bottom_negative_log_extended_convergence gaussianSquareMatrixLaw (gaussianSingularArray z)
    (gaussianShiftedSingularLimit z) (gaussian_shifted_weak_convergence z)
    (gaussian_empirical_log_convergence z) (gaussian_shifted_limit_finite_logarithmic_integral z)
    (gaussian_empirical_second_moment_bounded z) r hr hEpsilon

theorem gaussian_shifted_weak_and_full_log_exists (z : ℂ) :
    ∃ ν : Measure ℝ≥0, IsProbabilityMeasure ν ∧
      EmpiricalWeakConvergenceInProbability gaussianSquareMatrixLaw (gaussianSingularArray z) ν ∧
      FiniteLogarithmicIntegral ν ∧
      EmpiricalLogConvergenceInProbability gaussianSquareMatrixLaw (gaussianSingularArray z) ν ∧
      (∀ t : ℝ, 0 < t → ν.real {r : ℝ≥0 | (r : ℝ) < t} ≤ 48 * t) :=
  ⟨gaussianShiftedSingularLimit z, inferInstance, gaussian_shifted_weak_convergence z,
    gaussian_shifted_limit_finite_logarithmic_integral z, gaussian_empirical_log_convergence z,
    fun _ ht => gaussian_shifted_limit_small_mass z ht⟩

end CircularLaw
