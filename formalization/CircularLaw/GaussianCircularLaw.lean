import CircularLaw.GaussianShiftedLogValue
import CircularLaw.GaussianLogPrefixConvergence
import CircularLaw.CircularHermitization

/-!
# The Gaussian circular-law comparator with every hypothesis discharged

Full empirical logarithms, actual spectral potentials and every prefix
omitting a vanishing fraction converge to the checked circular potential.
The direct hermitization criterion then gives full bounded-Lipschitz ESD
convergence for the independent standard complex Gaussian matrix law.
This does not supply the sparse Bernoulli or independent row-slice law.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology ENNReal

namespace CircularLaw

theorem gaussian_log_mean_converges_circular (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => empiricalNonnegativeMean
        (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x))
        (fun t => Real.log (t : ℝ))) (circularLogPotential z) := by
  simpa only [gaussian_shifted_log_integral_eq_circular] using gaussian_log_mean_converges z

theorem gaussian_spectral_log_potential_converges_circular (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => spectralLogPotential ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) z)
      (circularLogPotential z) := by
  simpa only [gaussian_shifted_log_integral_eq_circular] using gaussian_spectral_log_potential_converges z

theorem gaussian_log_determinant_converges_circular (z : ℂ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => normalizedLogDeterminant ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) z)
      (circularLogPotential z) := by
  have hZero : Tendsto (fun n => (gaussianSquareMatrixLaw n).real
      {x | (normalizedShiftedGaussianMatrix z x).det = 0}) atTop (𝓝 0) := by
    simpa only [square_singular_has_zero_iff_det_zero] using
      gaussian_empirical_zero_probability_tendsto z
  apply varying_probability_of_agreement_outside_bad_event gaussianSquareMatrixLaw
    (fun n => {x : GaussianSquareSample n | (normalizedShiftedGaussianMatrix z x).det = 0})
    (gaussian_log_mean_converges_circular z) hZero
  exact Eventually.of_forall (fun n x hx =>
    (shifted_singular_empirical_mean_eq_log_determinant
      ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x) z hx).symm)

theorem gaussian_negative_log_prefix_converges_circular (z : ℂ) (ell : ℕ → ℕ)
    (hElln : ∀ n, ell n ≤ n)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x) (ell n))
      (circularPaperPotential z) := by
  simpa only [gaussian_shifted_log_integral_eq_circular, circularPaperPotential] using
    gaussian_square_negative_log_prefix_converges z ell hElln hRemoved

theorem gaussian_rounded_negative_log_prefix_converges_circular (z : ℂ) (epsilon : ℕ → ℝ)
    (hNonneg : ∀ n, 0 ≤ epsilon n) (hEpsilon : Tendsto epsilon atTop (𝓝 0)) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x)
        (bernoulliSqueezePrefixLength n (epsilon n))) (circularPaperPotential z) := by
  simpa only [gaussian_shifted_log_integral_eq_circular, circularPaperPotential] using
    gaussian_rounded_negative_log_prefix_converges z epsilon hNonneg hEpsilon

theorem gaussian_circular_law :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (gaussianSquareMatrixLaw n).real {x |
      ENNReal.ofReal ε < boundedLipschitzDistance
        (empiricalSpectralMeasure ((Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x))
        circularMeasure}) atTop (𝓝 0) := by
  apply matrix_circular_hermitization gaussianSquareMatrixLaw
    (fun n x => (Real.sqrt (n : ℝ) : ℂ)⁻¹ • gaussianSquareMatrix x)
  · intro n
    exact (gaussian_square_matrix_measurable n).const_smul ((Real.sqrt (n : ℝ) : ℂ)⁻¹)
  · simpa only [normalizedShiftedGaussianMatrix, zero_smul, sub_zero] using
      gaussian_normalized_energy_bounded_in_probability
  · exact Eventually.of_forall gaussian_log_determinant_converges_circular

end CircularLaw
