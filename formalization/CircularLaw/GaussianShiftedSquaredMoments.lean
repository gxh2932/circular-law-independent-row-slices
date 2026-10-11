import CircularLaw.GaussianShiftedMomentConcentration
import CircularLaw.GaussianShiftedNormSupport
import CircularLaw.VaryingProbabilityPolynomial

/-!
# All actual squared singular moments at every Gaussian shift

Squaring the actual singular values converts the even-moment probability
limits into all natural moment limits. The checked operator norm estimate
bounds the squared samples by `(128 + norm z)^2` outside a vanishing
event, supplying the inputs for compact moment existence and convergence.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def gaussianShiftedSquaredSingularValues {n : ℕ} (z : ℂ) (x : GaussianSquareSample n)
    (j : Fin n) : ℝ :=
  (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j : ℝ) ^ 2

def gaussianShiftedSquaredMomentLimit (z : ℂ) (m : ℕ) : ℝ :=
  (gaussianShiftedMomentMeanLimit z m).re

theorem gaussian_shifted_squared_moment_limit_zero (z : ℂ) :
    gaussianShiftedSquaredMomentLimit z 0 = 1 := by
  simp only [gaussianShiftedSquaredMomentLimit, gaussian_shifted_moment_mean_limit_zero,
    Complex.one_re]

theorem gaussian_shifted_squared_singular_moment_eq {n : ℕ} (z : ℂ) (m : ℕ)
    (x : GaussianSquareSample n) :
    finiteMean (fun j => gaussianShiftedSquaredSingularValues z x j ^ m) =
      gaussianShiftedSingularMoment z m x := by
  simp only [gaussianShiftedSingularMoment, gaussianSingularMeasure, squareSingularMeasure,
    empiricalNonnegativeMeasure_integral, empiricalNonnegativeMean,
    gaussianShiftedSquaredSingularValues, pow_mul]

theorem gaussian_shifted_squared_singular_moments_converge (z : ℂ) (m : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ x => finiteMean (fun j => gaussianShiftedSquaredSingularValues z x j ^ m))
      (gaussianShiftedSquaredMomentLimit z m) := by
  simp only [gaussian_shifted_squared_singular_moment_eq, gaussianShiftedSquaredMomentLimit]
  exact gaussian_shifted_singular_moment_converges_in_probability z m

theorem gaussian_shifted_squared_singular_values_nonneg {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) (j : Fin n) :
    0 ≤ gaussianShiftedSquaredSingularValues z x j := sq_nonneg _

theorem gaussian_shifted_squared_singular_bound_failure_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ => (gaussianSquareMatrixLaw n).real
      {x | ∃ j, (128 + ‖z‖) ^ 2 < gaussianShiftedSquaredSingularValues z x j})
      atTop (𝓝 0) := by
  have hEq (n : ℕ) :
      {x : GaussianSquareSample n | ∃ j,
        (128 + ‖z‖) ^ 2 < gaussianShiftedSquaredSingularValues z x j} =
      {x | ∃ j, 128 + ‖z‖ <
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j} := by
    ext x
    simp only [gaussianShiftedSquaredSingularValues, squareSingularValuesNNReal, NNReal.coe_mk]
    exact exists_congr (fun j => sq_lt_sq₀ (by positivity)
      (orderedSquareSingularValues_nonneg _ j))
  simp only [hEq]
  exact gaussian_shifted_singular_value_bad_probability_tendsto z

end CircularLaw
