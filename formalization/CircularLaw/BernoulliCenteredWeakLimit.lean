import CircularLaw.BernoulliGaussianWordCounts
import CircularLaw.CompactTargetMomentConvergence
import CircularLaw.GaussianShiftedWeakLimit

/-!
# Actual centered Bernoulli singular laws converge to the Gaussian law

Every centered shifted even moment converges in probability to the
Gaussian moment. Squaring the nonnegative singular values gives all
natural empirical moments of the compact Gaussian squared limit.
The moment-to-weak passage controls tails by higher moments, permitting
large exceptional sample singular values. Mapping through square root
therefore gives the actual centered Bernoulli weak singular law at every
complex shift. Restoring the deterministic rank-one mean is separate.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def bernoulliCenteredShiftedSquaredSingularValues {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (j : Fin n) : ℝ :=
  (squareSingularValuesNNReal (normalizedCenteredBernoulliMatrix d x - z • 1) j : ℝ) ^ 2

theorem bernoulli_centered_squared_singular_moment_eq {n : ℕ} (d : ℕ) (z : ℂ) (m : ℕ)
    (x : BernoulliSquareSample n) :
    finiteMean (fun j => bernoulliCenteredShiftedSquaredSingularValues d z x j ^ m) =
      bernoulliCenteredShiftedSingularMoment d z m x := by
  simp only [bernoulliCenteredShiftedSingularMoment, squareSingularMeasure,
    empiricalNonnegativeMeasure_integral, empiricalNonnegativeMean,
    bernoulliCenteredShiftedSquaredSingularValues, pow_mul]

theorem bernoulli_centered_squared_singular_moments_converge (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (m : ℕ) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => finiteMean (fun j => bernoulliCenteredShiftedSquaredSingularValues (d n) z x j ^ m))
      (gaussianShiftedSquaredMomentLimit z m) := by
  simp only [bernoulli_centered_squared_singular_moment_eq, gaussianShiftedSquaredMomentLimit]
  exact bernoulli_centered_shifted_gaussian_moment_in_probability d hDegree hSparse z m

theorem bernoulli_centered_squared_singular_values_nonneg {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) (j : Fin n) :
    0 ≤ bernoulliCenteredShiftedSquaredSingularValues d z x j := sq_nonneg _

theorem bernoulli_centered_shifted_weak_convergence (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) :
    EmpiricalWeakConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => squareSingularValuesNNReal (normalizedCenteredBernoulliMatrix (d n) x - z • 1))
      (gaussianShiftedSingularLimit z) := by
  intro f hf hBound
  let F : ℝ → ℝ := fun r => f (nonnegativeRealSquareRoot r)
  have hF : Continuous F := hf.comp continuous_nonnegative_real_square_root
  have hFBound : ∃ M : ℝ, ∀ r, |F r| ≤ M := by
    obtain ⟨M, hM⟩ := hBound
    exact ⟨M, fun r => hM (nonnegativeRealSquareRoot r)⟩
  have hLimit := varying_probability_bounded_continuous_of_compact_target_moments
    (fun n => sparseBernoulliMatrixLaw n (d n))
    (fun n => bernoulliCenteredShiftedSquaredSingularValues (d n) z)
    (gaussianShiftedSquaredMomentLimit z) ((128 + ‖z‖) ^ 2) (sq_nonneg _)
    (fun n => bernoulli_centered_squared_singular_values_nonneg (d n) z)
    (bernoulli_centered_squared_singular_moments_converge d hDegree hSparse z)
    (gaussianShiftedSquaredLimit z) (gaussian_shifted_squared_limit_moments z) F hF hFBound
  have hIntegral : (∫ t, f t ∂gaussianShiftedSingularLimit z) =
      ∫ t, F (t : ℝ)
        ∂(gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))) :=
    integral_map_of_stronglyMeasurable
      (μ := (gaussianShiftedSquaredLimit z : Measure (Set.Icc (0 : ℝ) ((128 + ‖z‖) ^ 2))))
      (continuous_nonnegative_real_square_root.comp continuous_subtype_val).measurable
      hf.measurable.stronglyMeasurable
  rw [← hIntegral] at hLimit
  simpa only [F, bernoulliCenteredShiftedSquaredSingularValues, nonnegative_real_square_root_sq,
    empiricalNonnegativeMean] using hLimit

end CircularLaw
