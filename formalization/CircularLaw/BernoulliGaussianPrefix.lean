import CircularLaw.GaussianLogPrefixConvergence
import CircularLaw.BernoulliSlowPrefixLimit
import CircularLaw.BernoulliGaussianWeakTransfer

/-!
# The actual Gaussian comparator and Bernoulli prefix with one fraction

All Gaussian-law bounds, Gaussian prefix limits and the actual Bernoulli
weak singular-law transfer are discharged by checked proofs. The minor
estimates needed to recover its full logarithm remain separate obligations.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem bernoulli_gaussian_comparator_prefix_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    ∃ epsilon : ℕ → ℝ, (∀ n, 0 < epsilon n ∧ epsilon n ≤ 1) ∧
      Antitone epsilon ∧ Tendsto epsilon atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (epsilon n)))
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z)) ∧
      VaryingConvergesInProbability gaussianSquareMatrixLaw
        (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x)
          (bernoulliSqueezePrefixLength n (epsilon n)))
        (-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianShiftedSingularLimit z)) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliSingularArray d z n x)
          (bernoulliSqueezePrefixLength n (epsilon n))}) atTop (𝓝 0) ∧
      Tendsto (fun n => (gaussianSquareMatrixLaw n).real
        {x | empiricalPrefixHasZero (gaussianSingularArray z n x)
          (bernoulliSqueezePrefixLength n (epsilon n))}) atTop (𝓝 0) := by
  obtain ⟨K, q, hRange, hAnti, hEpsilon, hBernoulli, hZero⟩ :=
    bernoulli_slow_prefix_log_convergence d z hd hsparse (gaussianShiftedSingularLimit z)
      (bernoulli_shifted_weak_convergence d hd hsparse z)
      (by norm_num : (0 : ℝ) < 48) (fun _ ht => gaussian_shifted_limit_small_mass z ht)
      (128 + ‖z‖) (gaussian_shifted_limit_support z)
  let epsilon : ℕ → ℝ := fun n => logarithmicStageFraction 48 K (q n)
  have hNonneg : ∀ n, 0 ≤ epsilon n := fun n => (hRange n).1.le
  exact ⟨epsilon, hRange, hAnti, hEpsilon, hBernoulli,
    gaussian_rounded_negative_log_prefix_converges z epsilon hNonneg hEpsilon, hZero,
    gaussian_prefix_zero_probability_tendsto z
      (fun n => bernoulliSqueezePrefixLength n (epsilon n))⟩

end CircularLaw
