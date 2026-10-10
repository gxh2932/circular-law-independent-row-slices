import CircularLaw.BernoulliGaussianPrefix
import CircularLaw.GaussianShiftedLogValue

/-!
# Common Bernoulli and Gaussian prefixes with the actual circular value

The Gaussian logarithmic-potential identification and the actual sparse
Bernoulli weak singular-law transfer are discharged. Both literal rounded
prefixes converge to the paper's circular potential with one common positive
antitone fraction tending to zero, and both zero events vanish.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem bernoulli_gaussian_circular_prefix_convergence (d : ℕ → ℕ) (z : ℂ)
    (hd : Tendsto d atTop atTop) (hsparse : SparseDegrees d) :
    ∃ epsilon : ℕ → ℝ, (∀ n, 0 < epsilon n ∧ epsilon n ≤ 1) ∧
      Antitone epsilon ∧ Tendsto epsilon atTop (𝓝 0) ∧
      VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
        (fun n x => squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x)
          (bernoulliSqueezePrefixLength n (epsilon n))) (circularPaperPotential z) ∧
      VaryingConvergesInProbability gaussianSquareMatrixLaw
        (fun n x => squareNegativeLogPrefix (normalizedShiftedGaussianMatrix z x)
          (bernoulliSqueezePrefixLength n (epsilon n))) (circularPaperPotential z) ∧
      Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliSingularArray d z n x)
          (bernoulliSqueezePrefixLength n (epsilon n))}) atTop (𝓝 0) ∧
      Tendsto (fun n => (gaussianSquareMatrixLaw n).real
        {x | empiricalPrefixHasZero (gaussianSingularArray z n x)
          (bernoulliSqueezePrefixLength n (epsilon n))}) atTop (𝓝 0) := by
  simpa only [gaussian_shifted_log_integral_eq_circular, circularPaperPotential] using
    bernoulli_gaussian_comparator_prefix_convergence d z hd hsparse

end CircularLaw
