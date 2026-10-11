import CircularLaw.BernoulliSqueezeRounding
import CircularLaw.EmpiricalPrefixMeans
import CircularLaw.BernoulliLogTailReduction

/-!
# Prefix deductions for the actual Bernoulli singular-value array

The exact manuscript floors and the actual shifted Bernoulli matrix law
are used throughout. Weak convergence and the limiting linear mass bound
remain explicit inputs. This module does not assert their Gaussian proofs
or full untruncated logarithmic convergence.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace CircularLaw

theorem bernoulli_squeeze_retained_small_probability (d : ℕ → ℕ) (z : ℂ)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν]
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    {C epsilon : ℝ} (hC : 0 < C) (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon ≤ 1)
    (hMass : ∀ t : ℝ, 0 < t → ν.real {x | (x : ℝ) < t} ≤ C * t) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalPrefixHasSmall (bernoulliSingularArray d z n x)
        (bernoulliSqueezePrefixLength n epsilon) (epsilon / (4 * C))}) atTop (𝓝 0) := by
  apply empirical_prefix_lower_bound_of_linear_mass
    (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν
    (fun n => bernoulliSqueezePrefixLength n epsilon) hWeak
    (bernoulliSingularArray_antitone d z) hC hEpsilon hMass
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact bernoulli_squeeze_removed_fraction_lower (by omega) hEpsilon.le hEpsilonOne

theorem bernoulli_squeeze_clipped_negative_convergence (d : ℕ → ℕ) (z : ℂ)
    (ν : Measure ℝ≥0)
    (hWeak : EmpiricalWeakConvergenceInProbability
      (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν)
    (epsilon : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ epsilon n)
    (hEpsilon : Tendsto epsilon atTop (𝓝 0)) {T : ℝ} (hT : 0 ≤ T) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => empiricalNonnegativePrefixMean (bernoulliSingularArray d z n x)
        (bernoulli_squeeze_prefix_le (hNonneg n)) (clippedNegativeLog T))
      (∫ t, clippedNegativeLog T t ∂ν) :=
  empirical_prefix_clipped_negative_convergence
    (fun n => sparseBernoulliMatrixLaw n (d n)) (bernoulliSingularArray d z) ν
    (fun n => bernoulliSqueezePrefixLength n (epsilon n))
    (fun n => bernoulli_squeeze_prefix_le (hNonneg n)) hWeak
    (bernoulli_squeeze_prefix_removed_fraction_tendsto hNonneg hEpsilon) hT

theorem bernoulli_prefix_negative_log_eq_square_prefix (d : ℕ → ℕ) (z : ℂ)
    {n ell : ℕ} (x : BernoulliSquareSample n) (hElln : ell ≤ n) :
    empiricalNonnegativePrefixMean (bernoulliSingularArray d z n x) hElln
        (fun t => -Real.log (t : ℝ)) =
      squareNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x) ell := by
  unfold empiricalNonnegativePrefixMean squareNegativeLogPrefix
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [squareNegativeLogAt, dif_pos (lt_of_lt_of_le j.isLt hElln)]
  rfl

end CircularLaw
