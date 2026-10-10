import CircularLaw.GaussianMinorLimitProperties
import CircularLaw.IndexedRetainedPrefixSmallValues
import CircularLaw.PrefixNegativeDeviation

/-!
# Retained singular values of the actual ambient-normalized minor

The literal second manuscript floor omits at least epsilon/4 of the
minor's own dimension. The proved ambient-normalized weak law and scaled
Gaussian mass bound give a strictly positive lower bound for the retained
singular values, with failure probability tending to zero. This controls
retained zeros without claiming a full or untruncated logarithmic limit.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def bernoulliMinorSingularArray (d : ℕ → ℕ) (z : ℂ) (epsilon : ℝ)
    (hNonneg : 0 ≤ epsilon) :
    ∀ n, BernoulliSquareSample n → Fin (bernoulliSqueezeMinorDimension n epsilon) → ℝ≥0 :=
  fun n x => squareSingularValuesNNReal
    (squarePrincipalMinor (normalizedShiftedBernoulliMatrix (d n) z x)
      (bernoulli_squeeze_lengths_le (n := n) hNonneg).2)

theorem bernoulliMinorSingularArray_antitone (d : ℕ → ℕ) (z : ℂ) (epsilon : ℝ)
    (hNonneg : 0 ≤ epsilon) (n : ℕ) (x : BernoulliSquareSample n) :
    Antitone (bernoulliMinorSingularArray d z epsilon hNonneg n x) := by
  intro i j hij
  exact orderedSquareSingularValues_antitone _ hij

theorem bernoulli_squeeze_minor_removed_fraction_lower {n : ℕ} {epsilon : ℝ}
    (hNonneg : 0 ≤ epsilon) (hOne : epsilon ≤ 1)
    (hMinor : 0 < bernoulliSqueezeMinorDimension n epsilon) :
    epsilon / 4 ≤
      (bernoulliSqueezeMinorDimension n epsilon - bernoulliSqueezePrefixLength n epsilon : ℕ) /
        (bernoulliSqueezeMinorDimension n epsilon : ℝ) := by
  have hLengths := bernoulli_squeeze_lengths_le (n := n) hNonneg
  have hPrefix : (bernoulliSqueezePrefixLength n epsilon : ℝ) ≤
      (1 - epsilon / 4) * bernoulliSqueezeMinorDimension n epsilon :=
    Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  rw [Nat.cast_sub hLengths.1]
  apply (le_div_iff₀ (by exact_mod_cast hMinor :
    (0 : ℝ) < bernoulliSqueezeMinorDimension n epsilon)).mpr
  linarith

theorem bernoulli_minor_retained_small_probability_tendsto (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) (hOne : epsilon < 1) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalPrefixHasSmall (bernoulliMinorSingularArray d z epsilon hEpsilon.le n x)
        (bernoulliSqueezePrefixLength n epsilon)
        ((epsilon / 4) / (4 * (48 / Real.sqrt (1 - epsilon))))}) atTop (𝓝 0) := by
  have hTheta : 0 < 1 - epsilon := by linarith
  have hQ := minor_dimension_tendsto_of_positive_ratio
    (fun n => bernoulliSqueezeMinorDimension n epsilon) hTheta
    (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne)
  apply indexed_empirical_prefix_lower_bound_of_linear_mass
    (fun n => sparseBernoulliMatrixLaw n (d n))
    (bernoulliMinorSingularArray d z epsilon hEpsilon.le)
    (gaussianMinorSingularLimit (1 - epsilon) z)
    (fun n => bernoulliSqueezePrefixLength n epsilon)
    (bernoulli_fixed_fraction_minor_ambient_weak_convergence d hDegree hSparse hEpsilon.le hOne z)
    (bernoulliMinorSingularArray_antitone d z epsilon hEpsilon.le)
    (div_pos (by norm_num) (Real.sqrt_pos.2 hTheta)) (by positivity)
    (fun _ ht => gaussian_minor_limit_small_mass hTheta z ht)
  filter_upwards [hQ.eventually_gt_atTop 0] with n hn
  exact bernoulli_squeeze_minor_removed_fraction_lower hEpsilon.le hOne.le hn

theorem bernoulli_minor_retained_zero_probability_tendsto (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0))
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) (hOne : epsilon < 1) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalPrefixHasZero (bernoulliMinorSingularArray d z epsilon hEpsilon.le n x)
        (bernoulliSqueezePrefixLength n epsilon)}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (bernoulli_minor_retained_small_probability_tendsto d z hDegree hSparse hEpsilon hOne)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  refine Eventually.of_forall (fun n => measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) ?_)
  intro x hx
  exact empirical_prefix_zero_subset_small _
    (by have hTheta : 0 < 1 - epsilon := by linarith
        have hRoot := Real.sqrt_pos.2 hTheta
        positivity) hx

end CircularLaw
