import CircularLaw.EmpiricalPrefixMeans
import CircularLaw.SqueezeRoundingError

/-!
# The untruncated negative prefix on its explicit good event

No retained value below `exp(-T)` makes the negative prefix identical to
the clipped prefix. Its deviation is then bounded by the omitted-fraction
error, the full clipped-mean deviation and the deterministic integral
error. The complementary small-value event is kept in the probability
bound, including retained zeros.
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace CircularLaw

def roundedNegativePrefixMean {n : ℕ} (s : Fin n → ℝ≥0) (epsilon : ℝ)
    (hEpsilon : 0 ≤ epsilon) : ℝ :=
  empiricalNonnegativePrefixMean s (bernoulli_squeeze_prefix_le hEpsilon) hermitizationNegativeLog

def empiricalPrefixHasZero {n : ℕ} (s : Fin n → ℝ≥0) (ell : ℕ) : Prop :=
  ∃ j, j.val < ell ∧ s j = 0

theorem empirical_prefix_zero_subset_small {n ell : ℕ} (s : Fin n → ℝ≥0)
    {a : ℝ} (ha : 0 < a) (hZero : empiricalPrefixHasZero s ell) :
    empiricalPrefixHasSmall s ell a := by
  obtain ⟨j, hj, hZero⟩ := hZero
  exact ⟨j, hj, by simpa only [hZero, NNReal.coe_zero] using ha⟩

theorem empirical_prefix_negative_error {n ell : ℕ} (s : Fin n → ℝ≥0)
    (hElln : ell ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (hGood : ¬empiricalPrefixHasSmall s ell (Real.exp (-T))) (a A : ℝ) :
    |empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog - A| ≤
      ((n - ell : ℕ) / (n : ℝ)) * T +
        |empiricalNonnegativeMean s (clippedNegativeLog T) - a| + |a - A| := by
  rw [empirical_prefix_negative_eq_clipped s hElln T hGood]
  have hError := empirical_prefix_mean_error s hElln (clippedNegativeLog T)
    (fun t => by
      rw [abs_of_nonneg (clippedNegativeLog_bounds hT t).1]
      exact (clippedNegativeLog_bounds hT t).2)
  have hOne := abs_sub_le
    (empiricalNonnegativePrefixMean s hElln (clippedNegativeLog T))
    (empiricalNonnegativeMean s (clippedNegativeLog T)) A
  have hTwo := abs_sub_le (empiricalNonnegativeMean s (clippedNegativeLog T)) a A
  linarith

theorem rounded_prefix_negative_error {n : ℕ} (s : Fin n → ℝ≥0) (hn : 0 < n)
    {epsilon T : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) (hT : 0 ≤ T)
    (hGood : ¬empiricalPrefixHasSmall s (bernoulliSqueezePrefixLength n epsilon)
      (Real.exp (-T))) (a A : ℝ) :
    |roundedNegativePrefixMean s epsilon hEpsilon - A| ≤
      (5 / 4 : ℝ) * (epsilon * T) + 2 * T / n +
        |empiricalNonnegativeMean s (clippedNegativeLog T) - a| + |a - A| := by
  have h := empirical_prefix_negative_error s (bernoulli_squeeze_prefix_le hEpsilon) hT hGood a A
  have hRound := bernoulli_squeeze_cutoff_error_upper hn hEpsilon hEpsilonOne hT
  exact h.trans (by linarith)

theorem rounded_prefix_negative_deviation_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (s : Ω → Fin n → ℝ≥0) (hn : 0 < n)
    {epsilon T : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1) (hT : 0 ≤ T)
    (delta a A : ℝ) :
    μ.real {ω | (5 / 4 : ℝ) * (epsilon * T) + 2 * T / n + delta + |a - A| <
      |roundedNegativePrefixMean (s ω) epsilon hEpsilon - A|} ≤
      μ.real {ω | empiricalPrefixHasSmall (s ω) (bernoulliSqueezePrefixLength n epsilon)
        (Real.exp (-T))} +
      μ.real {ω | delta < |empiricalNonnegativeMean (s ω) (clippedNegativeLog T) - a|} := by
  have hSubset : {ω | (5 / 4 : ℝ) * (epsilon * T) + 2 * T / n + delta + |a - A| <
      |roundedNegativePrefixMean (s ω) epsilon hEpsilon - A|} ⊆
      {ω | empiricalPrefixHasSmall (s ω) (bernoulliSqueezePrefixLength n epsilon)
        (Real.exp (-T))} ∪
      {ω | delta < |empiricalNonnegativeMean (s ω) (clippedNegativeLog T) - a|} := by
    intro ω hω
    change _ ∨ _
    by_contra h
    simp only [Set.mem_setOf_eq] at h
    push_neg at h
    have hError := rounded_prefix_negative_error (s ω) hn hEpsilon hEpsilonOne hT h.1 a A
    change (5 / 4 : ℝ) * (epsilon * T) + 2 * T / n + delta + |a - A| <
      |roundedNegativePrefixMean (s ω) epsilon hEpsilon - A| at hω
    linarith
  exact (measureReal_mono (μ := μ) hSubset).trans (measureReal_union_le _ _)

end CircularLaw
