import CircularLaw.EmpiricalWeakConvergence
import CircularLaw.VaryingProbabilityTransfer
import CircularLaw.RetainedPrefixSmallValues

/-!
# Bounded empirical tests on an actual retained prefix

The prefix sum keeps the manuscript's denominator `n`, rather than the
prefix length. Its exact difference from the full empirical mean is
bounded by the omitted fraction times the test-function bound.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace CircularLaw

def retainedPrefixIndices {n ell : ℕ} (hElln : ell ≤ n) : Finset (Fin n) :=
  Finset.univ.image (Fin.castLE hElln)

theorem retainedPrefixIndices_card {n ell : ℕ} (hElln : ell ≤ n) :
    (retainedPrefixIndices hElln).card = ell := by
  rw [retainedPrefixIndices, Finset.card_image_of_injective _ (Fin.castLE_injective hElln)]
  simp only [Finset.card_univ, Fintype.card_fin]

theorem retainedPrefixIndices_sum {n ell : ℕ} (hElln : ell ≤ n) (f : Fin n → ℝ) :
    (∑ j ∈ retainedPrefixIndices hElln, f j) = ∑ j : Fin ell, f (Fin.castLE hElln j) := by
  rw [retainedPrefixIndices, Finset.sum_image (fun _ _ _ _ h => Fin.castLE_injective hElln h)]

theorem retained_prefix_sum_error {n ell : ℕ} (hElln : ell ≤ n) (f : Fin n → ℝ)
    {M : ℝ} (hM : ∀ j, |f j| ≤ M) :
    |(∑ j : Fin ell, f (Fin.castLE hElln j)) - ∑ j : Fin n, f j| ≤ (n - ell : ℕ) * M := by
  let S := retainedPrefixIndices hElln
  have hCard : (Finset.univ \ S).card = n - ell := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin, S, retainedPrefixIndices_card]
  have hSplit := Finset.sum_sdiff (f := f) (Finset.subset_univ S)
  have hDiff : (∑ j : Fin n, f j) - ∑ j ∈ S, f j = ∑ j ∈ Finset.univ \ S, f j := by
    linarith
  rw [← retainedPrefixIndices_sum, abs_sub_comm, hDiff]
  calc
    _ ≤ ∑ j ∈ Finset.univ \ S, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.univ \ S, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hCard]

def empiricalNonnegativePrefixMean {n ell : ℕ} (s : Fin n → ℝ≥0) (hElln : ell ≤ n)
    (f : ℝ≥0 → ℝ) : ℝ := (∑ j : Fin ell, f (s (Fin.castLE hElln j))) / n

theorem empirical_prefix_mean_error {n ell : ℕ} (s : Fin n → ℝ≥0) (hElln : ell ≤ n)
    (f : ℝ≥0 → ℝ) {M : ℝ} (hM : ∀ t, |f t| ≤ M) :
    |empiricalNonnegativePrefixMean s hElln f - empiricalNonnegativeMean s f| ≤
      ((n - ell : ℕ) / (n : ℝ)) * M := by
  simp only [empiricalNonnegativePrefixMean, empiricalNonnegativeMean, finiteMean,
    Fintype.card_fin, ← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h := div_le_div_of_nonneg_right (retained_prefix_sum_error hElln
    (fun j => f (s j)) (fun j => hM (s j))) (Nat.cast_nonneg n)
  simpa only [mul_div_right_comm] using h

theorem empirical_prefix_bounded_test_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (hM : ∃ M : ℝ, ∀ t, |f t| ≤ M) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) f) (∫ t, f t ∂ν) := by
  obtain ⟨M, hM⟩ := hM
  apply varying_probability_of_uniform_error μ (hWeak f hf ⟨M, hM⟩)
    (show Tendsto (fun n => ((n - ell n : ℕ) / (n : ℝ)) * M) atTop (𝓝 0) from by
      simpa only [zero_mul] using hRemoved.mul_const M)
  exact Eventually.of_forall (fun n ω => empirical_prefix_mean_error (s n ω) (hElln n) f hM)

theorem empirical_prefix_clipped_negative_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) : VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) (clippedNegativeLog T))
      (∫ t, clippedNegativeLog T t ∂ν) :=
  empirical_prefix_bounded_test_convergence μ s ν ell hElln hWeak hRemoved
    (clippedNegativeLog T) (continuous_clippedNegativeLog T) ⟨T, fun t => by
      rw [abs_of_nonneg (clippedNegativeLog_bounds hT t).1]
      exact (clippedNegativeLog_bounds hT t).2⟩

theorem empirical_prefix_clipped_positive_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) : VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) (clippedPositiveLog T))
      (∫ t, clippedPositiveLog T t ∂ν) :=
  empirical_prefix_bounded_test_convergence μ s ν ell hElln hWeak hRemoved
    (clippedPositiveLog T) (continuous_clippedPositiveLog T) ⟨T, fun t => by
      rw [abs_of_nonneg (clippedPositiveLog_bounds hT t).1]
      exact (clippedPositiveLog_bounds hT t).2⟩

theorem empirical_prefix_negative_eq_clipped {n ell : ℕ} (s : Fin n → ℝ≥0)
    (hElln : ell ≤ n) (T : ℝ)
    (hGood : ¬empiricalPrefixHasSmall s ell (Real.exp (-T))) :
    empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog =
      empiricalNonnegativePrefixMean s hElln (clippedNegativeLog T) := by
  apply congrArg (fun u : ℝ => u / (n : ℝ))
  apply Finset.sum_congr rfl
  intro j _
  have hFloor : Real.exp (-T) ≤ (s (Fin.castLE hElln j) : ℝ) := by
    apply le_of_not_gt
    intro h
    exact hGood ⟨Fin.castLE hElln j, j.isLt, h⟩
  simp only [clippedNegativeLog, max_eq_left hFloor, hermitizationNegativeLog]

theorem empirical_prefix_positive_of_no_small {n ell : ℕ} (s : Fin n → ℝ≥0)
    {a : ℝ} (ha : 0 < a) (hGood : ¬empiricalPrefixHasSmall s ell a)
    (j : Fin n) (hj : j.val < ell) : 0 < (s j : ℝ) := by
  exact ha.trans_le (le_of_not_gt (fun h => hGood ⟨j, hj, h⟩))

end CircularLaw
