import CircularLaw.EmpiricalPrefixMeans
import CircularLaw.EmpiricalPositiveLogConvergence

/-!
# Positive logarithms on a prefix omitting a vanishing fraction

Tight second moments control the full positive-log clipping excess.
The omitted clipped terms are bounded by their fraction times the cutoff.
Thus the positive prefix has the same limit as the full positive mean.
The proof does not require an ordered array or positive singular values.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace CircularLaw

theorem empirical_prefix_mean_mono {n ell : ℕ} (s : Fin n → ℝ≥0) (hElln : ell ≤ n)
    {f g : ℝ≥0 → ℝ} (hfg : ∀ t, f t ≤ g t) :
    empiricalNonnegativePrefixMean s hElln f ≤ empiricalNonnegativePrefixMean s hElln g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => hfg (s (Fin.castLE hElln j))))
    (Nat.cast_nonneg n)

theorem empirical_prefix_mean_le_full_of_nonneg {n ell : ℕ} (s : Fin n → ℝ≥0)
    (hElln : ell ≤ n) {f : ℝ≥0 → ℝ} (hf : ∀ t, 0 ≤ f t) :
    empiricalNonnegativePrefixMean s hElln f ≤ empiricalNonnegativeMean s f := by
  simp only [empiricalNonnegativePrefixMean, empiricalNonnegativeMean, finiteMean, Fintype.card_fin]
  rw [← retainedPrefixIndices_sum hElln (fun j => f (s j))]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf (s j)))
    (Nat.cast_nonneg n)

theorem empirical_prefix_positive_log_error {n ell : ℕ} (s : Fin n → ℝ≥0)
    (hElln : ell ≤ n) {T : ℝ} (hT : 0 < T) :
    0 ≤ empiricalNonnegativeMean s hermitizationPositiveLog -
        empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog ∧
      empiricalNonnegativeMean s hermitizationPositiveLog -
        empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog ≤
      ((n - ell : ℕ) / (n : ℝ)) * T +
        (1 / T) * empiricalNonnegativeMean s (fun t => (t : ℝ) ^ 2) := by
  constructor
  · exact sub_nonneg.mpr (empirical_prefix_mean_le_full_of_nonneg s hElln
      hermitizationPositiveLog_nonneg)
  · have hClip := empirical_prefix_mean_error s hElln (clippedPositiveLog T)
      (fun t => by
        rw [abs_of_nonneg (clippedPositiveLog_bounds hT.le t).1]
        exact (clippedPositiveLog_bounds hT.le t).2)
    have hExcess := (empirical_positive_log_excess_bounds s hT).2
    have hPrefix := empirical_prefix_mean_mono s hElln (fun t => min_le_left (hermitizationPositiveLog t) T)
    change empiricalNonnegativePrefixMean s hElln (clippedPositiveLog T) ≤
      empiricalNonnegativePrefixMean s hElln hermitizationPositiveLog at hPrefix
    have hAbs := neg_le_abs
      (empiricalNonnegativePrefixMean s hElln (clippedPositiveLog T) -
        empiricalNonnegativeMean s (clippedPositiveLog T))
    linarith

theorem empirical_prefix_positive_log_difference_tendsto {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ (fun n ω =>
      empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
        empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationPositiveLog) 0 := by
  apply varying_probability_of_error_bound μ
  intro epsilon hEpsilon delta hDelta
  obtain ⟨M, hM, hTight⟩ := hMoment delta hDelta
  let T := 2 * M / epsilon
  have hT : 0 < T := by dsimp [T]; positivity
  have hScale : (1 / T) * M = epsilon / 2 := by
    dsimp [T]
    field_simp
  have hFractionLimit : Tendsto (fun n => ((n - ell n : ℕ) / (n : ℝ)) * T) atTop (𝓝 0) := by
    simpa only [zero_mul] using hRemoved.mul_const T
  have hFraction := hFractionLimit.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < epsilon / 2))
  filter_upwards [hTight, hFraction] with n hnMoment hnFraction
  have hSubset : {ω | epsilon < |(empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
      empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationPositiveLog) - 0|} ⊆
      {ω | M < |empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)|} := by
    intro ω hω
    by_contra h
    have hMomentN : empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2) ≤ M :=
      (le_abs_self _).trans (le_of_not_gt h)
    obtain ⟨hNonneg, hError⟩ := empirical_prefix_positive_log_error (s n ω) (hElln n) hT
    have hScaleN := mul_le_mul_of_nonneg_left hMomentN (by positivity : (0 : ℝ) ≤ 1 / T)
    rw [hScale] at hScaleN
    change epsilon < |(empiricalNonnegativeMean (s n ω) hermitizationPositiveLog -
      empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationPositiveLog) - 0| at hω
    rw [sub_zero, abs_of_nonneg hNonneg] at hω
    linarith
  exact (measureReal_mono (μ := μ n) hSubset).trans_lt hnMoment

theorem empirical_prefix_positive_log_convergence {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : Integrable (fun t : ℝ≥0 => Real.log (t : ℝ)) ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationPositiveLog)
      (∫ t, hermitizationPositiveLog t ∂ν) := by
  have hFull := empirical_positive_log_convergence μ s ν hWeak hLog hMoment
  have hDifference := empirical_prefix_positive_log_difference_tendsto μ s ell hElln hRemoved hMoment
  simpa only [sub_sub_cancel, sub_zero] using varying_probability_sub μ hFull hDifference

end CircularLaw
