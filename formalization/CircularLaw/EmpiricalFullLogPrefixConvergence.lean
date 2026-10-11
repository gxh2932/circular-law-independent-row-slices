import CircularLaw.NegativeLogUniformIntegrability
import CircularLaw.EmpiricalPositivePrefixConvergence
import CircularLaw.RoundedLogPrefixConvergence

/-!
# Full logarithms on every prefix omitting `o(n)` values

The negative difference is exactly the literal bottom sum. Its checked
uniform integrability, together with positive-part control, gives the
untruncated prefix limit for every vanishing removed fraction. No slow
choice is needed once the full logarithmic limit has been proved.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace CircularLaw

theorem retainedPrefixIndices_mem_iff {n ell : ℕ} (hElln : ell ≤ n) (j : Fin n) :
    j ∈ retainedPrefixIndices hElln ↔ j.val < ell := by
  simp only [retainedPrefixIndices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hj
    exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩

theorem empirical_prefix_negative_difference_eq_bottom {n ell : ℕ}
    (s : Fin n → ℝ≥0) (hElln : ell ≤ n) :
    empiricalNonnegativeMean s hermitizationNegativeLog -
      empiricalNonnegativePrefixMean s hElln hermitizationNegativeLog =
      empiricalBottomNegativeLog s (n - ell) := by
  have hSets : Finset.univ \ retainedPrefixIndices hElln = bottomLogIndices n (n - ell) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_univ, retainedPrefixIndices_mem_iff,
      true_and, not_lt, bottomLogIndices, Finset.mem_filter]
    rw [Nat.sub_sub_self hElln]
  have hSum := Finset.sum_sdiff (f := fun j => hermitizationNegativeLog (s j))
    (Finset.subset_univ (retainedPrefixIndices hElln))
  rw [hSets, retainedPrefixIndices_sum] at hSum
  simp only [empiricalNonnegativeMean, finiteMean, Fintype.card_fin,
    empiricalNonnegativePrefixMean, empiricalBottomNegativeLog, ← sub_div]
  exact congrArg (fun a : ℝ => a / n) (by linarith [hSum])

theorem empirical_bottom_negative_log_mean_converges {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2)))
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalBottomNegativeLog (s n ω) (r n)) 0 := by
  intro epsilon hEpsilon
  have hTail := empirical_bottom_log_convergence μ s ν hWeak hLog hν hMoment r hr hEpsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTail
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  apply Eventually.of_forall
  intro n
  apply measureReal_mono (h₂ := by finiteness)
  intro ω hω
  right
  have hNonneg : 0 ≤ empiricalBottomNegativeLog (s n ω) (r n) := by
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (Nat.cast_nonneg n)
  simpa only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg hNonneg] using hω

theorem empirical_prefix_negative_log_convergence_of_full {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationNegativeLog)
      (∫ t, hermitizationNegativeLog t ∂ν) := by
  have hFull := empirical_negative_log_convergence μ s ν hWeak hLog hν hMoment
  have hBottom := empirical_bottom_negative_log_mean_converges μ s ν hWeak hLog hν hMoment
    (fun n => n - ell n) hRemoved
  have hDiff : VaryingConvergesInProbability μ (fun n ω =>
      empiricalNonnegativeMean (s n ω) hermitizationNegativeLog -
        empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationNegativeLog) 0 := by
    simpa only [empirical_prefix_negative_difference_eq_bottom] using hBottom
  simpa only [sub_sub_cancel, sub_zero] using varying_probability_sub μ hFull hDiff

theorem empirical_prefix_log_convergence_of_full {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ≥0)
    (ν : Measure ℝ≥0) (ell : ℕ → ℕ) (hElln : ∀ n, ell n ≤ n)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν)
    (hLog : EmpiricalLogConvergenceInProbability μ s ν)
    (hν : FiniteLogarithmicIntegral ν)
    (hRemoved : Tendsto (fun n => (n - ell n : ℕ) / (n : ℝ)) atTop (𝓝 0))
    (hMoment : VaryingBoundedInProbability μ
      (fun n ω => empiricalNonnegativeMean (s n ω) (fun t => (t : ℝ) ^ 2))) :
    VaryingConvergesInProbability μ
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) (fun t => Real.log (t : ℝ)))
      (∫ t : ℝ≥0, Real.log (t : ℝ) ∂ν) := by
  have hPos := empirical_prefix_positive_log_convergence μ s ν ell hElln hWeak hν.2 hRemoved hMoment
  have hNeg := empirical_prefix_negative_log_convergence_of_full μ s ν ell hElln
    hWeak hLog hν hRemoved hMoment
  have h := varying_probability_sub μ hPos hNeg
  have hFunctions : (fun n ω =>
      empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationPositiveLog -
        empiricalNonnegativePrefixMean (s n ω) (hElln n) hermitizationNegativeLog) =
      (fun n ω => empiricalNonnegativePrefixMean (s n ω) (hElln n) (fun t => Real.log (t : ℝ))) := by
    funext n ω
    rw [← empirical_prefix_mean_sub]
    congr 1
    funext t
    exact (hermitization_log_decomposition t).symm
  rw [hFunctions, ← hermitization_log_integral_decomposition hν.2] at h
  exact h

end CircularLaw
