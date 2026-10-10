import CircularLaw.GreedyPrefixStepFailure
import CircularLaw.GreedyExposureHeight
import CircularLaw.ExposureGoodEventCoupling

/-!
# Conditional drift of the actual greedy exposure height

At every genuine insertion time, the actual bad-height event lies in the
past-measurable insertion-capacity event and the corresponding checked
row or column failure event. Conditional comparison and the actual greedy
insertion bounds prove the drift hypothesis without assuming it.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

theorem bernoulli_greedy_exposure_conditional_drift {N M r₀ s : ℕ}
    (hM : M ≤ N) (hr₀ : r₀ ≤ M) (hs : s < 2 * (N - M))
    (hInitialRows : (N : ℝ) / 2 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β d ε : ℝ} {z : ℂ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d) :
    ∀ᵐ x ∂bernoulliSquareMatrixLaw N p hp,
      x ∈ sourceGreedyProgressiveGoodEvent N M r₀ β d z s →
      2 * ((2 * (N - M) - s) / 8) ≤ sourceGreedyExposureHeight N M r₀ β d z s x →
      ((bernoulliSquareMatrixLaw N p hp)[
        ({y | sourceGreedyExposureHeight N M r₀ β d z s y - 1 <
          sourceGreedyExposureHeight N M r₀ β d z (s + 1) y}).indicator
            (fun _ => (1 : ℝ)) | sourceAlternatingPrefixFiltration N M s]) x ≤
        normalizedSourceProjectionFailureBound ε d := by
  let μ := bernoulliSquareMatrixLaw N p hp
  let F := sourceAlternatingPrefixFiltration N M
  let A := {x : BernoulliSquareSample N |
    sourceGreedyPrefixRank N M r₀ β d z s x < sourceAlternatingPrefixColumns N M s}
  let B := {x : BernoulliSquareSample N |
    sourceGreedyExposureHeight N M r₀ β d z s x - 1 < sourceGreedyExposureHeight N M r₀ β d z (s + 1) x}
  have hAMeas : MeasurableSet[F s] A :=
    measurableSet_bernoulli_prefix_event (source_alternating_prefix_rows_le N M s)
      (source_alternating_prefix_columns_le N M s) (fun u =>
        sourceGreedyPrefixRankOnPrefix N M r₀ β d z s u < sourceAlternatingPrefixColumns N M s)
  have hBMeas : MeasurableSet B := (Set.to_countable B).measurableSet
  have hεNonneg : 0 ≤ ε :=
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hFraction
  have hq := normalized_source_projection_failure_bound_nonneg hεNonneg
    ((Real.exp_pos 4).trans_le hd).le
  have hRowsLower : (N : ℝ) / 2 ≤ sourceAlternatingPrefixRows N M s :=
    hInitialRows.trans (by exact_mod_cast source_alternating_prefix_rows_ge_initial hM s)
  have hColsLower : (N : ℝ) / 2 ≤ sourceAlternatingPrefixColumns N M s :=
    hRowsLower.trans (by exact_mod_cast (source_alternating_prefix_dimensions N M s).1)
  rcases source_alternating_prefix_step_cases hM hs with ⟨hRowStep, hColStep, hSquare⟩ |
    ⟨hRowStep, hColStep, _⟩
  · have hNext : sourceAlternatingPrefixColumns N M s + 1 ≤ N := by
      simpa only [hColStep] using source_alternating_prefix_columns_le N M (s + 1)
    let C := {x : BernoulliSquareSample N |
      sourceGreedyPrefixColumnInsertionFailure N M r₀ β d z s hSquare hNext x}
    have hCMeas : MeasurableSet C := (Set.to_countable C).measurableSet
    have hSubset : B ⊆ A ∩ C := by
      intro x hx
      have hCapacity := source_greedy_bad_height_step_capacity hM hs β d z x hx
      have hReject := source_greedy_bad_height_step_rejects_advance hM hs β d z x hx
      refine ⟨hCapacity, ?_⟩
      by_contra hNot
      have hRoom : sourceGreedyPrefixRank N M r₀ β d z s x + 1 ≤ sourceAlternatingPrefixRows N M s := by
        omega
      exact hReject ((source_greedy_prefix_column_advance_iff_not_failure β d z
        hRowStep hColStep hSquare hNext x hRoom).mpr hNot)
    have hCompare := conditional_indicator_le_past_times_bad μ (F s) (F.le s)
      hAMeas hCMeas hBMeas hSubset
    have hConditional := bernoulli_greedy_prefix_column_conditional_failure hM hr₀ hs hSquare
      p hp hpPos hHalf hβ hβOne hd hDegree hRowsLower hFraction hε hz hzUpper
    filter_upwards [hCompare, hConditional] with x hx hConditional hGood hActive
    by_cases hCapacity : x ∈ A
    · simp only [Set.indicator_of_mem hCapacity, one_mul] at hx
      exact hx.trans (hConditional hGood hCapacity hActive)
    · simp only [Set.indicator_of_notMem hCapacity, zero_mul] at hx
      exact hx.trans hq
  · have hNext : sourceAlternatingPrefixRows N M s + 1 ≤ N := by
      simpa only [hRowStep] using source_alternating_prefix_rows_le N M (s + 1)
    let C := {x : BernoulliSquareSample N |
      sourceGreedyPrefixRowInsertionFailure N M r₀ β d z s hNext x}
    have hCMeas : MeasurableSet C := (Set.to_countable C).measurableSet
    have hSubset : B ⊆ A ∩ C := by
      intro x hx
      have hCapacity := source_greedy_bad_height_step_capacity hM hs β d z x hx
      have hReject := source_greedy_bad_height_step_rejects_advance hM hs β d z x hx
      refine ⟨hCapacity, ?_⟩
      by_contra hNot
      exact hReject ((source_greedy_prefix_row_advance_iff_not_failure β d z
        hRowStep hColStep hNext x).mpr hNot)
    have hCompare := conditional_indicator_le_past_times_bad μ (F s) (F.le s)
      hAMeas hCMeas hBMeas hSubset
    have hConditional := bernoulli_greedy_prefix_row_conditional_failure hM hr₀ hs
      p hp hpPos hHalf hβ hβOne hd hDegree hColsLower hFraction hε hz hzUpper
    filter_upwards [hCompare, hConditional] with x hx hConditional hGood hActive
    by_cases hCapacity : x ∈ A
    · simp only [Set.indicator_of_mem hCapacity, one_mul] at hx
      exact hx.trans (hConditional hGood hCapacity hActive)
    · simp only [Set.indicator_of_notMem hCapacity, zero_mul] at hx
      exact hx.trans hq

end CircularLaw
