import CircularLaw.SourceGreedyExposureConditions

/-!
# The modified height of the constructed greedy process

The actual rank gives an adapted height with the checked initial and
growth bounds. At terminal time, positive height is exactly failure to
retain rank N. A bad height step must have insertion capacity and must
reject the rank increase; the full-rank square case cannot be a bad step.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def sourceGreedyExposureHeight (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    (s : ℕ) (x : BernoulliSquareSample N) : ℕ :=
  sourceAlternatingRetainedHeight N M s (sourceGreedyPrefixRank N M r₀ β d z s x)

theorem measurable_source_greedy_exposure_height
    (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ) :
    Measurable[sourceAlternatingPrefixFiltration N M s]
      (sourceGreedyExposureHeight N M r₀ β d z s) :=
  measurable_source_alternating_retained_height _ (measurable_source_greedy_prefix_rank N M r₀ β d z s)

theorem source_greedy_exposure_height_initial {N M r₀ : ℕ}
    (hM : M ≤ N) (hr₀ : r₀ ≤ M) (hInitial : 2 * (M - r₀) ≤ N - M)
    (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    (sourceGreedyExposureHeight N M r₀ β d z 0 x : ℝ) ≤ (2 * (N - M) : ℕ) / (2 : ℝ) := by
  unfold sourceGreedyExposureHeight
  rw [source_greedy_prefix_initial_rank hM hr₀]
  exact source_alternating_retained_height_initial_bound hM hr₀ hInitial

theorem source_greedy_exposure_height_growth {N M r₀ s : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M)) (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    sourceGreedyExposureHeight N M r₀ β d z (s + 1) x ≤
      sourceGreedyExposureHeight N M r₀ β d z s x + 2 :=
  source_alternating_retained_height_growth hM hs
    (source_greedy_prefix_rank_step_bounds N M r₀ β d z s x).1

theorem source_greedy_exposure_height_terminal_zero_iff {N M r₀ : ℕ}
    (hM : M ≤ N) (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    sourceGreedyExposureHeight N M r₀ β d z (2 * (N - M)) x = 0 ↔
      sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x = N :=
  source_alternating_retained_height_terminal_zero_iff hM
    ((source_greedy_prefix_rank_le_rows N M r₀ β d z (2 * (N - M)) x).trans
      (source_alternating_prefix_rows_le N M (2 * (N - M))))

theorem source_greedy_bad_height_step_capacity {N M r₀ s : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M)) (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N)
    (hBad : sourceGreedyExposureHeight N M r₀ β d z s x - 1 <
      sourceGreedyExposureHeight N M r₀ β d z (s + 1) x) :
    sourceGreedyPrefixRank N M r₀ β d z s x < sourceAlternatingPrefixColumns N M s := by
  by_contra hNot
  have hr := source_greedy_prefix_rank_le_rows N M r₀ β d z s x
  have hrNew := source_greedy_prefix_rank_le_rows N M r₀ β d z (s + 1) x
  have hMono := (source_greedy_prefix_rank_step_bounds N M r₀ β d z s x).1
  have hOldDim := source_alternating_prefix_dimensions N M s
  have hNewDim := source_alternating_prefix_dimensions N M (s + 1)
  have hOldSum := source_alternating_prefix_dimension_sum hM hs.le
  have hNewSum := source_alternating_prefix_dimension_sum hM (by omega : s + 1 ≤ 2 * (N - M))
  have hRawNew : sourceAlternatingPrefixRows N M (s + 1) +
      sourceAlternatingPrefixColumns N M (s + 1) -
        2 * sourceGreedyPrefixRank N M r₀ β d z (s + 1) x = 1 := by omega
  have hZero : sourceGreedyExposureHeight N M r₀ β d z (s + 1) x = 0 := by
    simp [sourceGreedyExposureHeight, sourceAlternatingRetainedHeight, hRawNew,
      collapseExposureHeight]
  rw [hZero] at hBad
  omega

theorem source_greedy_bad_height_step_rejects_advance {N M r₀ s : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M)) (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N)
    (hBad : sourceGreedyExposureHeight N M r₀ β d z s x - 1 <
      sourceGreedyExposureHeight N M r₀ β d z (s + 1) x) :
    ¬ sourcePrefixRankAdvance N M s (sourceGreedyPrefixRank N M r₀ β d z s x) β d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
        (source_alternating_prefix_columns_le N M (s + 1)) x) := by
  intro hAdvance
  have hCapacity := source_greedy_bad_height_step_capacity hM hs β d z x hBad
  have hStep := source_greedy_prefix_rank_step N M r₀ β d z s x
  rw [if_pos hAdvance] at hStep
  have hDown := source_alternating_retained_height_success_down hM hs hCapacity
  unfold sourceGreedyExposureHeight at hBad
  rw [hStep] at hBad
  exact not_lt_of_ge hDown hBad

end CircularLaw
