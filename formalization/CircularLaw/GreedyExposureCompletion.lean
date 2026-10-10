import CircularLaw.GreedyConditionalDrift
import CircularLaw.WideBarrierGoodEventCoupling
import CircularLaw.GreedyTerminalLogBound

/-!
# Actual Bernoulli greedy completion and the prefix upper probability

Every conditional drift input is discharged for the constructed process.
Terminal rank failure is bounded by the initial positive-product failure,
the simultaneous graph error and the checked drift error. Positivity and
the cumulative actual log estimate then give the finite full-to-initial
prefix upper probability, with zero terminal products included explicitly.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def sourceGreedyTerminalPrefixBadEvent (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) :
    Set (BernoulliSquareSample N) :=
  {x : BernoulliSquareSample N |
    sourcePrefixRetainedProduct N M (2 * (N - M)) N d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (2 * (N - M)))
        (source_alternating_prefix_columns_le N M (2 * (N - M))) x) = 0 ∨
    sourcePrefixRetainedLog N M 0 r₀ d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x) +
      sourceNormalizedLogErrorBound 8 β ((N - r₀ : ℕ) / (N : ℝ)) d <
    sourcePrefixRetainedLog N M (2 * (N - M)) N d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (2 * (N - M)))
        (source_alternating_prefix_columns_le N M (2 * (N - M))) x)}

theorem bernoulli_greedy_terminal_rank_failure_le {N M r₀ : ℕ}
    (hN : 0 < N) (hM : M ≤ N) (hr₀ : r₀ ≤ M)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (hInitial : 2 * (M - r₀) ≤ N - M)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β d ε : ℝ} {z : ℂ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 1024 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d) :
    (bernoulliSquareMatrixLaw N p hp).real
      {x | sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x ≠ N} ≤
      (bernoulliSquareMatrixLaw N p hp).real (sourceGreedyInitialPositiveEvent N M r₀ β d z)ᶜ +
        sourceExposureGraphFailureError N d + 16 * normalizedSourceProjectionFailureBound ε d ^ (1 / 8 : ℝ) := by
  have hd4 : Real.exp 4 ≤ d :=
    (Real.exp_le_exp.mpr (by norm_num : (4 : ℝ) ≤ 1024)).trans hd
  have hHalfRows : (N : ℝ) / 2 ≤ M := by have hn := Nat.cast_nonneg (α := ℝ) N; linarith
  have hεNonneg : 0 ≤ ε := (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hFraction
  have hq := normalized_source_projection_failure_bound_nonneg hεNonneg
    ((Real.exp_pos 4).trans_le hd4).le
  have hDone := wide_barrier_good_event_completion_bound
    (bernoulliSquareMatrixLaw N p hp) (sourceAlternatingPrefixFiltration N M)
    (sourceGreedyExposureHeight N M r₀ β d z) (sourceGreedyProgressiveGoodEvent N M r₀ β d z)
    (2 * (N - M))
    (fun s _ => measurable_source_greedy_exposure_height N M r₀ β d z s)
    (fun s _ => measurableSet_source_greedy_progressive_good N M r₀ β d z s)
    (fun s _ => source_greedy_progressive_good_nested N M r₀ β d z (Nat.le_succ s))
    (source_greedy_exposure_height_initial hM hr₀ hInitial β d z)
    (fun s hs => source_greedy_exposure_height_growth hM hs β d z)
    hq (fun s hs => bernoulli_greedy_exposure_conditional_drift hM hr₀ hs hHalfRows
      p hp hpPos hHalf hβ hβOne hd4 hDegree hFraction hε hz hzUpper)
  have hEvent : {x : BernoulliSquareSample N | 0 < sourceGreedyExposureHeight N M r₀ β d z (2 * (N - M)) x} =
      {x | sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x ≠ N} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Nat.pos_iff_ne_zero]
    exact not_congr (source_greedy_exposure_height_terminal_zero_iff hM β d z x)
  rw [hEvent] at hDone
  have hGoodFailure := source_greedy_progressive_failure_le
    (N := N) (M := M) (r₀ := r₀) (s := 2 * (N - M)) p hp β d z
  have hGraphFailure := bernoulli_source_progressive_graph_failure_le hN hM hRows
    p hp hHalf hDegree hd hβ hβOne (2 * (N - M))
  linarith

theorem source_greedy_terminal_prefix_bad_subset {N M r₀ : ℕ} {β d : ℝ} {z : ℂ}
    (hN : 0 < N) (hM : M ≤ N) (hr₀ : r₀ ≤ M)
    (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 1 ≤ d) :
    sourceGreedyTerminalPrefixBadEvent N M r₀ β d z ⊆
      (sourceGreedyInitialPositiveEvent N M r₀ β d z)ᶜ ∪
        {x | sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x ≠ N} := by
  intro x hx
  by_cases hInitial : x ∈ sourceGreedyInitialPositiveEvent N M r₀ β d z
  · by_cases hTerminal : sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x = N
    · have hPositive := source_greedy_prefix_retained_product_pos x hInitial (2 * (N - M))
      rw [hTerminal] at hPositive
      have hLog := source_greedy_prefix_terminal_log_bound hN hβ hβOne hd x hInitial hTerminal
      rw [source_greedy_prefix_initial_rank hM hr₀] at hLog
      rcases hx with hZero | hLarge
      · exact False.elim (hPositive.ne' hZero)
      · exact False.elim (not_lt_of_ge hLog hLarge)
    · exact Or.inr hTerminal
  · exact Or.inl hInitial

theorem bernoulli_greedy_terminal_prefix_upper_probability {N M r₀ : ℕ}
    (hN : 0 < N) (hM : M ≤ N) (hr₀ : r₀ ≤ M)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (hInitial : 2 * (M - r₀) ≤ N - M)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β d ε : ℝ} {z : ℂ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 1024 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d) :
    (bernoulliSquareMatrixLaw N p hp).real (sourceGreedyTerminalPrefixBadEvent N M r₀ β d z) ≤
      2 * (bernoulliSquareMatrixLaw N p hp).real (sourceGreedyInitialPositiveEvent N M r₀ β d z)ᶜ +
        sourceExposureGraphFailureError N d + 16 * normalizedSourceProjectionFailureBound ε d ^ (1 / 8 : ℝ) := by
  have hdOne : 1 ≤ d := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp 1024 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1024)
      _ ≤ d := hd
  have hRank := bernoulli_greedy_terminal_rank_failure_le hN hM hr₀ hRows hInitial
    p hp hpPos hHalf hβ hβOne hd hDegree hFraction hε hz hzUpper
  have hSubset := source_greedy_terminal_prefix_bad_subset (β := β) (d := d) (z := z)
    hN hM hr₀ hβ hβOne hdOne
  have hUnion := (measureReal_mono (μ := bernoulliSquareMatrixLaw N p hp) hSubset).trans
    (measureReal_union_le _ _)
  linarith

end CircularLaw
