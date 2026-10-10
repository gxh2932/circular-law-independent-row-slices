import CircularLaw.GreedyPrefixLogControl

/-!
# The actual terminal greedy logarithm and its deterministic error

When the constructed greedy rank reaches N, its cumulative cost is the
literal source rank sum. The checked scalar estimate bounds that cost by
a square-root omitted fraction and a degree error tending to zero. The
probability that the rank reaches N is a separate remaining obligation.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem source_retained_rank_cumulative_budget_difference_eq {N r : ℕ}
    (hr : r ≤ N) (β d : ℝ) :
    sourceRetainedRankCumulativeBudget N N β d -
      sourceRetainedRankCumulativeBudget N r β d =
      ∑ k ∈ Finset.Ico r N,
        sourceNormalizedBernoulliLogIncrement 8 β N d (N - k : ℕ) := by
  exact (Finset.sum_Ico_eq_sub _ hr).symm

theorem source_retained_rank_terminal_budget_le {N r : ℕ} (hN : 0 < N)
    (hr : r ≤ N) {β d : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 1 ≤ d) :
    sourceRetainedRankCumulativeBudget N N β d -
      sourceRetainedRankCumulativeBudget N r β d ≤
      sourceNormalizedLogErrorBound 8 β ((N - r : ℕ) / (N : ℝ)) d := by
  rw [source_retained_rank_cumulative_budget_difference_eq hr]
  have hBound := source_normalized_log_increment_rank_sum_le hN
    (Nat.sub_le N r) (K := 8) (by norm_num) hβ hβOne hd
  simpa only [Nat.sub_sub_self hr] using hBound

theorem source_greedy_prefix_terminal_log_bound {N M r₀ : ℕ} {β d : ℝ} {z : ℂ}
    (hN : 0 < N) (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 1 ≤ d)
    (x : BernoulliSquareSample N)
    (hInitial : 0 < sourcePrefixRetainedProduct N M 0
      (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x))
    (hTerminal : sourceGreedyPrefixRank N M r₀ β d z (2 * (N - M)) x = N) :
    sourcePrefixRetainedLog N M (2 * (N - M)) N d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (2 * (N - M)))
        (source_alternating_prefix_columns_le N M (2 * (N - M))) x) ≤
      sourcePrefixRetainedLog N M 0 (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
        (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
          (source_alternating_prefix_columns_le N M 0) x) +
      sourceNormalizedLogErrorBound 8 β
        ((N - sourceGreedyPrefixRank N M r₀ β d z 0 x : ℕ) / (N : ℝ)) d := by
  have hLog := source_greedy_prefix_log_cumulative_bound x hInitial (2 * (N - M))
  rw [hTerminal] at hLog
  have hRank := (source_greedy_prefix_rank_le_rows N M r₀ β d z 0 x).trans
    (source_alternating_prefix_rows_le N M 0)
  have hBudget := source_retained_rank_terminal_budget_le hN hRank hβ hβOne hd
  linarith

end CircularLaw
