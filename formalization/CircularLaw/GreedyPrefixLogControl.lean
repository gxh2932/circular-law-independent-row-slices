import CircularLaw.GreedyPrefixRetainedRank
import CircularLaw.RectangularRetainedPrefixMonotonicity

/-!
# Positivity and the cumulative log bound of the actual greedy process

The old shifted prefix is exactly the coordinate restriction of the next
one. Interlacing therefore preserves positive products and decreases the
log prefix when rank is unchanged. An accepted increase has the actual
positive-product and log bound in its definition. Induction proves both
invariants of the entire retained-rank process.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal

namespace CircularLaw

theorem source_raw_shifted_prefix_restriction (N M s : ℕ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M (s + 1)) ×
      Fin (sourceAlternatingPrefixColumns N M (s + 1)) → Bool) :
    sourceRawShiftedPrefix N M s z (sourcePrefixRestrictionToPrevious N M s u) =
      (sourceRawShiftedPrefix N M (s + 1) z u).submatrix
        (Fin.castLE (source_alternating_prefix_rows_mono N M (Nat.le_succ s)))
        (Fin.castLE (source_alternating_prefix_columns_mono N M (Nat.le_succ s))) := by
  ext i j
  simp [sourceRawShiftedPrefix, sourcePrefixRestrictionToPrevious,
    diagonalEmbeddedShift, bernoulliRectangularMatrix, Fin.ext_iff]

theorem source_prefix_same_rank_product_le {N M s r : ℕ} (d : ℝ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M (s + 1)) ×
      Fin (sourceAlternatingPrefixColumns N M (s + 1)) → Bool)
    (hr : r ≤ sourceAlternatingPrefixRows N M s) :
    sourcePrefixRetainedProduct N M s r d z (sourcePrefixRestrictionToPrevious N M s u) ≤
      sourcePrefixRetainedProduct N M (s + 1) r d z u := by
  have hNew := hr.trans (source_alternating_prefix_rows_mono N M (Nat.le_succ s))
  rw [sourcePrefixRetainedProduct, dif_pos hr, sourcePrefixRetainedProduct, dif_pos hNew,
    source_raw_shifted_prefix_restriction]
  exact matrix_injective_restriction_retained_product_le
    (degreeNormalizingScalar d • sourceRawShiftedPrefix N M (s + 1) z u)
    ⟨Fin.castLE (source_alternating_prefix_rows_mono N M (Nat.le_succ s)),
      Fin.castLE_injective _⟩
    ⟨Fin.castLE (source_alternating_prefix_columns_mono N M (Nat.le_succ s)),
      Fin.castLE_injective _⟩ hr hNew

theorem source_prefix_same_rank_log_le {N M s r : ℕ} (d : ℝ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M (s + 1)) ×
      Fin (sourceAlternatingPrefixColumns N M (s + 1)) → Bool)
    (hr : r ≤ sourceAlternatingPrefixRows N M s)
    (hProd : 0 < sourcePrefixRetainedProduct N M s r d z
      (sourcePrefixRestrictionToPrevious N M s u)) :
    sourcePrefixRetainedLog N M (s + 1) r d z u ≤
      sourcePrefixRetainedLog N M s r d z (sourcePrefixRestrictionToPrevious N M s u) := by
  have hNew := hr.trans (source_alternating_prefix_rows_mono N M (Nat.le_succ s))
  rw [sourcePrefixRetainedProduct, dif_pos hr, source_raw_shifted_prefix_restriction] at hProd
  rw [sourcePrefixRetainedLog, dif_pos hNew, sourcePrefixRetainedLog, dif_pos hr,
    degreeNormalizedLeadingLogPrefix, degreeNormalizedLeadingLogPrefix,
    source_raw_shifted_prefix_restriction]
  exact div_le_div_of_nonneg_right (matrix_injective_restriction_retained_log_le
    (degreeNormalizingScalar d • sourceRawShiftedPrefix N M (s + 1) z u)
    ⟨Fin.castLE (source_alternating_prefix_rows_mono N M (Nat.le_succ s)),
      Fin.castLE_injective _⟩
    ⟨Fin.castLE (source_alternating_prefix_columns_mono N M (Nat.le_succ s)),
      Fin.castLE_injective _⟩ hr hNew hProd) (Nat.cast_nonneg N)

theorem source_greedy_prefix_retained_product_pos {N M r₀ : ℕ} {β d : ℝ} {z : ℂ}
    (x : BernoulliSquareSample N)
    (hInitial : 0 < sourcePrefixRetainedProduct N M 0
      (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x)) (s : ℕ) :
    0 < sourcePrefixRetainedProduct N M s (sourceGreedyPrefixRank N M r₀ β d z s x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) := by
  induction s with
  | zero => exact hInitial
  | succ s ih =>
    rw [source_greedy_prefix_rank_step]
    split_ifs with hAdvance
    · exact hAdvance.2.1
    · apply ih.trans_le
      have hBound := source_prefix_same_rank_product_le
        (N := N) (M := M) (s := s) (r := sourceGreedyPrefixRank N M r₀ β d z s x) d z
        (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
          (source_alternating_prefix_columns_le N M (s + 1)) x)
        (source_greedy_prefix_rank_le_rows N M r₀ β d z s x)
      rw [source_prefix_restriction_to_previous_sample] at hBound
      exact hBound

def sourceRetainedRankCumulativeBudget (N r : ℕ) (β d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range r, sourceNormalizedBernoulliLogIncrement 8 β N d (N - k : ℕ)

theorem source_retained_rank_cumulative_budget_succ (N r : ℕ) (β d : ℝ) :
    sourceRetainedRankCumulativeBudget N (r + 1) β d =
      sourceRetainedRankCumulativeBudget N r β d +
        sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ) :=
  Finset.sum_range_succ _ r

theorem source_greedy_prefix_log_cumulative_bound {N M r₀ : ℕ} {β d : ℝ} {z : ℂ}
    (x : BernoulliSquareSample N)
    (hInitial : 0 < sourcePrefixRetainedProduct N M 0
      (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
        (source_alternating_prefix_columns_le N M 0) x)) (s : ℕ) :
    sourcePrefixRetainedLog N M s (sourceGreedyPrefixRank N M r₀ β d z s x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) ≤
      sourcePrefixRetainedLog N M 0 (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
        (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
          (source_alternating_prefix_columns_le N M 0) x) +
      sourceRetainedRankCumulativeBudget N (sourceGreedyPrefixRank N M r₀ β d z s x) β d -
        sourceRetainedRankCumulativeBudget N (sourceGreedyPrefixRank N M r₀ β d z 0 x) β d := by
  induction s with
  | zero => linarith
  | succ s ih =>
    rw [source_greedy_prefix_rank_step]
    split_ifs with hAdvance
    · rw [source_retained_rank_cumulative_budget_succ]
      have hLog := hAdvance.2.2
      rw [source_prefix_restriction_to_previous_sample] at hLog
      linarith
    · have hLog := source_prefix_same_rank_log_le d z
        (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
          (source_alternating_prefix_columns_le N M (s + 1)) x)
        (source_greedy_prefix_rank_le_rows N M r₀ β d z s x)
        (source_greedy_prefix_retained_product_pos x hInitial s)
      exact hLog.trans ih

end CircularLaw
