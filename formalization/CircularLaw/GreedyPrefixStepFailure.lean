import CircularLaw.AlternatingPrefixInsertionIdentities

/-!
# Actual acceptance is the complement of the insertion failure

The alternating schedule has exactly one new column at square times and
one new row at rectangular times. The dimension-transport identities
identify the policy's actual retained product and logarithm with the
conditional insertion event, including all zero products.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

theorem source_alternating_prefix_step_cases {N M s : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M)) :
    (sourceAlternatingPrefixRows N M (s + 1) = sourceAlternatingPrefixRows N M s ∧
      sourceAlternatingPrefixColumns N M (s + 1) = sourceAlternatingPrefixColumns N M s + 1 ∧
      sourceAlternatingPrefixRows N M s = sourceAlternatingPrefixColumns N M s) ∨
    (sourceAlternatingPrefixRows N M (s + 1) = sourceAlternatingPrefixRows N M s + 1 ∧
      sourceAlternatingPrefixColumns N M (s + 1) = sourceAlternatingPrefixColumns N M s ∧
      sourceAlternatingPrefixColumns N M s = sourceAlternatingPrefixRows N M s + 1) := by
  have hOld := source_alternating_prefix_dimension_sum hM hs.le
  have hNew := source_alternating_prefix_dimension_sum hM (by omega : s + 1 ≤ 2 * (N - M))
  have hRows := source_alternating_prefix_rows_mono N M (Nat.le_succ s)
  have hCols := source_alternating_prefix_columns_mono N M (Nat.le_succ s)
  have hOldDim := source_alternating_prefix_dimensions N M s
  have hNewDim := source_alternating_prefix_dimensions N M (s + 1)
  omega

theorem source_prefix_adjoint_column_failure_eq_canonical {N a m : ℕ}
    (u : Fin a × Fin m → Bool) (hSquare : a = m) (y : Fin a → Bool)
    (z : ℂ) (β d : ℝ) (r : (Fin a × Fin m → Bool) → ℕ)
    (hr : ∀ v, r v ≤ a) (hNext : r u + 1 ≤ a) :
    sourcePrefixAdjointColumnInsertionFailure (N := N)
      ⟨Fin.castLE hSquare.ge, Fin.castLE_injective hSquare.ge⟩ (star z) β d r hr (fun _ => 0) u y ↔
      degreeNormalizedColumnStepFailure d N
        (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r u : ℕ))
        (diagonalEmbeddedShift (bernoulliRectangularMatrix u)
          ⟨Fin.castLE hSquare.le, Fin.castLE_injective hSquare.le⟩ z)
        (hr u) hNext (bernoulliCubeVector y) := by
  subst m
  exact source_prefix_adjoint_column_failure_eq_square_failure u y z β d r hr hNext

theorem source_greedy_prefix_row_advance_iff_not_failure {N M r₀ s : ℕ}
    (β d : ℝ) (z : ℂ)
    (hRowStep : sourceAlternatingPrefixRows N M (s + 1) = sourceAlternatingPrefixRows N M s + 1)
    (hColStep : sourceAlternatingPrefixColumns N M (s + 1) = sourceAlternatingPrefixColumns N M s)
    (hNext : sourceAlternatingPrefixRows N M s + 1 ≤ N) (x : BernoulliSquareSample N) :
    sourcePrefixRankAdvance N M s (sourceGreedyPrefixRank N M r₀ β d z s x) β d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
        (source_alternating_prefix_columns_le N M (s + 1)) x) ↔
      ¬ sourceGreedyPrefixRowInsertionFailure N M r₀ β d z s hNext x := by
  let r := sourceGreedyPrefixRank N M r₀ β d z s x
  have hr : r ≤ sourceAlternatingPrefixRows N M s :=
    source_greedy_prefix_rank_le_rows N M r₀ β d z s x
  have hValid : r + 1 ≤ sourceAlternatingPrefixRows N M (s + 1) := by omega
  have ham : sourceAlternatingPrefixRows N M s + 1 ≤ sourceAlternatingPrefixColumns N M s := by
    have hDim := (source_alternating_prefix_dimensions N M (s + 1)).1
    omega
  let B := bernoulliShiftedAmbientPrefix hNext (source_alternating_prefix_columns_le N M s) ham z x
  have hP := source_prefix_retained_product_at_dimensions hNext
    (source_alternating_prefix_columns_le N M s) ham hRowStep hColStep (Nat.succ_le_succ hr) d z x
  have hL := source_prefix_retained_log_at_dimensions hNext
    (source_alternating_prefix_columns_le N M s) ham hRowStep hColStep (Nat.succ_le_succ hr) d z x
  have hO := source_prefix_retained_log_at_dimensions
    (source_alternating_prefix_rows_le N M s) (source_alternating_prefix_columns_le N M s)
    ((Nat.le_succ _).trans ham) rfl rfl hr d z x
  have hFailure := last_row_degree_normalized_failure_iff B hr (Nat.succ_le_succ hr) d N
    (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ))
  dsimp only [B] at hFailure
  rw [bernoulli_shifted_ambient_row_old (source_alternating_prefix_rows_le N M s)
    (source_alternating_prefix_columns_le N M s) hNext ham,
    bernoulli_shifted_ambient_row_fresh (source_alternating_prefix_columns_le N M s) hNext ham] at hFailure
  change sourceGreedyPrefixRowInsertionFailure N M r₀ β d z s hNext x ↔ _ at hFailure
  rw [sourcePrefixRankAdvance, source_prefix_restriction_to_previous_sample, hP, hL, hO,
    hFailure, not_or, not_lt]
  have hNonneg : 0 ≤ leadingRowSingularProduct (degreeNormalizingScalar d • B) (Nat.succ_le_succ hr) :=
    Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
  constructor
  · rintro ⟨_, hPositive, hLog⟩
    exact ⟨hPositive.ne', hLog⟩
  · rintro ⟨hNonzero, hLog⟩
    exact ⟨hValid, lt_of_le_of_ne hNonneg (Ne.symm hNonzero), hLog⟩

theorem source_greedy_prefix_column_advance_iff_not_failure {N M r₀ s : ℕ}
    (β d : ℝ) (z : ℂ)
    (hRowStep : sourceAlternatingPrefixRows N M (s + 1) = sourceAlternatingPrefixRows N M s)
    (hColStep : sourceAlternatingPrefixColumns N M (s + 1) = sourceAlternatingPrefixColumns N M s + 1)
    (hSquare : sourceAlternatingPrefixRows N M s = sourceAlternatingPrefixColumns N M s)
    (hNext : sourceAlternatingPrefixColumns N M s + 1 ≤ N) (x : BernoulliSquareSample N)
    (hCapacity : sourceGreedyPrefixRank N M r₀ β d z s x + 1 ≤ sourceAlternatingPrefixRows N M s) :
    sourcePrefixRankAdvance N M s (sourceGreedyPrefixRank N M r₀ β d z s x) β d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
        (source_alternating_prefix_columns_le N M (s + 1)) x) ↔
      ¬ sourceGreedyPrefixColumnInsertionFailure N M r₀ β d z s hSquare hNext x := by
  let r := sourceGreedyPrefixRank N M r₀ β d z s x
  have hr : r ≤ sourceAlternatingPrefixRows N M s :=
    source_greedy_prefix_rank_le_rows N M r₀ β d z s x
  have hValid : r + 1 ≤ sourceAlternatingPrefixRows N M (s + 1) := by omega
  have ham := (source_alternating_prefix_dimensions N M s).1
  let B := bernoulliShiftedAmbientPrefix (source_alternating_prefix_rows_le N M s) hNext
    (ham.trans (Nat.le_succ _)) z x
  have hP := source_prefix_retained_product_at_dimensions
    (source_alternating_prefix_rows_le N M s) hNext (ham.trans (Nat.le_succ _))
    hRowStep hColStep hCapacity d z x
  have hL := source_prefix_retained_log_at_dimensions
    (source_alternating_prefix_rows_le N M s) hNext (ham.trans (Nat.le_succ _))
    hRowStep hColStep hCapacity d z x
  have hO := source_prefix_retained_log_at_dimensions
    (source_alternating_prefix_rows_le N M s) (source_alternating_prefix_columns_le N M s)
    ham rfl rfl hr d z x
  have hForward := source_prefix_adjoint_column_failure_eq_canonical (N := N)
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
      (source_alternating_prefix_columns_le N M s) x) hSquare
    (fun i => x (bernoulliFreshColumnEntryEmbedding (source_alternating_prefix_rows_le N M s) hNext i))
    z β d (sourceGreedyPrefixRankOnPrefix N M r₀ β d z s)
    (source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s) hCapacity
  have hFailure := last_column_degree_normalized_failure_iff B hr hCapacity d N
    (sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ))
  dsimp only [B] at hFailure
  rw [bernoulli_shifted_ambient_column_old (source_alternating_prefix_rows_le N M s)
    (source_alternating_prefix_columns_le N M s) hNext ham,
    bernoulli_shifted_ambient_column_fresh (source_alternating_prefix_rows_le N M s) hNext ham] at hFailure
  have hFailureActual : sourceGreedyPrefixColumnInsertionFailure N M r₀ β d z s hSquare hNext x ↔ _ :=
    hForward.trans hFailure
  rw [sourcePrefixRankAdvance, source_prefix_restriction_to_previous_sample, hP, hL, hO,
    hFailureActual, not_or, not_lt]
  have hNonneg : 0 ≤ leadingRowSingularProduct (degreeNormalizingScalar d • B) hCapacity :=
    Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
  constructor
  · rintro ⟨_, hPositive, hLog⟩
    exact ⟨hPositive.ne', hLog⟩
  · rintro ⟨hNonzero, hLog⟩
    exact ⟨hValid, lt_of_le_of_ne hNonneg (Ne.symm hNonzero), hLog⟩

end CircularLaw
