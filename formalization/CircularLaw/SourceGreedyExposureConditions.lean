import CircularLaw.GreedyPrefixLogControl
import CircularLaw.SourceProgressiveGraphEvents
import CircularLaw.SourceConditionalInsertion

/-!
# Actual good events supply the greedy insertion conditions

The initial positive-product event is measurable at time zero. Intersecting
it with the progressive graph event gives nested currently measurable good
events. Rank monotonicity bounds the remaining fraction by its initial
value, and the wider height barrier gives the strict insertion guard.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

theorem source_current_graph_budget_canonical {N a m : ℕ}
    (u : Fin a × Fin m → Bool) (ham : a ≤ m) (hma : m ≤ a + 1) {β d : ℝ}
    (hGood : SourceCurrentPrefixGraphBudget (N := N) u β d) :
    SourcePrefixGraphBudget (N := N) (bernoulliRectangularMatrix u)
      ⟨Fin.castLE ham, Fin.castLE_injective ham⟩ β d := by
  by_cases hSquare : a = m
  · subst m
    exact (hGood.1 rfl).1
  · have hRectangle : m = a + 1 := by omega
    subst m
    exact hGood.2 rfl

theorem source_greedy_prefix_initial_rank {N M r₀ : ℕ}
    (hM : M ≤ N) (hr : r₀ ≤ M) (β d : ℝ) (z : ℂ) (x : BernoulliSquareSample N) :
    sourceGreedyPrefixRank N M r₀ β d z 0 x = r₀ := by
  simp only [sourceGreedyPrefixRank, sourceGreedyPrefixRankOnPrefix,
    (source_alternating_prefix_initial hM).1, min_eq_left hr]

theorem source_greedy_prefix_remaining_fraction_le {N M r₀ : ℕ}
    (hM : M ≤ N) (hr : r₀ ≤ M) (β d : ℝ) (z : ℂ) (s : ℕ)
    (x : BernoulliSquareSample N) :
    ((N - sourceGreedyPrefixRank N M r₀ β d z s x : ℕ) : ℝ) / N ≤
      ((N - r₀ : ℕ) : ℝ) / N := by
  have hRank := source_greedy_prefix_rank_mono N M r₀ β d z x (Nat.zero_le s)
  dsimp only at hRank
  rw [source_greedy_prefix_initial_rank hM hr] at hRank
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Nat.sub_le_sub_left hRank N

def sourceGreedyInitialPositiveEvent (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) :
    Set (BernoulliSquareSample N) :=
  {x | 0 < sourcePrefixRetainedProduct N M 0
    (sourceGreedyPrefixRank N M r₀ β d z 0 x) d z
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M 0)
      (source_alternating_prefix_columns_le N M 0) x)}

def sourceGreedyProgressiveGoodEvent (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ) :
    Set (BernoulliSquareSample N) :=
  sourceGreedyInitialPositiveEvent N M r₀ β d z ∩ sourceProgressiveGraphGoodEvent N M β d s

theorem measurableSet_source_greedy_initial_positive (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) :
    MeasurableSet[sourceAlternatingPrefixFiltration N M 0]
      (sourceGreedyInitialPositiveEvent N M r₀ β d z) :=
  measurableSet_bernoulli_prefix_event (source_alternating_prefix_rows_le N M 0)
    (source_alternating_prefix_columns_le N M 0) (fun u =>
      0 < sourcePrefixRetainedProduct N M 0
        (sourceGreedyPrefixRankOnPrefix N M r₀ β d z 0 u) d z u)

theorem measurableSet_source_greedy_progressive_good
    (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ) :
    MeasurableSet[sourceAlternatingPrefixFiltration N M s]
      (sourceGreedyProgressiveGoodEvent N M r₀ β d z s) :=
  ((sourceAlternatingPrefixFiltration N M).mono (Nat.zero_le s) _
    (measurableSet_source_greedy_initial_positive N M r₀ β d z)).inter
      (measurableSet_source_progressive_graph_good N M β d s)

theorem source_greedy_progressive_good_nested (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    {s t : ℕ} (hst : s ≤ t) :
    sourceGreedyProgressiveGoodEvent N M r₀ β d z t ⊆
      sourceGreedyProgressiveGoodEvent N M r₀ β d z s := by
  intro x hx
  exact ⟨hx.1, source_progressive_graph_good_nested N M β d hst hx.2⟩

theorem source_greedy_progressive_good_product_pos {N M r₀ s : ℕ} {β d : ℝ} {z : ℂ}
    {x : BernoulliSquareSample N} (hx : x ∈ sourceGreedyProgressiveGoodEvent N M r₀ β d z s) :
    0 < sourcePrefixRetainedProduct N M s (sourceGreedyPrefixRank N M r₀ β d z s x) d z
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) :=
  source_greedy_prefix_retained_product_pos x hx.1 s

theorem source_greedy_progressive_failure_le {N M r₀ s : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (β d : ℝ) (z : ℂ) :
    (bernoulliSquareMatrixLaw N p hp).real
      (sourceGreedyProgressiveGoodEvent N M r₀ β d z s)ᶜ ≤
      (bernoulliSquareMatrixLaw N p hp).real (sourceGreedyInitialPositiveEvent N M r₀ β d z)ᶜ +
        (bernoulliSquareMatrixLaw N p hp).real (sourceProgressiveGraphGoodEvent N M β d s)ᶜ := by
  rw [sourceGreedyProgressiveGoodEvent, Set.compl_inter]
  exact measureReal_union_le _ _

theorem source_greedy_exposure_conditions {N M r₀ s : ℕ} {β d ε : ℝ} {z : ℂ}
    (hM : M ≤ N) (hr₀ : r₀ ≤ M) (hs : s ≤ 2 * (N - M)) (hd : 0 < d)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε)
    (x : BernoulliSquareSample N)
    (hx : x ∈ sourceGreedyProgressiveGoodEvent N M r₀ β d z s)
    (hNext : sourceGreedyPrefixRank N M r₀ β d z s x < sourceAlternatingPrefixColumns N M s)
    (hActive : 2 * ((2 * (N - M) - s) / 8) ≤
      sourceAlternatingRetainedHeight N M s (sourceGreedyPrefixRank N M r₀ β d z s x)) :
    SourceNormalizedInsertionConditions (N := N)
      (bernoulliRectangularMatrix (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x))
      ⟨Fin.castLE (source_alternating_prefix_dimensions N M s).1,
        Fin.castLE_injective (source_alternating_prefix_dimensions N M s).1⟩ z
      (source_greedy_prefix_rank_le_rows N M r₀ β d z s x) β d ε := by
  have hRank := source_greedy_prefix_rank_le_rows N M r₀ β d z s x
  have hPositive := source_greedy_progressive_good_product_pos hx
  rw [sourcePrefixRetainedProduct, dif_pos hRank] at hPositive
  have hRaw := (leading_row_singular_product_degree_normalization_pos_iff _ hRank hd).mp hPositive
  have hGraph := source_current_graph_budget_canonical _
    (source_alternating_prefix_dimensions N M s).1
    (source_alternating_prefix_dimensions N M s).2 (source_progressive_graph_good_current hx.2)
  exact ⟨hNext, hRaw, source_alternating_wide_barrier_insertion_guard hM hs hNext hActive,
    (source_greedy_prefix_remaining_fraction_le hM hr₀ β d z s x).trans hFraction,
    hGraph.1, hGraph.2.1, hGraph.2.2⟩

end CircularLaw
