import CircularLaw.AlternatingPrefixSchedule
import CircularLaw.SourcePrefixGraphBudgets
import CircularLaw.SourceExposureGraphFailureRates

/-!
# Nested good events in the actual exposure filtration

At time s, the good event requires every graph condition tested through
time s. It is measurable using only the entries already exposed and is
nested in time. The simultaneous ambient graph event implies every
progressive event, so their failure probabilities have the checked
uniform bound and tend to zero, even at a varying terminal time.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology NNReal

namespace CircularLaw

def sourceProgressiveGraphGoodEvent (N M : ℕ) (β d : ℝ) (s : ℕ) :
    Set (BernoulliSquareSample N) :=
  {x | ∀ t, t ≤ s → SourceCurrentPrefixGraphBudget (N := N)
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M t)
      (source_alternating_prefix_columns_le N M t) x) β d}

theorem source_progressive_graph_good_current {N M s : ℕ} {β d : ℝ}
    {x : BernoulliSquareSample N} (hx : x ∈ sourceProgressiveGraphGoodEvent N M β d s) :
    SourceCurrentPrefixGraphBudget (N := N)
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x) β d := hx s le_rfl

theorem source_progressive_graph_good_nested (N M : ℕ) (β d : ℝ) {s t : ℕ} (hst : s ≤ t) :
    sourceProgressiveGraphGoodEvent N M β d t ⊆ sourceProgressiveGraphGoodEvent N M β d s := by
  intro x hx k hk
  exact hx k (hk.trans hst)

theorem measurableSet_source_progressive_graph_good (N M : ℕ) (β d : ℝ) (s : ℕ) :
    MeasurableSet[sourceAlternatingPrefixFiltration N M s]
      (sourceProgressiveGraphGoodEvent N M β d s) := by
  have hLocal (t : ℕ) (ht : t ≤ s) :
      MeasurableSet[sourceAlternatingPrefixFiltration N M s]
        {x | SourceCurrentPrefixGraphBudget (N := N)
          (bernoulliPrefixSample (source_alternating_prefix_rows_le N M t)
            (source_alternating_prefix_columns_le N M t) x) β d} :=
    (sourceAlternatingPrefixFiltration N M).mono ht _
      (measurableSet_source_current_prefix_graph_budget
        (source_alternating_prefix_rows_le N M t) (source_alternating_prefix_columns_le N M t) β d)
  simpa only [sourceProgressiveGraphGoodEvent, Set.setOf_forall] using
    MeasurableSet.iInter (fun t => MeasurableSet.iInter (fun ht : t ≤ s => hLocal t ht))

theorem source_global_graph_event_subset_progressive_good {N M : ℕ}
    (hM : M ≤ N) (hRows : 3 * (N : ℝ) / 4 ≤ M) (β d : ℝ) (s : ℕ) :
    {x : BernoulliSquareSample N |
      BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β d} ⊆
        sourceProgressiveGraphGoodEvent N M β d s := by
  intro x hx t _
  apply source_global_graph_budget_current_prefix
    (source_alternating_prefix_rows_le N M t) (source_alternating_prefix_columns_le N M t) x _ hx
  exact hRows.trans (by exact_mod_cast source_alternating_prefix_rows_ge_initial hM t)

theorem bernoulli_source_progressive_graph_failure_le {N M : ℕ}
    (hN : 0 < N) (hM : M ≤ N) (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d)
    (hβ : 0 < β) (hβOne : β ≤ 1) (s : ℕ) :
    (bernoulliSquareMatrixLaw N p hp).real (sourceProgressiveGraphGoodEvent N M β d s)ᶜ ≤
      sourceExposureGraphFailureError N d := by
  have hSubset : (sourceProgressiveGraphGoodEvent N M β d s)ᶜ ⊆
      {x : BernoulliSquareSample N |
        ¬ BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β d} := by
    intro x hx hGood
    exact hx (source_global_graph_event_subset_progressive_good hM hRows β d s hGood)
  exact (measureReal_mono hSubset (measure_ne_top _ _)).trans
    (bernoulli_bidirectional_source_exposure_graph_failure hN p hp hHalf hDegree hd hβ hβOne)

theorem bernoulli_source_progressive_graph_failure_tendsto
    (p : ℕ → ℝ≥0) (hp : ∀ n, p n ≤ 1) (hHalf : ∀ᶠ n in atTop, (p n : ℝ) ≤ 1 / 2)
    (hD : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop)
    (M s : ℕ → ℕ) (hM : ∀ᶠ n in atTop, M n ≤ n)
    (hRows : ∀ᶠ n : ℕ in atTop, 3 * (n : ℝ) / 4 ≤ M n)
    {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    Tendsto (fun n => (bernoulliSquareMatrixLaw n (p n) (hp n)).real
      (sourceProgressiveGraphGoodEvent n (M n) β ((n : ℝ) * p n) (s n))ᶜ) atTop (𝓝 0) := by
  have hGlobal := bernoulli_bidirectional_source_exposure_graph_failure_tendsto p hp hHalf hD hβ hβOne
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hGlobal
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hM, hRows] with n hn hnRows
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx hGood
  exact hx (source_global_graph_event_subset_progressive_good hn hnRows β ((n : ℝ) * p n) (s n) hGood)

end CircularLaw
