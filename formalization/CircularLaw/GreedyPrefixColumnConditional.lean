import CircularLaw.GreedyPrefixRowConditional

/-!
# The actual greedy conditional column estimate

At square times both graph orientations are available. Conjugating the
raw shift identifies the adjoint row estimate with the forward column
estimate. The same adapted rank and current good event therefore supply
the source column conditions.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

theorem source_square_prefix_exposure_conditions_adjoint {N a m r : ℕ}
    (u : Fin a × Fin m → Bool) (hSquare : a = m) (hRow : r ≤ a) (hCol : r ≤ m)
    {β d ε : ℝ} {z : ℂ}
    (hGraph : SourceCurrentPrefixGraphBudget (N := N) u β d)
    (hForward : SourceNormalizedInsertionConditions (N := N) (bernoulliRectangularMatrix u)
      ⟨Fin.castLE hSquare.le, Fin.castLE_injective hSquare.le⟩ z hRow β d ε) :
    SourceNormalizedInsertionConditions (N := N) (bernoulliRectangularMatrix u).conjTranspose
      ⟨Fin.castLE hSquare.ge, Fin.castLE_injective hSquare.ge⟩ (star z) hCol β d ε := by
  subst m
  have hAdjoint := (hGraph.1 rfl).2
  have hProduct : 0 < leadingRowSingularProduct
      (diagonalEmbeddedShift (bernoulliRectangularMatrix u).conjTranspose
        (Function.Embedding.refl _) (star z)) hCol := by
    rw [← bernoulli_shifted_square_prefix_adjoint,
      ← leading_row_singular_product_conjTranspose (bernoulliShiftedSquarePrefix u z) hRow hCol]
    exact hForward.oldProduct
  exact ⟨hForward.nextRank, hProduct, hForward.barrier, hForward.fraction,
    hAdjoint.1, hAdjoint.2.1, hAdjoint.2.2⟩

def sourceGreedyPrefixColumnInsertionFailure (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ)
    (hSquare : sourceAlternatingPrefixRows N M s = sourceAlternatingPrefixColumns N M s)
    (hNext : sourceAlternatingPrefixColumns N M s + 1 ≤ N)
    (x : BernoulliSquareSample N) : Prop :=
  sourcePrefixAdjointColumnInsertionFailure (N := N)
    ⟨Fin.castLE hSquare.ge, Fin.castLE_injective hSquare.ge⟩ (star z) β d
    (sourceGreedyPrefixRankOnPrefix N M r₀ β d z s)
    (source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s) (fun _ => 0)
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
      (source_alternating_prefix_columns_le N M s) x)
    (fun i => x (bernoulliFreshColumnEntryEmbedding (source_alternating_prefix_rows_le N M s) hNext i))

theorem bernoulli_greedy_prefix_column_conditional_failure {N M r₀ s : ℕ}
    (hM : M ≤ N) (hr₀ : r₀ ≤ M) (hs : s < 2 * (N - M))
    (hSquare : sourceAlternatingPrefixRows N M s = sourceAlternatingPrefixColumns N M s)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β d ε : ℝ} {z : ℂ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbientLower : (N : ℝ) / 2 ≤ sourceAlternatingPrefixRows N M s)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d) :
    ∀ᵐ x ∂bernoulliSquareMatrixLaw N p hp,
      x ∈ sourceGreedyProgressiveGoodEvent N M r₀ β d z s →
      sourceGreedyPrefixRank N M r₀ β d z s x < sourceAlternatingPrefixColumns N M s →
      2 * ((2 * (N - M) - s) / 8) ≤
        sourceAlternatingRetainedHeight N M s (sourceGreedyPrefixRank N M r₀ β d z s x) →
      ((bernoulliSquareMatrixLaw N p hp)[
        ({x | sourceGreedyPrefixColumnInsertionFailure N M r₀ β d z s hSquare
          (by
            rw [← hSquare]
            exact Nat.succ_le_of_lt (source_alternating_prefix_rows_lt_terminal hM hs)) x}).indicator
          (fun _ => (1 : ℝ)) | sourceAlternatingPrefixFiltration N M s]) x ≤
        normalizedSourceProjectionFailureBound ε d := by
  let a := sourceAlternatingPrefixColumns N M s
  let m := sourceAlternatingPrefixRows N M s
  let e : Fin a ↪ Fin m := ⟨Fin.castLE hSquare.ge, Fin.castLE_injective hSquare.ge⟩
  let r := sourceGreedyPrefixRankOnPrefix N M r₀ β d z s
  let hrm := source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s
  let hr := fun u => (hrm u).trans hSquare.le
  let G := fun u : Fin m × Fin a → Bool =>
    SourceNormalizedInsertionConditions (N := N) (bernoulliRectangularMatrix u).conjTranspose
      e (star z) (hr u) β d ε
  have hNext : a + 1 ≤ N := by
    dsimp only [a]
    rw [← hSquare]
    exact Nat.succ_le_of_lt (source_alternating_prefix_rows_lt_terminal hM hs)
  have hConditional := bernoulli_prefix_adjoint_column_conditional_normalized_failure
    (source_alternating_prefix_columns_le N M s) (source_alternating_prefix_rows_le N M s) hNext
    p hp hpPos hHalf e (star z) hβ hβOne hd hDegree hAmbientLower hε
    (by simpa only [norm_star] using hz) (by simpa only [norm_star] using hzUpper)
    r hr hrm (fun _ => 0) G (fun _ h => h)
  filter_upwards [hConditional] with x hx hGood hCapacity hActive
  have hForward := source_greedy_exposure_conditions hM hr₀ hs.le
    ((Real.exp_pos 4).trans_le hd) hFraction x hGood hCapacity hActive
  exact hx (source_square_prefix_exposure_conditions_adjoint _ hSquare
    (source_greedy_prefix_rank_le_rows N M r₀ β d z s x)
    ((source_greedy_prefix_rank_le_rows N M r₀ β d z s x).trans hSquare.le)
    (source_progressive_graph_good_current hGood.2) hForward)

end CircularLaw
