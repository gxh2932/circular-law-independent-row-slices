import CircularLaw.SourceGreedyExposureConditions
import CircularLaw.BernoulliPrefixInsertionViews

/-!
# The conditional row estimate with the actual greedy retained rank

The past-dependent rank is the constructed greedy policy. Its progressive
good event, current height and initial omitted fraction discharge every
local insertion condition. The scalar degree and raw shift range remain
the explicit numerical hypotheses of the source estimate.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def sourceFreshRowDiagonalShift (a m : ℕ) (z : ℂ) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (fun j => if j.val = a then -z else 0)

theorem source_fresh_row_diagonal_shift_last (m : ℕ) (z : ℂ) :
    sourceFreshRowDiagonalShift m (m + 1) z = sourceLastDiagonalRowShift m z := by
  ext j
  simp [sourceFreshRowDiagonalShift, sourceLastDiagonalRowShift, Fin.ext_iff]

theorem source_alternating_prefix_rows_lt_terminal {N M s : ℕ}
    (hM : M ≤ N) (hs : s < 2 * (N - M)) :
    sourceAlternatingPrefixRows N M s < N := by
  unfold sourceAlternatingPrefixRows
  omega

def sourceGreedyPrefixRowInsertionFailure (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ)
    (hNext : sourceAlternatingPrefixRows N M s + 1 ≤ N) (x : BernoulliSquareSample N) : Prop :=
  sourcePrefixRowInsertionFailure (N := N)
    ⟨Fin.castLE (source_alternating_prefix_dimensions N M s).1,
      Fin.castLE_injective (source_alternating_prefix_dimensions N M s).1⟩ z β d
    (sourceGreedyPrefixRankOnPrefix N M r₀ β d z s)
    (source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s)
    (fun _ => sourceFreshRowDiagonalShift (sourceAlternatingPrefixRows N M s)
      (sourceAlternatingPrefixColumns N M s) z)
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
      (source_alternating_prefix_columns_le N M s) x)
    (fun j => x (bernoulliFreshRowEntryEmbedding hNext (source_alternating_prefix_columns_le N M s) j))

theorem bernoulli_greedy_prefix_row_conditional_failure {N M r₀ s : ℕ}
    (hM : M ≤ N) (hr₀ : r₀ ≤ M) (hs : s < 2 * (N - M))
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β d ε : ℝ} {z : ℂ} (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbientLower : (N : ℝ) / 2 ≤ sourceAlternatingPrefixColumns N M s)
    (hFraction : ((N - r₀ : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d) :
    ∀ᵐ x ∂bernoulliSquareMatrixLaw N p hp,
      x ∈ sourceGreedyProgressiveGoodEvent N M r₀ β d z s →
      sourceGreedyPrefixRank N M r₀ β d z s x < sourceAlternatingPrefixColumns N M s →
      2 * ((2 * (N - M) - s) / 8) ≤
        sourceAlternatingRetainedHeight N M s (sourceGreedyPrefixRank N M r₀ β d z s x) →
      ((bernoulliSquareMatrixLaw N p hp)[
        ({x | sourceGreedyPrefixRowInsertionFailure N M r₀ β d z s
          (Nat.succ_le_of_lt (source_alternating_prefix_rows_lt_terminal hM hs)) x}).indicator
          (fun _ => (1 : ℝ)) | sourceAlternatingPrefixFiltration N M s]) x ≤
        normalizedSourceProjectionFailureBound ε d := by
  let a := sourceAlternatingPrefixRows N M s
  let m := sourceAlternatingPrefixColumns N M s
  let e : Fin a ↪ Fin m :=
    ⟨Fin.castLE (source_alternating_prefix_dimensions N M s).1,
      Fin.castLE_injective (source_alternating_prefix_dimensions N M s).1⟩
  let r := sourceGreedyPrefixRankOnPrefix N M r₀ β d z s
  let hr := source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s
  let G := fun u : Fin a × Fin m → Bool =>
    SourceNormalizedInsertionConditions (N := N) (bernoulliRectangularMatrix u) e z (hr u) β d ε
  have hConditional := bernoulli_prefix_row_conditional_normalized_failure
    (source_alternating_prefix_rows_le N M s) (source_alternating_prefix_columns_le N M s)
    (Nat.succ_le_of_lt (source_alternating_prefix_rows_lt_terminal hM hs))
    p hp hpPos hHalf e z hβ hβOne hd hDegree hAmbientLower hε hz hzUpper
    r hr (fun _ => sourceFreshRowDiagonalShift a m z) G (fun _ h => h)
  filter_upwards [hConditional] with x hx hGood hCapacity hActive
  exact hx (source_greedy_exposure_conditions hM hr₀ hs.le
    ((Real.exp_pos 4).trans_le hd) hFraction x hGood hCapacity hActive)

end CircularLaw
