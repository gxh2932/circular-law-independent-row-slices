import CircularLaw.AlternatingRetainedHeight
import CircularLaw.SourceNormalizedLogError
import CircularLaw.LastIndexDegreeNormalizedSteps
import CircularLaw.BernoulliUniqueRowLaw

/-!
# The actual greedy retained-rank process on exposed Bernoulli prefixes

The policy retains one more singular value exactly when its actual
normalized product is positive and the normalized log increment obeys
the source budget. The recursion takes the exposed prefix as its input,
so adaptedness is proved directly. All zero products and invalid ranks
are totalized; acceptance explicitly requires a positive new product.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def sourcePrefixRestrictionToPrevious (N M s : ℕ)
    (u : Fin (sourceAlternatingPrefixRows N M (s + 1)) ×
      Fin (sourceAlternatingPrefixColumns N M (s + 1)) → Bool) :
    Fin (sourceAlternatingPrefixRows N M s) × Fin (sourceAlternatingPrefixColumns N M s) → Bool :=
  fun ij => u (Fin.castLE (source_alternating_prefix_rows_mono N M (Nat.le_succ s)) ij.1,
    Fin.castLE (source_alternating_prefix_columns_mono N M (Nat.le_succ s)) ij.2)

def sourceRawShiftedPrefix (N M s : ℕ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M s) × Fin (sourceAlternatingPrefixColumns N M s) → Bool) :
    Matrix (Fin (sourceAlternatingPrefixRows N M s)) (Fin (sourceAlternatingPrefixColumns N M s)) ℂ :=
  diagonalEmbeddedShift (bernoulliRectangularMatrix u)
    ⟨Fin.castLE (source_alternating_prefix_dimensions N M s).1,
      Fin.castLE_injective (source_alternating_prefix_dimensions N M s).1⟩ z

def sourcePrefixRetainedProduct (N M s r : ℕ) (d : ℝ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M s) × Fin (sourceAlternatingPrefixColumns N M s) → Bool) : ℝ :=
  if h : r ≤ sourceAlternatingPrefixRows N M s then
    leadingRowSingularProduct (degreeNormalizingScalar d • sourceRawShiftedPrefix N M s z u) h
  else 0

def sourcePrefixRetainedLog (N M s r : ℕ) (d : ℝ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M s) × Fin (sourceAlternatingPrefixColumns N M s) → Bool) : ℝ :=
  if h : r ≤ sourceAlternatingPrefixRows N M s then
    degreeNormalizedLeadingLogPrefix d (sourceRawShiftedPrefix N M s z u) h / N
  else 0

def sourcePrefixRankAdvance (N M s r : ℕ) (β d : ℝ) (z : ℂ)
    (u : Fin (sourceAlternatingPrefixRows N M (s + 1)) ×
      Fin (sourceAlternatingPrefixColumns N M (s + 1)) → Bool) : Prop :=
  r + 1 ≤ sourceAlternatingPrefixRows N M (s + 1) ∧
    0 < sourcePrefixRetainedProduct N M (s + 1) (r + 1) d z u ∧
      sourcePrefixRetainedLog N M (s + 1) (r + 1) d z u ≤
        sourcePrefixRetainedLog N M s r d z (sourcePrefixRestrictionToPrevious N M s u) +
          sourceNormalizedBernoulliLogIncrement 8 β N d (N - r : ℕ)

def sourceGreedyPrefixRankOnPrefix (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) :
    ∀ s, (Fin (sourceAlternatingPrefixRows N M s) ×
      Fin (sourceAlternatingPrefixColumns N M s) → Bool) → ℕ
  | 0, _ => min r₀ (sourceAlternatingPrefixRows N M 0)
  | s + 1, u =>
    let r := sourceGreedyPrefixRankOnPrefix N M r₀ β d z s (sourcePrefixRestrictionToPrevious N M s u)
    if sourcePrefixRankAdvance N M s r β d z u then r + 1 else r

def sourceGreedyPrefixRank (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ)
    (x : BernoulliSquareSample N) : ℕ :=
  sourceGreedyPrefixRankOnPrefix N M r₀ β d z s
    (bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
      (source_alternating_prefix_columns_le N M s) x)

theorem source_prefix_restriction_to_previous_sample (N M s : ℕ) (x : BernoulliSquareSample N) :
    sourcePrefixRestrictionToPrevious N M s
      (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
        (source_alternating_prefix_columns_le N M (s + 1)) x) =
      bernoulliPrefixSample (source_alternating_prefix_rows_le N M s)
        (source_alternating_prefix_columns_le N M s) x := rfl

theorem source_greedy_prefix_rank_on_prefix_le (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ)
    (u : Fin (sourceAlternatingPrefixRows N M s) × Fin (sourceAlternatingPrefixColumns N M s) → Bool) :
    sourceGreedyPrefixRankOnPrefix N M r₀ β d z s u ≤ sourceAlternatingPrefixRows N M s := by
  induction s with
  | zero => exact min_le_right _ _
  | succ s ih =>
    dsimp only [sourceGreedyPrefixRankOnPrefix]
    split_ifs with hAdvance
    · exact hAdvance.1
    · exact (ih _).trans (source_alternating_prefix_rows_mono N M (Nat.le_succ s))

theorem source_greedy_prefix_rank_le_rows (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    (s : ℕ) (x : BernoulliSquareSample N) :
    sourceGreedyPrefixRank N M r₀ β d z s x ≤ sourceAlternatingPrefixRows N M s :=
  source_greedy_prefix_rank_on_prefix_le N M r₀ β d z s _

theorem source_greedy_prefix_rank_step (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    (s : ℕ) (x : BernoulliSquareSample N) :
    sourceGreedyPrefixRank N M r₀ β d z (s + 1) x =
      if sourcePrefixRankAdvance N M s (sourceGreedyPrefixRank N M r₀ β d z s x) β d z
        (bernoulliPrefixSample (source_alternating_prefix_rows_le N M (s + 1))
          (source_alternating_prefix_columns_le N M (s + 1)) x)
      then sourceGreedyPrefixRank N M r₀ β d z s x + 1
      else sourceGreedyPrefixRank N M r₀ β d z s x := rfl

theorem source_greedy_prefix_rank_step_bounds (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    (s : ℕ) (x : BernoulliSquareSample N) :
    sourceGreedyPrefixRank N M r₀ β d z s x ≤ sourceGreedyPrefixRank N M r₀ β d z (s + 1) x ∧
      sourceGreedyPrefixRank N M r₀ β d z (s + 1) x ≤ sourceGreedyPrefixRank N M r₀ β d z s x + 1 := by
  rw [source_greedy_prefix_rank_step]
  split_ifs <;> omega

theorem source_greedy_prefix_rank_mono (N M r₀ : ℕ) (β d : ℝ) (z : ℂ)
    (x : BernoulliSquareSample N) : Monotone (fun s => sourceGreedyPrefixRank N M r₀ β d z s x) :=
  monotone_nat_of_le_succ (fun s => (source_greedy_prefix_rank_step_bounds N M r₀ β d z s x).1)

theorem measurable_source_greedy_prefix_rank (N M r₀ : ℕ) (β d : ℝ) (z : ℂ) (s : ℕ) :
    Measurable[sourceAlternatingPrefixFiltration N M s]
      (sourceGreedyPrefixRank N M r₀ β d z s) :=
  measurable_bernoulli_prefix_function (source_alternating_prefix_rows_le N M s)
    (source_alternating_prefix_columns_le N M s) (sourceGreedyPrefixRankOnPrefix N M r₀ β d z s)

end CircularLaw
