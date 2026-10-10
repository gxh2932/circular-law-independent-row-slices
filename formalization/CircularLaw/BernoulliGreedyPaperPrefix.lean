import CircularLaw.GreedyPrefixPaperNormalization
import CircularLaw.BernoulliGreedyCutoff
import CircularLaw.BernoulliPrincipalMinorSmallValues
import CircularLaw.BernoulliLogSqueeze

/-!
# The finite greedy estimate for the actual manuscript full and minor logs

The terminal failure is exactly full singularity or excessive normalized
full logarithm relative to the literal retained minor prefix. The initial
positive-product failure is the actual retained-zero event; its checked
minor weak law proves vanishing probability at every fixed positive cutoff.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology NNReal

namespace CircularLaw

theorem source_greedy_terminal_bad_eq_paper_event {N M r : ℕ}
    (hM : M ≤ N) (hr : r ≤ M) {d : ℕ} (hd : 0 < d) (β : ℝ) (z : ℂ) :
    sourceGreedyTerminalPrefixBadEvent N M r β d (sourceRawBernoulliShift d z) =
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix d z x)) ∨
        squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix d z x) hM r +
          sourceNormalizedLogErrorBound 8 β ((N - r : ℕ) / (N : ℝ)) d <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix d z x)} := by
  ext x
  change (_ = 0 ∨ _) ↔ (_ ∨ _)
  rw [source_terminal_normalized_retained_product hM hd,
    leading_row_square_full_product_zero_iff,
    source_initial_normalized_retained_log hM hr hd,
    source_terminal_normalized_retained_log hM hd]

theorem bernoulli_greedy_initial_product_failure_tendsto
    (d : ℕ → ℕ) (z : ℂ) (β : ℝ) (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {ε : ℝ} (hε : 0 < ε) (hOne : ε < 1) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      (sourceGreedyInitialPositiveEvent n (bernoulliSqueezeMinorDimension n ε)
        (bernoulliSqueezePrefixLength n ε) β (d n) (sourceRawBernoulliShift (d n) z))ᶜ)
        atTop (𝓝 0) := by
  apply (bernoulli_minor_retained_zero_probability_tendsto d z hDegree hSparse hε hOne).congr'
  filter_upwards [hDegree.eventually_ge_atTop 1] with n hn
  rw [source_initial_positive_complement_eq_minor_zero
    (bernoulli_squeeze_lengths_le (n := n) hε.le).2
    (bernoulli_squeeze_lengths_le (n := n) hε.le).1 (by omega)]
  rfl

theorem bernoulli_normalized_minor_prefix_upper_probability {N M r d : ℕ}
    (hN : 0 < N) (hM : M ≤ N) (hr : r ≤ M)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (hInitial : 2 * (M - r) ≤ N - M)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {β ε : ℝ} (z : ℂ) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 1024 ≤ (d : ℝ)) (hDegree : (d : ℝ) = (N : ℝ) * p)
    (hFraction : ((N - r : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖sourceRawBernoulliShift d z‖) (hzUpper : ‖sourceRawBernoulliShift d z‖ ≤ d) :
    (bernoulliSquareMatrixLaw N p hp).real
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix d z x)) ∨
        squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix d z x) hM r +
          sourceNormalizedLogErrorBound 8 β ((N - r : ℕ) / (N : ℝ)) d <
            squareNegativeLogMean (normalizedShiftedBernoulliMatrix d z x)} ≤
      2 * (bernoulliSquareMatrixLaw N p hp).real
        {x | empiricalPrefixHasZero
          (squareSingularValuesNNReal (squarePrincipalMinor (normalizedShiftedBernoulliMatrix d z x) hM)) r} +
      sourceExposureGraphFailureError N d + 16 * normalizedSourceProjectionFailureBound ε d ^ (1 / 8 : ℝ) := by
  have hdPos : 0 < d := by
    have hReal : (0 : ℝ) < d := (Real.exp_pos 1024).trans_le hd
    exact_mod_cast hReal
  have hBound := bernoulli_greedy_terminal_prefix_upper_probability hN hM hr hRows hInitial
    p hp hpPos hHalf hβ hβOne hd hDegree hFraction hε hz hzUpper
  rw [source_greedy_terminal_bad_eq_paper_event hM hr hdPos,
    source_initial_positive_complement_eq_minor_zero hM hr hdPos] at hBound
  exact hBound

end CircularLaw
