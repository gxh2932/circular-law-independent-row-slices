import CircularLaw.BernoulliGreedyErrorRates
import CircularLaw.BernoulliGreedyAsymptoticParameters
import CircularLaw.BernoulliMinorUpperProbabilityReduction

/-!
# The actual fixed-fraction Bernoulli full-to-minor upper estimate

All finite process hypotheses are discharged eventually. The retained-zero
and simultaneous graph errors vanish with dimension; the completion error
has an explicit fraction-dependent limit. This supplies the remaining
probability input to the common slow-cutoff logarithmic squeeze.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology NNReal

namespace CircularLaw

theorem bernoulli_greedy_minor_upper_probability_eventually
    (d : ℕ → ℕ) (z : ℂ) (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (hz : z ≠ 0) {ε : ℝ} (hε : 0 < ε) (hSmall : ε ≤ bernoulliGreedyMaximumFraction)
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    ∀ᶠ n in atTop, (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefixAt d z ε hε.le n x + bernoulliGreedyLogError ε + δ <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} ≤
        bernoulliGreedyFailureBound ε + γ := by
  let β : ℝ := min 1 ‖z‖
  have hβ : 0 < β := bernoulli_greedy_shift_beta_pos hz
  have hβOne : β ≤ 1 := min_le_left _ _
  have hEighth : ε ≤ 1 / 8 := hSmall.trans (min_le_left _ _)
  have hTiny : 2 * ε ≤ Real.exp (-4) := by
    have h := hSmall.trans (min_le_right _ _)
    linarith
  have hOne : ε < 1 := by linarith
  have hParameters := sparse_bernoulli_greedy_probability_parameters_eventually d hDegree hSparse
  have hDReal : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hDUpper : ∀ᶠ n in atTop, (d n : ℝ) ≤ n := by
    filter_upwards [hParameters] with n hn
    exact_mod_cast hn.2.2.1
  have hZero := bernoulli_minor_retained_zero_probability_tendsto d z hDegree hSparse hε hOne
  have hGraph := source_exposure_graph_failure_error_tendsto (fun n => (d n : ℝ)) hDReal hDUpper
  have hDrift := bernoulli_greedy_completion_error_fixed_fraction_tendsto ε hDReal
  have hProbability : Tendsto (fun n =>
      2 * (sparseBernoulliMatrixLaw n (d n)).real
        {x | empiricalPrefixHasZero (bernoulliMinorSingularArray d z ε hε.le n x)
          (bernoulliSqueezePrefixLength n ε)} +
      sourceExposureGraphFailureError n (d n) +
      16 * normalizedSourceProjectionFailureBound (2 * ε) (d n) ^ (1 / 8 : ℝ))
      atTop (𝓝 (bernoulliGreedyFailureBound ε)) := by
    simpa only [mul_zero, zero_add] using ((hZero.const_mul 2).add hGraph).add hDrift
  have hLog := source_normalized_log_error_bound_fixed_fraction_tendsto 8 β ε hDReal
  filter_upwards [hParameters, bernoulli_greedy_shift_range_eventually d z hDegree,
    bernoulli_rounded_greedy_cutoff_eventually hε hEighth,
    hLog.eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ)),
    hProbability.eventually (gt_mem_nhds (lt_add_of_pos_right _ hγ))]
      with n hn hShift hCutoff hLogSmall hProbabilitySmall
  rcases hn with ⟨hn, hdPos, hdN, hpPos, hpHalf, hDegreeEq, hdLarge⟩
  have hLengths := bernoulli_squeeze_lengths_le (n := n) hε.le
  have hBound := bernoulli_normalized_minor_prefix_upper_probability hn hLengths.2 hLengths.1
    hCutoff.1 hCutoff.2.1 (rowBernoulliParameter n (d n)) (rowBernoulliParameter_le_one hn hdN)
    hpPos hpHalf z hβ hβOne hdLarge hDegreeEq hCutoff.2.2 hTiny hShift.1 hShift.2
  rw [← sparseBernoulliMatrixLaw_eq hn hdN] at hBound
  have hError := source_normalized_log_error_bound_mono_fraction 8 β (d n) hCutoff.2.2
  have hSubset :
      {x | empiricalHasZero (bernoulliSingularArray d z n x) ∨
        bernoulliMinorLogPrefixAt d z ε hε.le n x + bernoulliGreedyLogError ε + δ <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} ⊆
      {x | empiricalHasZero (squareSingularValuesNNReal (normalizedShiftedBernoulliMatrix (d n) z x)) ∨
        squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x) hLengths.2
          (bernoulliSqueezePrefixLength n ε) +
        sourceNormalizedLogErrorBound 8 β ((n - bernoulliSqueezePrefixLength n ε : ℕ) / (n : ℝ)) (d n) <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x)} := by
    intro x hx
    rcases hx with hZero | hExcess
    · exact Or.inl hZero
    · apply Or.inr
      change squareMinorNegativeLogPrefix (normalizedShiftedBernoulliMatrix (d n) z x) hLengths.2
        (bernoulliSqueezePrefixLength n ε) + bernoulliGreedyLogError ε + δ <
          squareNegativeLogMean (normalizedShiftedBernoulliMatrix (d n) z x) at hExcess
      linarith
  exact ((measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) hSubset).trans hBound).trans
    hProbabilitySmall.le

theorem bernoulli_shifted_full_log_convergence (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (hz : z ≠ 0) :
    EmpiricalLogConvergenceInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliSingularArray d z) (gaussianShiftedSingularLimit z) := by
  apply bernoulli_full_log_convergence_of_minor_upper_probability_bound d z hDegree hSparse
    bernoulliGreedyLogError bernoulliGreedyFailureBound bernoulli_greedy_maximum_fraction_pos
    bernoulli_greedy_log_error_tendsto_zero bernoulli_greedy_failure_bound_tendsto_zero
  intro ε hε hSmall δ γ hδ hγ
  exact bernoulli_greedy_minor_upper_probability_eventually d z hDegree hSparse hz hε hSmall hδ hγ

end CircularLaw
