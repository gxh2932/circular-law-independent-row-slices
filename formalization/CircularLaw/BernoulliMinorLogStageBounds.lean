import CircularLaw.MinorLogarithmicStages
import CircularLaw.MinorLogPrefixDeviation

/-!
# Actual fixed-stage probability bounds for the minor logarithmic prefix

Weak convergence supplies both clipped-mean events, the retained-value
bound supplies the small-value event, and the uniform second moment
supplies the upper-tail event. Exact floor and normalization errors are
enforced alongside them. All statements use the actual ambient law.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def minorLogStageArray (d : ℕ → ℕ) (z : ℂ) (K k : ℕ) :
    ∀ n, BernoulliSquareSample n → Fin (bernoulliSqueezeMinorDimension n (logarithmicStageFraction 48 K k)) → ℝ≥0 :=
  bernoulliMinorSingularArray d z (logarithmicStageFraction 48 K k)
    (logarithmicStageFraction_pos (by norm_num : (0 : ℝ) < 48) K k).le

def MinorLogStageReady (d : ℕ → ℕ) (z : ℂ) (K k n : ℕ) : Prop :=
  0 < bernoulliSqueezeMinorDimension n (logarithmicStageFraction 48 K k) ∧
  (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) /
      (bernoulliSqueezeMinorDimension n (logarithmicStageFraction 48 K k) : ℝ) ≤ diagonalAccuracy k ∧
  |(bernoulliSqueezeMinorDimension n (logarithmicStageFraction 48 K k) : ℝ) / n -
      (1 - logarithmicStageFraction 48 K k)| *
      |-(∫ t : ℝ≥0, Real.log (t : ℝ)
        ∂gaussianMinorSingularLimit (1 - logarithmicStageFraction 48 K k) z)| ≤ diagonalAccuracy k ∧
  (sparseBernoulliMatrixLaw n (d n)).real {x | empiricalPrefixHasSmall (minorLogStageArray d z K k n x)
    (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K k))
    (Real.exp (-minorLogStageNegativeCutoff K k))} < diagonalAccuracy k ∧
  (sparseBernoulliMatrixLaw n (d n)).real {x | diagonalAccuracy k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (clippedNegativeLog (minorLogStageNegativeCutoff K k)) -
      ∫ t, clippedNegativeLog (minorLogStageNegativeCutoff K k) t
        ∂gaussianMinorSingularLimit (1 - logarithmicStageFraction 48 K k) z|} < diagonalAccuracy k ∧
  (sparseBernoulliMatrixLaw n (d n)).real {x | diagonalAccuracy k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (clippedPositiveLog (minorLogStagePositiveCutoff k)) -
      ∫ t, clippedPositiveLog (minorLogStagePositiveCutoff k) t
        ∂gaussianMinorSingularLimit (1 - logarithmicStageFraction 48 K k) z|} < diagonalAccuracy k ∧
  (sparseBernoulliMatrixLaw n (d n)).real {x | minorLogStageMomentBudget z k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (fun t => (t : ℝ) ^ 2)|} < diagonalAccuracy k

theorem bernoulli_minor_log_stage_ready_eventually (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (K k : ℕ)
    (hHalf : logarithmicStageFraction 48 K k ≤ 1 / 2) :
    ∀ᶠ n in atTop, MinorLogStageReady d z K k n := by
  let epsilon := logarithmicStageFraction 48 K k
  have hPos : 0 < epsilon := logarithmicStageFraction_pos (by norm_num) K k
  have hOne : epsilon < 1 := by dsimp [epsilon]; linarith
  have hQ := minor_dimension_tendsto_of_positive_ratio
    (fun n => bernoulliSqueezeMinorDimension n epsilon) (by linarith : 0 < 1 - epsilon)
    (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne)
  have hRatio := bernoulli_squeeze_fixed_minor_ratio_tendsto hOne
  have hRound : Tendsto (fun n => (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) /
      (bernoulliSqueezeMinorDimension n epsilon : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hQ
  have hNormalize : Tendsto (fun n =>
      |(bernoulliSqueezeMinorDimension n epsilon : ℝ) / n - (1 - epsilon)| *
        |-(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (1 - epsilon) z)|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using ((hRatio.sub_const (1 - epsilon)).abs).mul_const _
  have hWeak := bernoulli_fixed_fraction_minor_ambient_weak_convergence d hDegree hSparse hPos.le hOne z
  have hTn : 0 ≤ minorLogStageNegativeCutoff K k := by dsimp [minorLogStageNegativeCutoff]; positivity
  have hTp : 0 ≤ minorLogStagePositiveCutoff k := by dsimp [minorLogStagePositiveCutoff]; positivity
  have hNegative := hWeak (clippedNegativeLog (minorLogStageNegativeCutoff K k))
    (continuous_clippedNegativeLog _) ⟨minorLogStageNegativeCutoff K k, fun t => by
      rw [abs_of_nonneg (clippedNegativeLog_bounds hTn t).1]
      exact (clippedNegativeLog_bounds hTn t).2⟩ (diagonalAccuracy k) (diagonalAccuracy_pos k)
  have hPositive := hWeak (clippedPositiveLog (minorLogStagePositiveCutoff k))
    (continuous_clippedPositiveLog _) ⟨minorLogStagePositiveCutoff k, fun t => by
      rw [abs_of_nonneg (clippedPositiveLog_bounds hTp t).1]
      exact (clippedPositiveLog_bounds hTp t).2⟩ (diagonalAccuracy k) (diagonalAccuracy_pos k)
  have hSmall := bernoulli_minor_stage_small_probability_tendsto d z hDegree hSparse K k hHalf
  filter_upwards [hQ.eventually_gt_atTop 0,
    hRound.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
    hNormalize.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
    hSmall.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
    hNegative.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
    hPositive.eventually (gt_mem_nhds (diagonalAccuracy_pos k)),
    eventually_valid_bernoulli_degrees hDegree hSparse] with n hm hr hn hs hneg hpos hd
  refine ⟨hm, hr.le, hn.le, hs, hneg, hpos, ?_⟩
  apply (bernoulli_principal_minor_second_moment_tail_bound
    (bernoulli_squeeze_lengths_le hPos.le).2 hm hd.1 hd.2 z
    (by dsimp [minorLogStageMomentBudget]; positivity)).trans_lt
  exact minor_log_stage_moment_tail_ratio z k

theorem bernoulli_minor_log_stage_deviation_probability_bound (d : ℕ → ℕ) (z : ℂ)
    (K k n : ℕ) (hHalf : logarithmicStageFraction 48 K k ≤ 1 / 2)
    (hSupport : Real.log (128 + ‖z‖) ≤ minorLogStagePositiveCutoff k)
    (hReady : MinorLogStageReady d z K k n) :
    (sparseBernoulliMatrixLaw n (d n)).real {x |
      minorLogStageTolerance K z k < |bernoulliMinorLogPrefixAt d z (logarithmicStageFraction 48 K k)
        (logarithmicStageFraction_pos (by norm_num : (0 : ℝ) < 48) K k).le n x - minorLogStageLimit K z k|} ≤
      4 * diagonalAccuracy k := by
  let epsilon := logarithmicStageFraction 48 K k
  have hNonneg : 0 ≤ epsilon := (logarithmicStageFraction_pos (by norm_num) K k).le
  let A := -(∫ t : ℝ≥0, Real.log (t : ℝ) ∂gaussianMinorSingularLimit (1 - epsilon) z)
  let B₁ := {x : BernoulliSquareSample n | empiricalPrefixHasSmall (minorLogStageArray d z K k n x)
    (bernoulliSqueezePrefixLength n epsilon) (Real.exp (-minorLogStageNegativeCutoff K k))}
  let B₂ := {x : BernoulliSquareSample n | diagonalAccuracy k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (clippedNegativeLog (minorLogStageNegativeCutoff K k)) -
      ∫ t, clippedNegativeLog (minorLogStageNegativeCutoff K k) t ∂gaussianMinorSingularLimit (1 - epsilon) z|}
  let B₃ := {x : BernoulliSquareSample n | diagonalAccuracy k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (clippedPositiveLog (minorLogStagePositiveCutoff k)) -
      ∫ t, clippedPositiveLog (minorLogStagePositiveCutoff k) t ∂gaussianMinorSingularLimit (1 - epsilon) z|}
  let B₄ := {x : BernoulliSquareSample n | minorLogStageMomentBudget z k <
    |empiricalNonnegativeMean (minorLogStageArray d z K k n x) (fun t => (t : ℝ) ^ 2)|}
  rcases hReady with ⟨hm, hRound, hNormalize, hSmall, hNegative, hPositive, hMoment⟩
  have hSubset : {x | minorLogStageTolerance K z k <
      |bernoulliMinorLogPrefixAt d z epsilon hNonneg n x - minorLogStageLimit K z k|} ⊆
      B₁ ∪ (B₂ ∪ (B₃ ∪ B₄)) := by
    intro x hx
    by_contra h
    have hNot := not_or.mp h
    have hNot₂ := not_or.mp hNot.2
    have hNot₃ := not_or.mp hNot₂.2
    have hN : |empiricalNonnegativeMean (minorLogStageArray d z K k n x)
        (clippedNegativeLog (minorLogStageNegativeCutoff K k)) - ∫ t,
          clippedNegativeLog (minorLogStageNegativeCutoff K k) t ∂gaussianMinorSingularLimit (1 - epsilon) z| ≤
        diagonalAccuracy k := le_of_not_gt hNot₂.1
    have hP : |empiricalNonnegativeMean (minorLogStageArray d z K k n x)
        (clippedPositiveLog (minorLogStagePositiveCutoff k)) - ∫ t,
          clippedPositiveLog (minorLogStagePositiveCutoff k) t ∂gaussianMinorSingularLimit (1 - epsilon) z| ≤
        diagonalAccuracy k := le_of_not_gt hNot₃.1
    have hM : empiricalNonnegativeMean (minorLogStageArray d z K k n x) (fun t => (t : ℝ) ^ 2) ≤
        minorLogStageMomentBudget z k := (le_abs_self _).trans (le_of_not_gt hNot₃.2)
    have hBound := bernoulli_minor_prefix_good_event_log_bound d z hNonneg hHalf n x
      (by dsimp [minorLogStageNegativeCutoff]; positivity)
      (by dsimp [minorLogStagePositiveCutoff]; positivity) hSupport hNot.1 hM hN hP
    have hRemoved := bernoulli_squeeze_minor_removed_fraction_upper hNonneg hm
    have hProduct := mul_le_mul_of_nonneg_right hRemoved
      (show 0 ≤ minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k by
        dsimp [minorLogStageNegativeCutoff, minorLogStagePositiveCutoff]; positivity)
    have hRoundEq : (epsilon / 4 + 1 / (bernoulliSqueezeMinorDimension n epsilon : ℝ)) *
        (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) =
        epsilon / 4 * (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) +
          (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) /
            (bernoulliSqueezeMinorDimension n epsilon : ℝ) := by ring
    rw [hRoundEq] at hProduct
    have hTriangle := abs_sub_le (bernoulliMinorLogPrefixAt d z epsilon hNonneg n x)
      (((bernoulliSqueezeMinorDimension n epsilon : ℝ) / n) * A) ((1 - epsilon) * A)
    have hNormEq : |((bernoulliSqueezeMinorDimension n epsilon : ℝ) / n) * A - (1 - epsilon) * A| =
        |(bernoulliSqueezeMinorDimension n epsilon : ℝ) / n - (1 - epsilon)| * |A| := by
      rw [← sub_mul, abs_mul]
    rw [hNormEq] at hTriangle
    change minorLogStageTolerance K z k < |bernoulliMinorLogPrefixAt d z epsilon hNonneg n x -
      (1 - epsilon) * A| at hx
    dsimp [minorLogStageTolerance] at hx
    dsimp only [epsilon, A] at hTriangle hProduct
    linarith
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n (d n)) hSubset).trans
  have h₁ := measureReal_union_le (μ := sparseBernoulliMatrixLaw n (d n)) B₁ (B₂ ∪ (B₃ ∪ B₄))
  have h₂ := measureReal_union_le (μ := sparseBernoulliMatrixLaw n (d n)) B₂ (B₃ ∪ B₄)
  have h₃ := measureReal_union_le (μ := sparseBernoulliMatrixLaw n (d n)) B₃ B₄
  linarith

end CircularLaw
