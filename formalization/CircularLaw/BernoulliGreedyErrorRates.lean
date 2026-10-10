import CircularLaw.BernoulliGreedyPaperPrefix
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Fixed-fraction limits for the actual greedy errors

At a fixed source cutoff epsilon the projection failure tends to a constant
times epsilon. Both its eighth-root completion error and the deterministic
square-root log error vanish when epsilon decreases to zero.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def bernoulliGreedyLogError (ε : ℝ) : ℝ := 32 * Real.sqrt (2 * ε)

def bernoulliGreedyFailureBound (ε : ℝ) : ℝ :=
  16 * (bernoulliLargeProjectionConstant * (2 * ε)) ^ (1 / 8 : ℝ)

def bernoulliGreedyMaximumFraction : ℝ := min (1 / 8) (Real.exp (-4) / 2)

theorem bernoulli_greedy_maximum_fraction_pos : 0 < bernoulliGreedyMaximumFraction := by
  unfold bernoulliGreedyMaximumFraction
  exact lt_min (by norm_num) (by positivity)

theorem bernoulli_greedy_log_error_tendsto_zero :
    Tendsto bernoulliGreedyLogError (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0)).const_mul 2)).const_mul 32
  simp only [mul_zero, Real.sqrt_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem bernoulli_greedy_failure_bound_tendsto_zero :
    Tendsto bernoulliGreedyFailureBound (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hBase := ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0)).const_mul 2).const_mul
    bernoulliLargeProjectionConstant
  simp only [mul_zero] at hBase
  have hPower := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 8)).continuousAt.tendsto.comp hBase
  simp only [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)] at hPower
  simpa only [bernoulliGreedyFailureBound, mul_zero] using
    (hPower.const_mul 16).mono_left nhdsWithin_le_nhds

theorem normalized_source_projection_failure_bound_fixed_fraction_tendsto
    {α : Type*} {l : Filter α} {d : α → ℝ} (ε : ℝ) (hd : Tendsto d l atTop) :
    Tendsto (fun x => normalizedSourceProjectionFailureBound ε (d x)) l
      (𝓝 (bernoulliLargeProjectionConstant * ε)) := by
  have hPower : Tendsto (fun x => d x ^ (-1 / 4 : ℝ)) l (𝓝 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hd
  have hRoot : Tendsto (fun x => Real.sqrt (Real.log (Real.log (d x)))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hd))
  have hTail : Tendsto (fun x =>
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log (d x)))) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRoot
  simpa only [normalizedSourceProjectionFailureBound, mul_zero, add_zero] using
    (((tendsto_const_nhds : Tendsto (fun _ : α => ε) l (𝓝 ε)).add
      (hPower.const_mul 3)).const_mul bernoulliLargeProjectionConstant).add hTail

theorem bernoulli_greedy_completion_error_fixed_fraction_tendsto
    {α : Type*} {l : Filter α} {d : α → ℝ} (ε : ℝ) (hd : Tendsto d l atTop) :
    Tendsto (fun x => 16 * normalizedSourceProjectionFailureBound (2 * ε) (d x) ^ (1 / 8 : ℝ)) l
      (𝓝 (bernoulliGreedyFailureBound ε)) := by
  exact (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 8)).continuousAt.tendsto.comp
    (normalized_source_projection_failure_bound_fixed_fraction_tendsto (2 * ε) hd)).const_mul 16)

theorem source_normalized_log_error_bound_mono_fraction (K β d : ℝ) {ε η : ℝ} (h : ε ≤ η) :
    sourceNormalizedLogErrorBound K β ε d ≤ sourceNormalizedLogErrorBound K β η d := by
  unfold sourceNormalizedLogErrorBound
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h)
    (by norm_num : (0 : ℝ) ≤ 32)) (le_refl _)

theorem source_normalized_log_error_bound_fixed_fraction_tendsto
    {α : Type*} {l : Filter α} {d : α → ℝ} (K β ε : ℝ) (hd : Tendsto d l atTop) :
    Tendsto (fun x => sourceNormalizedLogErrorBound K β (2 * ε) (d x)) l
      (𝓝 (bernoulliGreedyLogError ε)) := by
  have hTail := (log_eighth_power_times_negative_eighth_tendsto_zero.comp hd).const_mul
    (4 * sourceGraphProjectionConstant (graphGrowthConstant (K + 1)) β * (16 : ℝ) ^ 8)
  simp only [mul_zero] at hTail
  have hLimit := (tendsto_const_nhds : Tendsto (fun _ : α => bernoulliGreedyLogError ε) l
    (𝓝 (bernoulliGreedyLogError ε))).add hTail
  simp only [add_zero] at hLimit
  apply hLimit.congr
  intro x
  dsimp [sourceNormalizedLogErrorBound, bernoulliGreedyLogError]
  ring

end CircularLaw
