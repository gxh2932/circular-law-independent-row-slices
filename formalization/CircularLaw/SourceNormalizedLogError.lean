import CircularLaw.TwoBranchLogSums
import CircularLaw.NormalizedSourceProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing accumulated error for the normalized source schedule

The literal finite rank sum is controlled by a square-root remaining
fraction and log(d)^8*d^(-1/8). The latter tends to zero with growing
degree. The source integer cutoff and both schedule branches are retained.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def sourceNormalizedLogErrorBound (K β ε d : ℝ) : ℝ :=
  32 * Real.sqrt ε +
    4 * sourceGraphProjectionConstant (graphGrowthConstant (K + 1)) β * (16 : ℝ) ^ 8 *
      Real.log d ^ 8 * d ^ (-1 / 8 : ℝ)

theorem sqrt_degree_negative_quarter {d : ℝ} (hd : 0 < d) :
    Real.sqrt (d ^ (-1 / 4 : ℝ)) = d ^ (-1 / 8 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le]
  norm_num

theorem log_eighth_power_times_negative_eighth_tendsto_zero :
    Tendsto (fun d : ℝ => Real.log d ^ 8 * d ^ (-1 / 8 : ℝ)) atTop (𝓝 0) := by
  have hLimit : Tendsto (fun d : ℝ => Real.log d ^ 8 / d ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (8 : ℝ) (s := 1 / 8) (by norm_num)).tendsto_div_nhds_zero
  apply hLimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
  rw [neg_div, Real.rpow_neg hd.le, div_eq_mul_inv]

theorem source_normalized_log_error_bound_tendsto_zero
    {α : Type*} {l : Filter α} {ε d : α → ℝ} (K β : ℝ)
    (hε : Tendsto ε l (𝓝 0)) (hd : Tendsto d l atTop) :
    Tendsto (fun x => sourceNormalizedLogErrorBound K β (ε x) (d x)) l (𝓝 0) := by
  have hRoot : Tendsto (fun x => Real.sqrt (ε x)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hε
  have hDegree := log_eighth_power_times_negative_eighth_tendsto_zero.comp hd
  have hLimit := (hRoot.const_mul 32).add
    (hDegree.const_mul (4 * sourceGraphProjectionConstant (graphGrowthConstant (K + 1)) β * (16 : ℝ) ^ 8))
  simp only [mul_zero, zero_add] at hLimit
  apply hLimit.congr'
  exact Eventually.of_forall (fun x => by dsimp [sourceNormalizedLogErrorBound]; ring)

theorem source_normalized_log_increment_eq_two_branch (K β N d : ℝ) (g : ℕ) :
    sourceNormalizedBernoulliLogIncrement K β N d g =
      normalizedTwoBranchLogIncrement
        (2 * sourceGraphProjectionConstant (graphGrowthConstant (K + 1)) β * Real.log d ^ 8)
        (d ^ (-1 / 4 : ℝ)) N g := by
  unfold sourceNormalizedBernoulliLogIncrement normalizedTwoBranchLogIncrement
    sourceNormalizedGraphLogIncrement sourceGraphLogIncrement sourceGraphProjectionExponent
    sourceLargeLogIncrement
  split_ifs <;> ring

theorem source_normalized_log_increment_nonneg {K β N d : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hN : 0 < N) (g : ℕ) :
    0 ≤ sourceNormalizedBernoulliLogIncrement K β N d g := by
  rw [source_normalized_log_increment_eq_two_branch]
  apply normalized_two_branch_log_increment_nonneg ?_ hN
  have hC := source_graph_projection_constant_ge_one
    (graph_growth_constant_ge_one (by linarith : 0 ≤ K + 1)) hβ hβOne
  exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)

theorem source_normalized_log_increment_range_sum_le {N L : ℕ} (hN : 0 < N) (hL : L ≤ N)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 1 ≤ d) :
    (∑ j ∈ Finset.range L, sourceNormalizedBernoulliLogIncrement K β N d (j + 1 : ℕ)) ≤
      sourceNormalizedLogErrorBound K β ((L : ℝ) / N) d := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdPos : 0 < d := zero_lt_one.trans_le hd
  have hC := source_graph_projection_constant_ge_one
    (graph_growth_constant_ge_one (by linarith : 0 ≤ K + 1)) hβ hβOne
  have hB : 0 ≤ 2 * sourceGraphProjectionConstant (graphGrowthConstant (K + 1)) β * Real.log d ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  simp_rw [source_normalized_log_increment_eq_two_branch]
  have hSum := normalized_two_branch_log_sum_le hB (Real.rpow_nonneg hdPos.le _)
    (Real.rpow_le_one_of_one_le_of_nonpos hd (by norm_num : (-1 / 4 : ℝ) ≤ 0)) hn L (by exact_mod_cast hL)
  apply hSum.trans_eq
  rw [sourceNormalizedLogErrorBound, sqrt_degree_negative_quarter hdPos]
  ring

theorem source_normalized_log_increment_rank_sum_eq {N L : ℕ} (hL : L ≤ N) (K β d : ℝ) :
    (∑ r ∈ Finset.Ico (N - L) N, sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ)) =
      ∑ j ∈ Finset.range L, sourceNormalizedBernoulliLogIncrement K β N d (j + 1 : ℕ) := by
  apply Finset.sum_bij (fun r _ => N - r - 1)
  · intro r hr
    have hRanks := Finset.mem_Ico.mp hr
    exact Finset.mem_range.mpr (by omega)
  · intro r hr s hs hEq
    have hR := Finset.mem_Ico.mp hr
    have hS := Finset.mem_Ico.mp hs
    omega
  · intro j hj
    have hJ := Finset.mem_range.mp hj
    refine ⟨N - (j + 1), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro r hr
    have hRanks := Finset.mem_Ico.mp hr
    have hRank : N - r = N - r - 1 + 1 := by omega
    exact congrArg (fun g : ℕ => sourceNormalizedBernoulliLogIncrement K β N d g) hRank

theorem source_normalized_log_increment_rank_sum_le {N L : ℕ} (hN : 0 < N) (hL : L ≤ N)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 1 ≤ d) :
    (∑ r ∈ Finset.Ico (N - L) N, sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ)) ≤
      sourceNormalizedLogErrorBound K β ((L : ℝ) / N) d := by
  rw [source_normalized_log_increment_rank_sum_eq hL]
  exact source_normalized_log_increment_range_sum_le hN hL hK hβ hβOne hd

theorem source_normalized_log_increment_rank_sum_tendsto_zero
    {α : Type*} {l : Filter α} {N L : α → ℕ} {d : α → ℝ}
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hDims : ∀ᶠ x in l, 0 < N x ∧ L x ≤ N x)
    (hFraction : Tendsto (fun x => (L x : ℝ) / N x) l (𝓝 0)) (hd : Tendsto d l atTop) :
    Tendsto (fun x => ∑ r ∈ Finset.Ico (N x - L x) (N x),
      sourceNormalizedBernoulliLogIncrement K β (N x) (d x) (N x - r : ℕ)) l (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (source_normalized_log_error_bound_tendsto_zero K β hFraction hd)
  · filter_upwards [hDims] with x hx
    apply Finset.sum_nonneg
    intro r _
    exact source_normalized_log_increment_nonneg hK hβ hβOne (by exact_mod_cast hx.1) _
  · filter_upwards [hDims, hd.eventually_ge_atTop 1] with x hx hxD
    exact source_normalized_log_increment_rank_sum_le hx.1 hx.2 hK hβ hβOne hxD

end CircularLaw
