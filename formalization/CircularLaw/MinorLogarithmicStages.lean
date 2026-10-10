import CircularLaw.BernoulliPrincipalMinorSecondMoment
import CircularLaw.GaussianMinorUniformLogBounds
import CircularLaw.LogarithmicStages

/-!
# Explicit common stages for the minor logarithmic prefix

The existing exponentially decreasing fraction is retained. Twice the
negative cutoff lies below the proved retained-value threshold. A cubic
positive cutoff and a linear moment budget give vanishing tail errors.
The minor's ambient-normalized limiting value tends to the full circular
potential. These are deterministic and fixed-stage probability inputs.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

def minorLogStageNegativeCutoff (K k : ℕ) : ℝ := 2 * logarithmicStageCutoff K k

def minorLogStagePositiveCutoff (k : ℕ) : ℝ := (k + 1 : ℝ) ^ 3

def minorLogStageMomentBudget (z : ℂ) (k : ℕ) : ℝ :=
  (2 + 2 * ‖z‖ ^ 2) * (k + 1 : ℝ) + 1

def minorLogStageLimit (K : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  (1 - logarithmicStageFraction 48 K k) *
    (-(∫ t : ℝ≥0, Real.log (t : ℝ)
      ∂gaussianMinorSingularLimit (1 - logarithmicStageFraction 48 K k) z))

def minorLogStageTolerance (K : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  logarithmicStageFraction 48 K k / 4 *
      (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k) +
    2 * minorLogStageMomentBudget z k / minorLogStagePositiveCutoff k +
    4 * diagonalAccuracy k + 192 * Real.exp (-minorLogStageNegativeCutoff K k / 2)

theorem logarithmic_stage_fraction_mul_successor_power_tendsto (C : ℝ) (K p : ℕ) :
    Tendsto (fun k => logarithmicStageFraction C K k * (k + 1 : ℝ) ^ p) atTop (𝓝 0) := by
  have hReal : Tendsto (fun k : ℕ => (k + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp hReal).const_mul
    (4 * C * Real.exp (1 - K))
  simp only [mul_zero, Function.comp_apply] at h
  have hEq (k : ℕ) : logarithmicStageFraction C K k * (k + 1 : ℝ) ^ p =
      (4 * C * Real.exp (1 - K)) * ((k + 1 : ℝ) ^ p * Real.exp (-(k + 1 : ℝ))) := by
    unfold logarithmicStageFraction logarithmicStageCutoff
    rw [Nat.cast_add]
    have hExp : Real.exp (1 - (K : ℝ)) * Real.exp (-(k + 1 : ℝ)) =
        Real.exp (-((k : ℝ) + K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show (4 * C * Real.exp (1 - (K : ℝ))) *
        ((k + 1 : ℝ) ^ p * Real.exp (-(k + 1 : ℝ))) =
        (4 * C) * (Real.exp (1 - (K : ℝ)) * Real.exp (-(k + 1 : ℝ))) * (k + 1 : ℝ) ^ p by ring,
      hExp]
  apply h.congr'
  exact Eventually.of_forall (fun k => (hEq k).symm)

theorem minor_log_stage_negative_threshold (K k : ℕ)
    (hHalf : logarithmicStageFraction 48 K k ≤ 1 / 2) :
    Real.exp (-minorLogStageNegativeCutoff K k) ≤ logarithmicStageFraction 48 K k / 1536 := by
  let a := Real.exp (-(logarithmicStageCutoff K k : ℝ))
  have hEq : logarithmicStageFraction 48 K k = 192 * a := by dsimp [logarithmicStageFraction, a]; norm_num
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have haSmall : a ≤ 1 / 8 := by rw [hEq] at hHalf; linarith
  have hExp : Real.exp (-minorLogStageNegativeCutoff K k) = a * a := by
    dsimp [minorLogStageNegativeCutoff, a]
    rw [show -(2 * (logarithmicStageCutoff K k : ℝ)) =
      -(logarithmicStageCutoff K k : ℝ) + -(logarithmicStageCutoff K k : ℝ) by ring, Real.exp_add]
  rw [hExp, hEq]
  have hProduct := mul_nonneg ha (sub_nonneg.mpr haSmall)
  nlinarith

theorem bernoulli_minor_stage_small_probability_tendsto (d : ℕ → ℕ) (z : ℂ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (K k : ℕ)
    (hHalf : logarithmicStageFraction 48 K k ≤ 1 / 2) :
    Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalPrefixHasSmall
        (bernoulliMinorSingularArray d z (logarithmicStageFraction 48 K k)
          (logarithmicStageFraction_pos (by norm_num : (0 : ℝ) < 48) K k).le n x)
        (bernoulliSqueezePrefixLength n (logarithmicStageFraction 48 K k))
        (Real.exp (-minorLogStageNegativeCutoff K k))}) atTop (𝓝 0) := by
  let epsilon := logarithmicStageFraction 48 K k
  have hPos : 0 < epsilon := logarithmicStageFraction_pos (by norm_num) K k
  have hOne : epsilon < 1 := by dsimp [epsilon]; linarith
  have hQ := minor_dimension_tendsto_of_positive_ratio
    (fun n => bernoulliSqueezeMinorDimension n epsilon) (by linarith : 0 < 1 - epsilon)
    (bernoulli_squeeze_fixed_minor_ratio_tendsto hOne)
  have hSmall : Tendsto (fun n => (sparseBernoulliMatrixLaw n (d n)).real
      {x | empiricalPrefixHasSmall (bernoulliMinorSingularArray d z epsilon hPos.le n x)
        (bernoulliSqueezePrefixLength n epsilon) (epsilon / 1536)}) atTop (𝓝 0) := by
    have h := indexed_empirical_prefix_lower_bound_of_linear_mass
      (fun n => sparseBernoulliMatrixLaw n (d n))
      (bernoulliMinorSingularArray d z epsilon hPos.le)
      (gaussianMinorSingularLimit (1 - epsilon) z) (fun n => bernoulliSqueezePrefixLength n epsilon)
      (bernoulli_fixed_fraction_minor_ambient_weak_convergence d hDegree hSparse hPos.le hOne z)
      (bernoulliMinorSingularArray_antitone d z epsilon hPos.le)
      (by norm_num : (0 : ℝ) < 96) (by positivity : 0 < epsilon / 4)
      (fun _ ht => gaussian_minor_limit_uniform_small_mass (by dsimp [epsilon]; linarith) z ht)
      ((hQ.eventually_gt_atTop 0).mono (fun _ hn =>
        bernoulli_squeeze_minor_removed_fraction_lower hPos.le hOne.le hn))
    have hThreshold : (epsilon / 4) / (4 * (96 : ℝ)) = epsilon / 1536 := by ring
    simpa only [hThreshold] using h
  apply varying_probability_event_of_subset (fun n => sparseBernoulliMatrixLaw n (d n)) ?_ hSmall
  intro n x hx
  obtain ⟨j, hj, hs⟩ := hx
  exact ⟨j, hj, hs.trans_le (minor_log_stage_negative_threshold K k hHalf)⟩

theorem bernoulli_squeeze_minor_removed_fraction_upper {n : ℕ} {epsilon : ℝ}
    (hNonneg : 0 ≤ epsilon) (hMinor : 0 < bernoulliSqueezeMinorDimension n epsilon) :
    (bernoulliSqueezeMinorDimension n epsilon - bernoulliSqueezePrefixLength n epsilon : ℕ) /
      (bernoulliSqueezeMinorDimension n epsilon : ℝ) ≤ epsilon / 4 +
        1 / (bernoulliSqueezeMinorDimension n epsilon : ℝ) := by
  have hLengths := bernoulli_squeeze_lengths_le (n := n) hNonneg
  have hFloor := Nat.lt_floor_add_one
    ((1 - epsilon / 4) * bernoulliSqueezeMinorDimension n epsilon)
  change (1 - epsilon / 4) * (bernoulliSqueezeMinorDimension n epsilon : ℝ) <
    (bernoulliSqueezePrefixLength n epsilon : ℝ) + 1 at hFloor
  rw [Nat.cast_sub hLengths.1]
  have hmR : (0 : ℝ) < bernoulliSqueezeMinorDimension n epsilon := by exact_mod_cast hMinor
  apply (div_le_iff₀ hmR).mpr
  have hCancel := div_mul_cancel₀ (1 : ℝ) hmR.ne'
  nlinarith

theorem minor_log_stage_moment_tail_ratio (z : ℂ) (k : ℕ) :
    (2 + 2 * ‖z‖ ^ 2) / minorLogStageMomentBudget z k < diagonalAccuracy k := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hBudget : 0 < minorLogStageMomentBudget z k := by dsimp [minorLogStageMomentBudget]; positivity
  apply (div_lt_iff₀ hBudget).mpr
  have hAccuracy : diagonalAccuracy k = 1 / (k + 1 : ℝ) := by simp only [diagonalAccuracy, Nat.cast_add, Nat.cast_one]
  rw [hAccuracy]
  dsimp [minorLogStageMomentBudget]
  have hCancel : (1 / (k + 1 : ℝ)) * (k + 1 : ℝ) = 1 := by field_simp
  have hProduct := congrArg (fun t : ℝ => (2 + 2 * ‖z‖ ^ 2) * t) hCancel
  nlinarith [one_div_pos.mpr hk]

theorem minor_log_stage_limit_tendsto (K : ℕ) (z : ℂ) :
    Tendsto (minorLogStageLimit K z) atTop (𝓝 (circularPaperPotential z)) := by
  have hTheta : Tendsto (fun k => 1 - logarithmicStageFraction 48 K k) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (logarithmicStageFraction_tendsto 48 K)
  have hPositive : ∀ᶠ k in atTop, 0 < 1 - logarithmicStageFraction 48 K k := by
    filter_upwards [(logarithmicStageFraction_tendsto 48 K).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with k hk
    linarith
  simpa only [minorLogStageLimit, one_mul] using hTheta.mul
    (gaussian_minor_limit_negative_log_tendsto _ z hPositive hTheta)

theorem minor_log_stage_positive_cutoff_tendsto :
    Tendsto minorLogStagePositiveCutoff atTop atTop := by
  have hReal : Tendsto (fun k : ℕ => (k + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact (tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hReal

theorem minor_log_stage_tolerance_tendsto (K : ℕ) (z : ℂ) :
    Tendsto (minorLogStageTolerance K z) atTop (𝓝 0) := by
  have hInv : Tendsto (fun k : ℕ => (k + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hMoment : Tendsto (fun k => 2 * minorLogStageMomentBudget z k / minorLogStagePositiveCutoff k)
      atTop (𝓝 0) := by
    have h := ((hInv.pow 2).const_mul (2 * (2 + 2 * ‖z‖ ^ 2))).add ((hInv.pow 3).const_mul 2)
    simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero] at h
    apply h.congr'
    refine Eventually.of_forall (fun k => ?_)
    dsimp [minorLogStageMomentBudget, minorLogStagePositiveCutoff]
    field_simp
  have hRound : Tendsto (fun k => logarithmicStageFraction 48 K k / 4 *
      (minorLogStageNegativeCutoff K k + minorLogStagePositiveCutoff k)) atTop (𝓝 0) := by
    have hNeg := (logarithmicStageFraction_mul_cutoff_tendsto 48 K).const_mul (1 / 2 : ℝ)
    have hPos := (logarithmic_stage_fraction_mul_successor_power_tendsto 48 K 3).div_const 4
    have h := hNeg.add hPos
    simp only [mul_zero, zero_div, add_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun k => by dsimp [minorLogStageNegativeCutoff, minorLogStagePositiveCutoff]; ring)
  have hExp : Tendsto (fun k => 192 * Real.exp (-minorLogStageNegativeCutoff K k / 2)) atTop (𝓝 0) := by
    have h := logarithmicStageFraction_tendsto 48 K
    apply h.congr'
    exact Eventually.of_forall (fun k => by
      dsimp [logarithmicStageFraction, minorLogStageNegativeCutoff]
      rw [show -(2 * (logarithmicStageCutoff K k : ℝ)) / 2 =
        -(logarithmicStageCutoff K k : ℝ) by ring]
      norm_num)
  have h := ((hRound.add hMoment).add (diagonalAccuracy_tendsto.const_mul 4)).add hExp
  simpa only [minorLogStageTolerance, mul_zero, zero_add] using h

end CircularLaw
