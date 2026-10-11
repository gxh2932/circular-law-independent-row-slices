import CircularLaw.HermitizationReplacementScale
import CircularLaw.ShiftedReplacementUpperBound

/-!
# Vanishing row replacement error at the rounded hermitization cutoff

The literal ceiling gives the lower bound for Q. Any polynomial degree
budget for the logarithmic regularization ratio then yields a vanishing
replacement error for every fixed 0<a<1. The cutoff budget remains an
explicit premise until it is discharged for each manuscript regime.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem degree_power_exponential_decay (d : ℕ → ℕ) (hDegree : Tendsto d atTop atTop)
    {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (b : ℝ) :
    Tendsto (fun n => Real.rpow (d n : ℝ) b *
      Real.exp (-c * Real.rpow (d n : ℝ) κ)) atTop (𝓝 0) := by
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hPower := (tendsto_rpow_atTop hκ).comp hCast
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / κ) c hc).comp hPower
  apply h.congr'
  exact Eventually.of_forall (fun n => by
    simp only [Function.comp_apply, Real.rpow_eq_pow]
    rw [← Real.rpow_mul (Nat.cast_nonneg (d n)), mul_div_cancel₀ b hκ.ne'])

def hermitizationReplacementEnvelope (d : ℕ) (a C b : ℝ) : ℝ :=
  9216 * Real.sqrt (2 * (1 + Real.log d) / Real.rpow (d : ℝ) (1 - a)) +
    (2 * rowDistanceTailConstant) * C * Real.rpow (d : ℝ) (b + 1 / 2) *
      Real.exp (-(1 / 524288) * Real.rpow (d : ℝ) (1 - a))

theorem hermitization_replacement_error_le_envelope {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) {a C b η R : ℝ} (hC : 0 ≤ C)
    (hrn : hermitizationDeletionCount n d a ≤ n) (hHalf : (d : ℝ) / n ≤ 1 / 2)
    (hLog : Real.log (rowReplacementUpperBound n η R / η) ≤ C * Real.rpow (d : ℝ) b) :
    rowReplacementErrorBound n d (n - hermitizationDeletionCount n d a) η R ≤
      hermitizationReplacementEnvelope d a C b := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower : 0 < Real.rpow (d : ℝ) (1 - a) := Real.rpow_pos_of_pos hdR _
  have hQ := hermitization_row_comparison_Q_lower hn hd hHalf (a := a)
  have hQPos : 0 < rowLogComparisonQ n d (hermitizationDeletionCount n d a) :=
    (div_pos hPower (by norm_num)).trans_le hQ
  have hLogD : 0 ≤ 1 + Real.log (d : ℝ) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
    linarith
  have hRatio : (1 + Real.log (d : ℝ)) / rowLogComparisonQ n d (hermitizationDeletionCount n d a) ≤
      2 * (1 + Real.log d) / Real.rpow (d : ℝ) (1 - a) := by
    apply (div_le_div_iff₀ hQPos hPower).mpr
    have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * (1 + Real.log d) by linarith)
    nlinarith only [h]
  have hExp : Real.exp (-(1 / 262144) * rowLogComparisonQ n d (hermitizationDeletionCount n d a)) ≤
      Real.exp (-(1 / 524288) * Real.rpow (d : ℝ) (1 - a)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hQ]
  have hConstant : 0 ≤ 2 * rowDistanceTailConstant := by
    unfold rowDistanceTailConstant
    positivity
  have hBad : (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) *
      Real.log (rowReplacementUpperBound n η R / η) *
      Real.exp (-(1 / 262144) * rowLogComparisonQ n d (hermitizationDeletionCount n d a)) ≤
      (2 * rowDistanceTailConstant) * C * Real.rpow (d : ℝ) (b + 1 / 2) *
        Real.exp (-(1 / 524288) * Real.rpow (d : ℝ) (1 - a)) := by
    calc
      _ ≤ (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) * (C * Real.rpow (d : ℝ) b) *
          Real.exp (-(1 / 262144) * rowLogComparisonQ n d (hermitizationDeletionCount n d a)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLog (mul_nonneg hConstant (Real.sqrt_nonneg _)))
          (Real.exp_nonneg _)
      _ ≤ (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) * (C * Real.rpow (d : ℝ) b) *
          Real.exp (-(1 / 524288) * Real.rpow (d : ℝ) (1 - a)) :=
        mul_le_mul_of_nonneg_left hExp (mul_nonneg
          (mul_nonneg hConstant (Real.sqrt_nonneg _))
          (mul_nonneg hC (Real.rpow_nonneg hdR.le _)))
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_add hdR, Real.sqrt_eq_rpow]
        ring
  unfold rowReplacementErrorBound hermitizationReplacementEnvelope
  rw [Nat.sub_sub_self hrn, rowLogDegree_eq d hd]
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRatio) (by norm_num)) hBad

theorem hermitization_replacement_envelope_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) {a : ℝ} (haOne : a < 1) (C b : ℝ) :
    Tendsto (fun n => hermitizationReplacementEnvelope (d n) a C b) atTop (𝓝 0) := by
  have hκ : 0 < 1 - a := sub_pos.mpr haOne
  have hCast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hInv := ((tendsto_rpow_atTop hκ).comp hCast).inv_tendsto_atTop
  have hLog : Tendsto (fun n => Real.log (d n : ℝ) / Real.rpow (d n : ℝ) (1 - a))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow] using
      (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero.comp hCast
  have hRatio : Tendsto (fun n => 2 * (1 + Real.log (d n : ℝ)) /
      Real.rpow (d n : ℝ) (1 - a)) atTop (𝓝 0) := by
    have h := (hInv.add hLog).const_mul 2
    simp only [add_zero, mul_zero] at h
    apply h.congr'
    exact Eventually.of_forall (fun n => by dsimp; ring)
  have hGood := hRatio.sqrt.const_mul 9216
  have hBad := (degree_power_exponential_decay d hDegree hκ
    (by norm_num : (0 : ℝ) < 1 / 524288) (b + 1 / 2)).const_mul ((2 * rowDistanceTailConstant) * C)
  have h := hGood.add hBad
  simpa only [Real.sqrt_zero, mul_zero, add_zero, hermitizationReplacementEnvelope,
    mul_assoc] using h

theorem hermitization_replacement_error_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    {a C b : ℝ} (ha : 0 < a) (haOne : a < 1) (hC : 0 ≤ C) (η R : ℕ → ℝ)
    (hη : ∀ᶠ n in atTop, 0 < η n)
    (hLog : ∀ᶠ n in atTop, Real.log (rowReplacementUpperBound n (η n) (R n) / η n) ≤
      C * Real.rpow (d n : ℝ) b) :
    Tendsto (fun n => rowReplacementErrorBound n (d n)
      (n - hermitizationDeletionCount n (d n) a) (η n) (R n)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hermitization_replacement_envelope_tendsto_zero d hDegree haOne C b)
  · filter_upwards [hη] with n hn
    exact rowReplacementErrorBound_nonneg _ _ _ hn _
  · have hHalf := hSparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hη, hLog, hHalf, eventually_valid_bernoulli_degrees hDegree hSparse,
      eventually_hermitization_deletion_valid d hDegree hSparse ha haOne.le] with n hηn hLn hH hd hr
    exact hermitization_replacement_error_le_envelope (lt_of_lt_of_le hd.1 hd.2) hd.1 hC
      hr.2.1.le hH.le hLn

end CircularLaw
