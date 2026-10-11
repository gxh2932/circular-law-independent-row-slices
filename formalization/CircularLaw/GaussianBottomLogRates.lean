import CircularLaw.GaussianUniformQuantiles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing Gaussian logarithmic budgets

The sqrt(n) exceptional ranks cost o(n) logarithmically. At a fixed
bottom fraction eta, the remaining entropy budget converges to
eta*(log(16/eta)+1), which tends to zero as eta decreases to zero.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem natural_sqrt_cast_le_real_sqrt (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  calc
    (Nat.sqrt n : ℝ) = Real.sqrt ((Nat.sqrt n : ℝ) ^ 2) :=
      (Real.sqrt_sq (Nat.cast_nonneg _)).symm
    _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' n)

theorem natural_sqrt_ratio_bound {n : ℕ} (hn : 0 < n) :
    (Nat.sqrt n : ℝ) / n ≤ (Real.sqrt n)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRoot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  calc
    _ ≤ Real.sqrt n / n := div_le_div_of_nonneg_right (natural_sqrt_cast_le_real_sqrt n) hnR.le
    _ = Real.sqrt n / (Real.sqrt n) ^ 2 := by rw [Real.sq_sqrt hnR.le]
    _ = _ := by field_simp

theorem natural_sqrt_ratio_tendsto :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  have hLimit := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => by positivity))
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact natural_sqrt_ratio_bound hn

theorem natural_sqrt_log_budget_tendsto :
    Tendsto (fun n : ℕ => (4 * (Nat.sqrt n : ℝ) * Real.log n) / n) atTop (𝓝 0) := by
  have hLimit : Tendsto (fun n : ℕ => 4 * (Real.log n / Real.sqrt n)) atTop (𝓝 0) := by
    simpa only [← Real.sqrt_eq_rpow, mul_zero] using
      (((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop).const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn)))
      (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnPos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hRoot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    calc
      _ ≤ (4 * Real.sqrt n * Real.log n) / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (natural_sqrt_cast_le_real_sqrt n) (by norm_num)) hLog) hnR.le
      _ = (4 * Real.sqrt n * Real.log n) / (Real.sqrt n) ^ 2 := by
        rw [Real.sq_sqrt hnR.le]
      _ = _ := by field_simp

def gaussianBottomLogBudget (eta : ℝ) (n : ℕ) : ℝ :=
  (4 * (Nat.sqrt n : ℝ) * Real.log n) / n +
    ((gaussianQuantileDeletion eta n : ℝ) / n) *
      (Real.log (16 * (n : ℝ) / gaussianQuantileDeletion eta n) + 1)

theorem gaussian_bottom_log_budget_tendsto {eta : ℝ} (hEta : 0 < eta) :
    Tendsto (gaussianBottomLogBudget eta) atTop (𝓝 (eta * (Real.log (16 / eta) + 1))) := by
  have hRatio := gaussian_quantile_deletion_ratio_tendsto hEta.le
  have hInv := (hRatio.inv₀ hEta.ne').const_mul 16
  have hLog : Tendsto
      (fun n : ℕ => Real.log (16 * (n : ℝ) / gaussianQuantileDeletion eta n))
      atTop (𝓝 (Real.log (16 / eta))) := by
    have h := hInv.log (by positivity : (16 : ℝ) * eta⁻¹ ≠ 0)
    have hFunction : (fun n : ℕ => Real.log (16 * ((gaussianQuantileDeletion eta n : ℝ) / n)⁻¹)) =
        (fun n : ℕ => Real.log (16 * (n : ℝ) / gaussianQuantileDeletion eta n)) := by
      funext n
      rw [inv_div]
      congr 1
      ring
    rw [hFunction] at h
    simpa only [div_eq_mul_inv] using h
  have h := natural_sqrt_log_budget_tendsto.add (hRatio.mul (hLog.add_const 1))
  simpa only [zero_add] using h

theorem gaussian_bottom_entropy_small_fraction :
    Tendsto (fun eta : ℝ => eta * (Real.log (16 / eta) + 1)) (𝓝[>] 0) (𝓝 0) := by
  have hLog := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at hLog
  have hId : Tendsto (fun eta : ℝ => eta) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := (hId.mul_const (Real.log 16 + 1)).sub hLog
  simp only [zero_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with eta hEta
  rw [Real.log_div (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hEta)]
  ring

theorem gaussian_sqrt_smaller_than_fixed_fraction {eta : ℝ} (hEta : 0 < eta) :
    ∀ᶠ n in atTop, 2 * Nat.sqrt n < gaussianQuantileDeletion eta n := by
  have hLower := (gaussian_quantile_deletion_ratio_tendsto hEta.le).eventually
    (lt_mem_nhds (by linarith : eta / 2 < eta))
  have hUpper := natural_sqrt_ratio_tendsto.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < eta / 4))
  filter_upwards [hLower, hUpper, eventually_gt_atTop 0] with n hnLower hnUpper hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNat : (2 : ℝ) * Nat.sqrt n < gaussianQuantileDeletion eta n := by
    have h1 := (lt_div_iff₀ hnR).mp hnLower
    have h2 := (div_lt_iff₀ hnR).mp hnUpper
    linarith
  exact_mod_cast hNat

end CircularLaw
