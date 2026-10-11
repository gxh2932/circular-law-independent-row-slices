import CircularLaw.GaussianNonflatUniform
import CircularLaw.GaussianSourceAntiClustering

/-!
# Coordinate and radius comparisons for a forbidden normal vector

In the manuscript's standing degree band the inverse codimension ratio
dominates log(n). The checked uniform largest-coordinate estimate then
suffices for all the required reverse-steepness inequalities. Polynomial
losses in the combination radius are absorbed by an absolute exponent.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory

namespace CircularLaw

theorem gaussianUniformCoordinate_log_cap {n p : ℕ} (hn : 64 ≤ n)
    (hp : 0 < p) (hpn : p ≤ n) {q : ℝ}
    (hpq : (p : ℝ) ≤ 2 * q) (hLog : Real.log (n : ℝ) ≤ q) (hQ : 12288 ≤ q) :
    Real.sqrt p * Real.sqrt (Real.log ((p : ℝ) * n / (1 / 64))) ≤ q ^ 2 / 4096 := by
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpnR : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have hLogEq : Real.log ((p : ℝ) * n / (1 / 64)) =
      Real.log 64 + Real.log p + Real.log n := by
    rw [show (p : ℝ) * n / (1 / 64) = 64 * ((p : ℝ) * n) by ring,
      Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) (mul_ne_zero hpR.ne' hnPos.ne'),
      Real.log_mul hpR.ne' hnPos.ne']
    ring
  have hLog64 := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hnR
  have hLogPN := Real.log_le_log hpR hpnR
  have hLogBound : Real.log ((p : ℝ) * n / (1 / 64)) ≤ 3 * q := by
    rw [hLogEq]
    linarith
  have hLogNonneg : 0 ≤ Real.log ((p : ℝ) * n / (1 / 64)) := by
    rw [hLogEq]
    exact add_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hpOne))
      (Real.log_nonneg (by linarith))
  have hMul := mul_le_mul hpq hLogBound hLogNonneg (by linarith : 0 ≤ 2 * q)
  have hSq : (Real.sqrt p * Real.sqrt (Real.log ((p : ℝ) * n / (1 / 64)))) ^ 2 ≤ 6 * q ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p), Real.sq_sqrt hLogNonneg]
    nlinarith only [hMul]
  have hThree : Real.sqrt p * Real.sqrt (Real.log ((p : ℝ) * n / (1 / 64))) ≤ 3 * q := by
    apply (sq_le_sq₀ (by positivity) (by linarith : 0 ≤ 3 * q)).mp
    exact hSq.trans (by nlinarith only [sq_nonneg q])
  apply hThree.trans
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4096)).mpr
  nlinarith only [hQ]

theorem orderedNormAt_le_coordinate_cap {n k : ℕ} (x : Fin n → ℂ)
    (hk : 0 < k) (hkn : k ≤ n) {U : ℝ} (hCoord : ∀ i, ‖x i‖ ≤ U) :
    orderedNormAt x k ≤ U := by
  rw [orderedNormAt_eq x hk hkn]
  exact hCoord _

theorem gaussianForbidden_reverse_from_coordinate_bounds {n L q r : ℕ}
    (hn : 0 < n) (hL : 0 < L) (hq : 0 < q)
    (hqr : q ≤ r) (hrn : r ≤ n) (hqL : q ≤ L)
    (v : Fin n → ℂ)
    (hLower : (L : ℝ) / (2048 * n) ≤ orderedNormAt v r)
    (hUpper : ∀ j, ‖v j‖ ≤ ((n : ℝ) / L) ^ 2 / 4096) :
    ∀ i : ℕ, 0 < i → i ≤ q → orderedNormAt v i ≤
      (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hLowerQ := hLower.trans (orderedNormAt_antitone v hq hqr hrn)
  have hRatio : 0 ≤ (n : ℝ) / L := by positivity
  have hIdentity : (9 / 10 : ℝ) * ((n : ℝ) / L) ^ 3 * ((L : ℝ) / (2048 * n)) =
      (9 / 20480 : ℝ) * ((n : ℝ) / L) ^ 2 := by field_simp; ring
  intro i hi hiq
  have hin : i ≤ n := hiq.trans (hqr.trans hrn)
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hiL : (i : ℝ) ≤ L := by exact_mod_cast hiq.trans hqL
  have hRatioI : (n : ℝ) / L ≤ (n : ℝ) / i :=
    div_le_div_of_nonneg_left hnR.le hiR hiL
  calc
    _ ≤ ((n : ℝ) / L) ^ 2 / 4096 := orderedNormAt_le_coordinate_cap v hi hin hUpper
    _ ≤ (9 / 20480 : ℝ) * ((n : ℝ) / L) ^ 2 := by nlinarith only [sq_nonneg ((n : ℝ) / L)]
    _ = (9 / 10 : ℝ) * ((n : ℝ) / L) ^ 3 * ((L : ℝ) / (2048 * n)) := hIdentity.symm
    _ ≤ (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt v q := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRatio hRatioI 3) (by norm_num))
        hLowerQ (by positivity) (by positivity)

theorem gaussianSource_combination_radius_absorption {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {C : ℝ} (hC : 8192 ≤ C) {p : ℕ} (hp : (p : ℝ) ≤ 2 / t) :
    (p : ℝ) * gaussianSourceAlpha C t ≤
      Real.exp (-2 * gaussianSourceGrowth t) * t / 2048 := by
  have hGrowth := gaussianSourceGrowth_one_le ht ht1
  have hInvLog := gaussianSource_log_inverse_bound ht
  have hLog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hLog2048 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2048)
  have hScale := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ gaussianSourceGrowth t)
  have hLeftPos : 0 < (2 / t) * gaussianSourceAlpha C t := by
    exact mul_pos (div_pos (by norm_num) ht) (gaussianSourceAlpha_pos C t)
  have hRightPos : 0 < Real.exp (-2 * gaussianSourceGrowth t) * t / 2048 := by positivity
  have hLeftLog : Real.log ((2 / t) * gaussianSourceAlpha C t) =
      Real.log 2 - Real.log t - C * gaussianSourceGrowth t := by
    unfold gaussianSourceAlpha
    rw [Real.log_mul (div_ne_zero (by norm_num) ht.ne') (Real.exp_ne_zero _),
      Real.log_div (by norm_num) ht.ne']
    rw [Real.log_exp]
    ring
  have hRightLog : Real.log (Real.exp (-2 * gaussianSourceGrowth t) * t / 2048) =
      -2 * gaussianSourceGrowth t + Real.log t - Real.log 2048 := by
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) ht.ne') (by norm_num),
      Real.log_mul (Real.exp_ne_zero _) ht.ne', Real.log_exp]
  apply (mul_le_mul_of_nonneg_right hp (gaussianSourceAlpha_pos C t).le).trans
  apply (Real.log_le_log_iff hLeftPos hRightPos).mp
  rw [hLeftLog, hRightLog]
  nlinarith only [hGrowth, hInvLog, hLog2, hLog2048, hScale]

theorem sourceGaussian_combination_radius_absorption {n L p : ℕ}
    (hn : 0 < n) (hL : 0 < L) (hLn : L ≤ n) {C : ℝ} (hC : 8192 ≤ C)
    (hp : (p : ℝ) ≤ 2 * n / L) :
    (p : ℝ) * gaussianSourceAlpha C ((L : ℝ) / n) ≤
      Real.exp (-2 * structuralGrowth n L) * ((L : ℝ) / (2048 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have ht : 0 < (L : ℝ) / n := by positivity
  have ht1 : (L : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hLn)
  have hCount : (p : ℝ) ≤ 2 / ((L : ℝ) / n) := by
    convert hp using 1
    field_simp
  have h := gaussianSource_combination_radius_absorption ht ht1 hC hCount
  rw [gaussianSourceGrowth_ratio] at h
  convert h using 1
  ring

end CircularLaw
