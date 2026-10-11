import CircularLaw.GaussianGreedyClusters
import CircularLaw.StructuralParameters

/-!
# The literal Gaussian source parameters

The ratio `t` is `L/n`. The probability parameter, small-ball parameter,
integer cluster cutoff and exponential radius keep the manuscript choices.
An explicit absolute loss of 1024 in the radius exponent absorbs the
polynomial and logarithmic factors for every `0<t<=1`.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def gaussianSourceGrowth (t : ℝ) : ℝ := Real.rpow (1 / t) (1 / 288)

def gaussianSourceAlpha (C t : ℝ) : ℝ := Real.exp (-C * gaussianSourceGrowth t)

def gaussianSourceBeta (t : ℝ) : ℝ := (1 / 4) * (t / 4) ^ 3

def gaussianSourceSmallBall (t : ℝ) : ℝ := (1 / 2) * Real.rpow t (3 / 2)

theorem gaussianSourceAlpha_pos (C t : ℝ) : 0 < gaussianSourceAlpha C t := Real.exp_pos _

theorem gaussianSourceBeta_pos {t : ℝ} (ht : 0 < t) : 0 < gaussianSourceBeta t := by
  unfold gaussianSourceBeta
  positivity

theorem gaussianSourceBeta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gaussianSourceBeta t := by
  unfold gaussianSourceBeta
  positivity

theorem gaussianSourceBeta_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    gaussianSourceBeta t < 1 := by
  have hPow : (t / 4) ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  unfold gaussianSourceBeta
  nlinarith only [hPow]

theorem gaussianSourceSmallBall_pos {t : ℝ} (ht : 0 < t) :
    0 < gaussianSourceSmallBall t := by
  unfold gaussianSourceSmallBall
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos ht _)

theorem gaussianSourceSmallBall_sq {t : ℝ} (ht : 0 ≤ t) :
    gaussianSourceSmallBall t ^ 2 = t ^ 3 / 4 := by
  have hSq : Real.rpow t (3 / 2) ^ 2 = t ^ 3 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_two, ← Real.rpow_mul ht]
    norm_num
  unfold gaussianSourceSmallBall
  rw [mul_pow, hSq]
  ring

theorem gaussianSourceBeta_inverse {t : ℝ} (ht : 0 < t) :
    1 / gaussianSourceBeta t = 256 / t ^ 3 := by
  unfold gaussianSourceBeta
  field_simp
  ring

theorem gaussianSourceBeta_log_inverse {t : ℝ} (ht : 0 < t) :
    Real.log (1 / gaussianSourceBeta t) = Real.log 256 - 3 * Real.log t := by
  rw [gaussianSourceBeta_inverse ht, Real.log_div (by norm_num) (pow_ne_zero _ ht.ne'),
    Real.log_pow]
  norm_num

theorem gaussianSourceGrowth_one_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ gaussianSourceGrowth t := by
  unfold gaussianSourceGrowth
  exact Real.one_le_rpow ((one_le_div ht).mpr ht1) (by norm_num)

theorem gaussianSource_log_inverse_bound {t : ℝ} (ht : 0 < t) :
    -Real.log t ≤ 288 * gaussianSourceGrowth t := by
  have h := Real.log_le_rpow_div (le_of_lt (one_div_pos.mpr ht))
    (by norm_num : (0 : ℝ) < 1 / 288)
  rw [one_div, Real.log_inv] at h
  simpa [gaussianSourceGrowth, Real.rpow_eq_pow, one_div, div_eq_mul_inv, mul_comm] using h

theorem gaussianSourceBeta_log_inverse_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.log (1 / gaussianSourceBeta t) ≤ 1119 * gaussianSourceGrowth t := by
  have hLog := gaussianSource_log_inverse_bound ht
  have hGrowth := gaussianSourceGrowth_one_le ht ht1
  have hConst := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256)
  rw [gaussianSourceBeta_log_inverse ht]
  linarith

theorem gaussianSource_radius_pos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (C : ℝ) :
    0 < gaussianClusterRadius (gaussianSourceAlpha C t) (gaussianSourceBeta t)
      (gaussianSourceSmallBall t) := by
  unfold gaussianClusterRadius
  have hLog : 0 < Real.log (1 / gaussianSourceBeta t) :=
    Real.log_pos ((one_lt_div (gaussianSourceBeta_pos ht)).mpr (gaussianSourceBeta_lt_one ht ht1))
  exact div_pos (mul_pos (gaussianSourceAlpha_pos C t) (gaussianSourceSmallBall_pos ht))
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr hLog))

theorem gaussianSource_radius_log {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (C : ℝ) :
    Real.log (gaussianClusterRadius (gaussianSourceAlpha C t) (gaussianSourceBeta t)
      (gaussianSourceSmallBall t)) =
        -C * gaussianSourceGrowth t + (3 / 2) * Real.log t - Real.log 8 -
          Real.log (Real.log (1 / gaussianSourceBeta t)) / 2 := by
  have hLog : 0 < Real.log (1 / gaussianSourceBeta t) :=
    Real.log_pos ((one_lt_div (gaussianSourceBeta_pos ht)).mpr (gaussianSourceBeta_lt_one ht ht1))
  have hRadius : gaussianClusterRadius (gaussianSourceAlpha C t) (gaussianSourceBeta t)
      (gaussianSourceSmallBall t) =
        Real.exp (-C * gaussianSourceGrowth t) * Real.rpow t (3 / 2) /
          (8 * Real.sqrt (Real.log (1 / gaussianSourceBeta t))) := by
    unfold gaussianClusterRadius gaussianSourceAlpha gaussianSourceSmallBall
    ring
  rw [hRadius]
  simp only [Real.rpow_eq_pow]
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) (Real.rpow_pos_of_pos ht _).ne')
    (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hLog).ne'),
    Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos ht _).ne', Real.log_exp,
    Real.log_rpow ht, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hLog).ne',
    Real.log_sqrt hLog.le]
  ring

theorem gaussianSource_radius_absorption {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (C : ℝ) :
    Real.exp (-(C + 1024) * gaussianSourceGrowth t) ≤
      gaussianClusterRadius (gaussianSourceAlpha C t) (gaussianSourceBeta t)
        (gaussianSourceSmallBall t) := by
  have hGrowth := gaussianSourceGrowth_one_le ht ht1
  have hInvLog := gaussianSource_log_inverse_bound ht
  have hLog := gaussianSourceBeta_log_inverse_bound ht ht1
  have hLogPos : 0 < Real.log (1 / gaussianSourceBeta t) :=
    Real.log_pos ((one_lt_div (gaussianSourceBeta_pos ht)).mpr (gaussianSourceBeta_lt_one ht ht1))
  have hLogLog := Real.log_le_sub_one_of_pos hLogPos
  have hEight := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  rw [← Real.exp_log (gaussianSource_radius_pos ht ht1 C)]
  apply Real.exp_le_exp.mpr
  rw [gaussianSource_radius_log ht ht1]
  nlinarith only [hGrowth, hInvLog, hLog, hLogLog, hEight]

theorem gaussianSource_half_cutoff {L : ℕ} (hL : 2 ≤ L) :
    0 < L / 2 ∧ 2 * (L / 2) ≤ L ∧ L ≤ 3 * (L / 2) := by omega

theorem gaussianSource_failure_bound {n L : ℕ} (hn : 0 < n) (hL : 2 ≤ L) :
    (gaussianSourceSmallBall ((L : ℝ) / n) * n) ^ 2 / (2 * (L / 2 : ℕ) ^ 2 : ℝ) ≤
      (9 / 8 : ℝ) * ((L : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  obtain ⟨hb, _, hLb⟩ := gaussianSource_half_cutoff hL
  have hbR : (0 : ℝ) < (L / 2 : ℕ) := by exact_mod_cast hb
  have hLbR : (L : ℝ) ≤ 3 * (L / 2 : ℕ) := by exact_mod_cast hLb
  rw [mul_pow, gaussianSourceSmallBall_sq (div_nonneg hLR.le hnR.le)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((L / 2 : ℕ) : ℝ) ^ 2)).mpr
  have hSq : (L : ℝ) ^ 2 ≤ 9 * ((L / 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  field_simp
  nlinarith only [hSq]

end CircularLaw
