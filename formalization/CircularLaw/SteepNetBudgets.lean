import CircularLaw.SteepNetRanks

/-!
# A quantitative entropy budget for the steep nets

Only the base grid and support entropy have a macroscopic contribution.
The two short-prefix budgets below keep every floor and ceiling in the
finite count before replacing them by proved density bounds.
-/

noncomputable section
open Classical

namespace CircularLaw

def steepNetMiddleConstant : ℝ := 13 + Real.log 1936
def steepNetHighConstant : ℝ := 18 + Real.log 121

theorem steepNetMiddleConstant_pos : 0 < steepNetMiddleConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1936)
  unfold steepNetMiddleConstant
  linarith

theorem steepNetHighConstant_pos : 0 < steepNetHighConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 121)
  unfold steepNetHighConstant
  linarith

theorem smallSetEntropy_inverse_degree_power {d : ℕ} (hd : 0 < d) (a : ℝ) :
    smallSetEntropy (1 / Real.rpow (d : ℝ) a) =
      (1 + a * Real.log (d : ℝ)) / Real.rpow (d : ℝ) a := by
  have hLog : Real.log (1 / Real.rpow (d : ℝ) a) = -(a * Real.log (d : ℝ)) := by
    rw [one_div, Real.log_inv, positive_degree_power_log hd]
  rw [smallSetEntropy, hLog]
  ring

theorem steepNetGridCount_log_base_one {d : ℕ} (hd : 0 < d) :
    Real.log (steepNetGridCount d 1) ≤ Real.log 121 + 3 * Real.log (d : ℝ) := by
  apply (steepNetGridCount_log_le (steepNetGridCount_base_one hd)).trans_eq
  rw [Real.log_mul (by norm_num : (121 : ℝ) ≠ 0) (by exact_mod_cast pow_ne_zero 3 hd.ne'), Real.log_pow]
  norm_num

theorem steepNetGridCount_log_base_power {d : ℕ} (hd : 0 < d) :
    Real.log (steepNetGridCount d (Real.rpow (d : ℝ) (3 / 2))) ≤
      Real.log 121 + 6 * Real.log (d : ℝ) := by
  apply (steepNetGridCount_log_le (steepNetGridCount_base_power hd)).trans_eq
  rw [Real.log_mul (by norm_num : (121 : ℝ) ≠ 0) (by exact_mod_cast pow_ne_zero 6 hd.ne'), Real.log_pow]
  norm_num

theorem steepNetGridCount_log_middle {d : ℕ} (hd : 0 < d) {cap : ℝ}
    (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2)) :
    Real.log (steepNetGridCount d (4 * (d : ℝ) * cap)) ≤ Real.log 1936 + 8 * Real.log (d : ℝ) := by
  apply (steepNetGridCount_log_le (steepNetGridCount_middle hd hCap hCapUpper)).trans_eq
  rw [Real.log_mul (by norm_num : (1936 : ℝ) ≠ 0) (by exact_mod_cast pow_ne_zero 8 hd.ne'), Real.log_pow]
  norm_num

theorem steepNetGridCount_log_high {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) (hLogN : 1 ≤ Real.log (n : ℝ)) {cap : ℝ}
    (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2)) :
    Real.log (steepNetGridCount d ((n : ℝ) ^ 6 * cap)) ≤ steepNetHighConstant * Real.log (n : ℝ) := by
  have hBound := steepNetGridCount_log_le (steepNetGridCount_high hn hd hCap hCapUpper)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 6 hdR.ne')) (pow_ne_zero 12 hnR.ne'),
    Real.log_mul (by norm_num : (121 : ℝ) ≠ 0) (pow_ne_zero 6 hdR.ne'), Real.log_pow] at hBound
  have hLogDN := Real.log_le_log hdR (by exact_mod_cast hdn : (d : ℝ) ≤ n)
  have hConstant := mul_le_mul_of_nonneg_left hLogN (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 121))
  unfold steepNetHighConstant
  norm_num at hBound
  linarith

theorem steep_net_middle_budget {n d : ℕ} (hd : 0 < d) (hLogD : 1 ≤ Real.log (d : ℝ))
    {cap : ℝ} (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2)) :
    2 * (n : ℝ) * smallSetEntropy (1 / Real.rpow (d : ℝ) (3 / 2)) +
      (firstSteepScale n d - 1 : ℕ) * Real.log (steepNetGridCount d (4 * (d : ℝ) * cap)) ≤
        steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) * Real.log (d : ℝ) := by
  have hLog := steepNetGridCount_log_middle hd hCap hCapUpper
  have hLogPositive : 0 ≤ Real.log 1936 + 8 * Real.log (d : ℝ) := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1936)
    linarith
  have hMiddle := (mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (firstSteepScale_prev_upper n d) hLogPositive)
  have hCoeff : 2 + Real.log 1936 + 11 * Real.log (d : ℝ) ≤
      steepNetMiddleConstant * Real.log (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hLogD
      (by have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1936); linarith : (0 : ℝ) ≤ 2 + Real.log 1936)
    unfold steepNetMiddleConstant
    linarith
  have hN : 0 ≤ (n : ℝ) / Real.rpow (d : ℝ) (3 / 2) :=
    div_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  rw [smallSetEntropy_inverse_degree_power hd]
  have hScaled := mul_le_mul_of_nonneg_left hCoeff hN
  calc
    _ ≤ 2 * (n : ℝ) * ((1 + (3 / 2) * Real.log d) / Real.rpow (d : ℝ) (3 / 2)) +
        ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) * (Real.log 1936 + 8 * Real.log d) :=
      add_le_add (le_refl _) hMiddle
    _ = ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) *
        (2 + Real.log 1936 + 11 * Real.log d) := by ring
    _ ≤ _ := by convert hScaled using 1; ring

theorem steep_net_entropy_budget {n d next : ℕ} {cap t b : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hLogD : 1 ≤ Real.log (d : ℝ))
    (hLogN : 1 ≤ Real.log (n : ℝ)) (hp : 1 ≤ steepStride d) (hn1 : 0 < firstSteepScale n d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (hCubic : 4 * d ≤ steepStride d ^ 3)
    (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2))
    (hBase : Real.log (steepNetGridCount d cap) ≤ b) :
    steepNetCountEntropy n d next cap t ≤ (n : ℝ) * smallSetEntropy t + (next : ℝ) * b +
      steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) * Real.log (d : ℝ) +
        steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) := by
  have hMid := steep_net_middle_budget (n := n) hd hLogD hCap hCapUpper
  have hHigh := steepNetGridCount_log_high hn hd hdn hLogN hCap hCapUpper
  have hDensity := steep_net_high_prefix_density hd hp hn1 hDimension hCubic
  have hHighCost :
      (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1 : ℕ) *
        Real.log (steepNetGridCount d ((n : ℝ) ^ 6 * cap)) ≤
          steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hHigh (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hDensity (mul_nonneg steepNetHighConstant_pos.le (by linarith)))
    convert h using 1
    ring
  have hBaseCost := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg next : (0 : ℝ) ≤ next)
  unfold steepNetCountEntropy
  linarith

end CircularLaw
