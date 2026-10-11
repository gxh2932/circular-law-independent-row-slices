import CircularLaw.SteepNetBudgets

/-!
# Absorbing the short-prefix and support entropy budgets

These finite inequalities allocate the source exponent to its four
actual costs. The thresholds involve fixed constants and positive
powers of the degree, so the next uniform-band step can discharge them.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem steep_net_T1_middle_absorbed {n d M : ℕ} (hd : 0 < d)
    (hN : (n : ℝ) ≤ 2 * M * Real.rpow (d : ℝ) (2 / 3))
    (hPower : 4 * steepNetMiddleConstant ≤ Real.rpow (d : ℝ) (5 / 6))
    (hLog : 0 ≤ Real.log (d : ℝ)) :
    steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) * Real.log (d : ℝ) ≤
      ((M : ℝ) / 2) * Real.log (d : ℝ) := by
  have hD : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hR23 : 0 ≤ Real.rpow (d : ℝ) (2 / 3) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hPowerScaled := mul_le_mul_of_nonneg_left hPower hR23
  rw [positive_degree_power_mul hd] at hPowerScaled
  rw [show (2 / 3 : ℝ) + (5 / 6) = 3 / 2 by norm_num] at hPowerScaled
  have hNScaled := mul_le_mul_of_nonneg_left hN steepNetMiddleConstant_pos.le
  have hMScaled := mul_le_mul_of_nonneg_left hPowerScaled (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hNumerator : steepNetMiddleConstant * (n : ℝ) ≤ ((M : ℝ) / 2) * Real.rpow (d : ℝ) (3 / 2) := by
    nlinarith
  have hRatio : steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) ≤ (M : ℝ) / 2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr hNumerator
  exact mul_le_mul_of_nonneg_right hRatio hLog

theorem steep_net_T1_high_absorbed {n d M : ℕ} {C : ℝ} (hd : 0 < d) (hC : 0 < C)
    (hN : (n : ℝ) ≤ 2 * M * Real.rpow (d : ℝ) (2 / 3))
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ)) (hLogN : 0 ≤ Real.log (n : ℝ))
    (hPower : 8 * steepNetHighConstant / C ≤ Real.rpow (d : ℝ) (1 / 12))
    (hLogD : 1 ≤ Real.log (d : ℝ)) :
    steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) ≤
      ((M : ℝ) / 2) * Real.log (d : ℝ) := by
  have hD : 0 < Real.rpow (d : ℝ) (7 / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hK := steepNetHighConstant_pos
  have hR23 : 0 ≤ Real.rpow (d : ℝ) (2 / 3) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hProduct : Real.rpow (d : ℝ) (2 / 3) * (d : ℝ) * Real.rpow (d : ℝ) (1 / 12) =
      Real.rpow (d : ℝ) (7 / 4) := by
    calc
      _ = Real.rpow (d : ℝ) (2 / 3) * Real.rpow (d : ℝ) 1 * Real.rpow (d : ℝ) (1 / 12) := by
        simp only [Real.rpow_eq_pow, Real.rpow_one]
      _ = _ := by rw [positive_degree_power_mul hd, positive_degree_power_mul hd]; norm_num
  have hPowerC := (div_le_iff₀ hC).mp hPower
  have hTerm := mul_le_mul_of_nonneg_right hPowerC
    (by positivity : (0 : ℝ) ≤ (M : ℝ) * Real.rpow (d : ℝ) (2 / 3) * d)
  rw [show Real.rpow (d : ℝ) (1 / 12) * C *
      ((M : ℝ) * Real.rpow (d : ℝ) (2 / 3) * d) =
        C * M * (Real.rpow (d : ℝ) (2 / 3) * d * Real.rpow (d : ℝ) (1 / 12)) by ring,
    hProduct] at hTerm
  have hNScaled := mul_le_mul_of_nonneg_left hN
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * steepNetHighConstant) hLogN)
  have hLowerScaled := mul_le_mul_of_nonneg_left hLower
    (by positivity : (0 : ℝ) ≤ 4 * steepNetHighConstant * M * Real.rpow (d : ℝ) (2 / 3))
  have hNumerator : 2 * steepNetHighConstant * (n : ℝ) * Real.log (n : ℝ) ≤
      ((M : ℝ) / 2) * Real.rpow (d : ℝ) (7 / 4) := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith
  have hRatio : steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) ≤
      (M : ℝ) / 2 := by
    rw [show steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) =
      (2 * steepNetHighConstant * n * Real.log n) / Real.rpow (d : ℝ) (7 / 4) by ring]
    exact (div_le_iff₀ hD).mpr hNumerator
  exact hRatio.trans (by nlinarith [mul_le_mul_of_nonneg_left hLogD (by positivity : (0 : ℝ) ≤ (M : ℝ) / 2)])

theorem steep_net_T2_middle_absorbed {n d M : ℕ} {a₃ : ℝ} (hd : 0 < d) (ha : 0 < a₃)
    (hN : a₃ * (n : ℝ) ≤ 2 * M)
    (hPower : 8 * steepNetMiddleConstant / a₃ ≤ Real.rpow (d : ℝ) (3 / 2))
    (hLog : 0 ≤ Real.log (d : ℝ)) :
    steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) * Real.log (d : ℝ) ≤
      ((M : ℝ) / 4) * Real.log (d : ℝ) := by
  have hD : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hPowerA := (div_le_iff₀ ha).mp hPower
  have hNScaled := mul_le_mul_of_nonneg_left hN steepNetMiddleConstant_pos.le
  have hMScaled := mul_le_mul_of_nonneg_left hPowerA (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hNumerator : steepNetMiddleConstant * (n : ℝ) ≤ ((M : ℝ) / 4) * Real.rpow (d : ℝ) (3 / 2) := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  have hRatio : steepNetMiddleConstant * ((n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) ≤ (M : ℝ) / 4 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr hNumerator
  exact mul_le_mul_of_nonneg_right hRatio hLog

theorem steep_net_T2_high_absorbed {n d M : ℕ} {a₃ C : ℝ} (hd : 0 < d) (ha : 0 < a₃) (hC : 0 < C)
    (hN : a₃ * (n : ℝ) ≤ 2 * M)
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ)) (hLogN : 0 ≤ Real.log (n : ℝ))
    (hPower : 16 * steepNetHighConstant / (a₃ * C) ≤ Real.rpow (d : ℝ) (3 / 4))
    (hLogD : 1 ≤ Real.log (d : ℝ)) :
    steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) ≤
      ((M : ℝ) / 4) * Real.log (d : ℝ) := by
  have hD : 0 < Real.rpow (d : ℝ) (7 / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hK := steepNetHighConstant_pos
  have hProduct : (d : ℝ) * Real.rpow (d : ℝ) (3 / 4) = Real.rpow (d : ℝ) (7 / 4) := by
    calc
      _ = Real.rpow (d : ℝ) 1 * Real.rpow (d : ℝ) (3 / 4) := by
        simp only [Real.rpow_eq_pow, Real.rpow_one]
      _ = _ := by rw [positive_degree_power_mul hd]; norm_num
  have hPowerA := (div_le_iff₀ (mul_pos ha hC)).mp hPower
  have hTerm := mul_le_mul_of_nonneg_right hPowerA (by positivity : (0 : ℝ) ≤ (M : ℝ) * d)
  rw [show Real.rpow (d : ℝ) (3 / 4) * (a₃ * C) * ((M : ℝ) * d) =
      a₃ * C * M * ((d : ℝ) * Real.rpow (d : ℝ) (3 / 4)) by ring, hProduct] at hTerm
  have hNScaled := mul_le_mul_of_nonneg_left hN
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * steepNetHighConstant) hLogN)
  have hLowerScaled := mul_le_mul_of_nonneg_left hLower
    (by positivity : (0 : ℝ) ≤ 4 * steepNetHighConstant * M)
  have hNumerator : 2 * steepNetHighConstant * (n : ℝ) * Real.log (n : ℝ) ≤
      ((M : ℝ) / 4) * Real.rpow (d : ℝ) (7 / 4) := by
    apply (mul_le_mul_iff_right₀ (mul_pos ha hC)).mp
    nlinarith
  have hRatio : steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) ≤
      (M : ℝ) / 4 := by
    rw [show steepNetHighConstant * (2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4)) * Real.log (n : ℝ) =
      (2 * steepNetHighConstant * n * Real.log n) / Real.rpow (d : ℝ) (7 / 4) by ring]
    exact (div_le_iff₀ hD).mpr hNumerator
  exact hRatio.trans (by nlinarith [mul_le_mul_of_nonneg_left hLogD (by positivity : (0 : ℝ) ≤ (M : ℝ) / 4)])

theorem steep_net_T1_support_absorbed {n d M : ℕ} (hd : 0 < d)
    (hN : (n : ℝ) ≤ 2 * M * Real.rpow (d : ℝ) (2 / 3)) (hLog : 3 ≤ Real.log (d : ℝ)) :
    (n : ℝ) * smallSetEntropy (1 / Real.rpow (d : ℝ) (2 / 3)) ≤
      2 * (M : ℝ) * Real.log (d : ℝ) := by
  have hD : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hRatio := (div_le_iff₀ hD).mpr hN
  have hCoeff : 1 + (2 / 3 : ℝ) * Real.log (d : ℝ) ≤ Real.log (d : ℝ) := by linarith
  rw [smallSetEntropy_inverse_degree_power hd]
  calc
    _ = ((n : ℝ) / Real.rpow (d : ℝ) (2 / 3)) * (1 + (2 / 3) * Real.log d) := by ring
    _ ≤ ((n : ℝ) / Real.rpow (d : ℝ) (2 / 3)) * Real.log d :=
      mul_le_mul_of_nonneg_left hCoeff (div_nonneg (Nat.cast_nonneg n) hD.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hRatio (by linarith)

theorem steep_net_T2_support_absorbed {n d M : ℕ} {a₃ : ℝ} (ha : 0 < a₃) (haOne : a₃ ≤ 1)
    (hN : a₃ * (n : ℝ) ≤ 2 * M)
    (hLog : 8 * smallSetEntropy a₃ / a₃ ≤ Real.log (d : ℝ)) :
    (n : ℝ) * smallSetEntropy a₃ ≤ ((M : ℝ) / 4) * Real.log (d : ℝ) := by
  have hη := smallSetEntropy_nonneg ha haOne
  have hNScaled := mul_le_mul_of_nonneg_left hN hη
  have hLogA := (div_le_iff₀ ha).mp hLog
  have hMScaled := mul_le_mul_of_nonneg_left hLogA (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith

end CircularLaw
