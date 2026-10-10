import CircularLaw.GradualClassCounting

/-!
# The four explicit gradual-class entropy costs

The exact cap entropy separates into a dimension factor and four costs.
The bulk and middle costs depend only on the degree, the short tail
cost only on `a3`, and the initial cost has the factor `d^(-3/2)`.
This identity retains all grid-count constants and rank rounding bounds.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem gradualClassCountingEntropy_eq {n d : ℕ} {a₃ : ℝ}
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a₃) :
    gradualClassCountingEntropy n d a₃ = (n : ℝ) *
      (25 / (d : ℝ) ^ 3 * (1 + Real.log (1 + (d : ℝ) ^ 3 / 25)) +
        a₃ * (1 + Real.log (1 + 49 / a₃)) +
        1 / Real.rpow (d : ℝ) (2 / 3) *
          (1 + Real.log (1 + 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3))) +
        2 / Real.rpow (d : ℝ) (3 / 2) *
          (1 + Real.log (1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 *
            Real.rpow (d : ℝ) (3 / 2)))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR23 : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdR _
  have hR32 : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos hdR _
  have h₀ : (n : ℝ) / (25 * n / (d : ℝ) ^ 3) = (d : ℝ) ^ 3 / 25 := by
    field_simp [hnR.ne', hdR.ne']
  have h₁ : (49 * (n : ℝ)) / (a₃ * n) = 49 / a₃ := by
    field_simp [hnR.ne', ha.ne']
  have h₂ : (49 * (n : ℝ) * (d : ℝ) ^ 3) / ((n : ℝ) / Real.rpow (d : ℝ) (2 / 3)) =
      49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3) := by
    field_simp [hnR.ne', hR23.ne']
  have h₃ : (49 * (n : ℝ) ^ 13) / (2 * n / Real.rpow (d : ℝ) (3 / 2)) =
      (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2) := by
    field_simp [hnR.ne', hR32.ne']
  simp [gradualClassCountingEntropy, Fin.sum_univ_succ,
    gradualClassBlockEntropy, gradualClassSizeCap, gradualClassAlphabetCap]
  simp only [Real.rpow_eq_pow] at h₂ h₃
  rw [h₀, h₁, h₂, h₃]
  ring

theorem gradualClass_tail_cost_small {a₃ : ℝ} (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) :
    a₃ * (1 + Real.log (1 + 49 / a₃)) ≤ 1 / 4 := by
  let t := 1 + 49 / a₃
  have ht : 0 < t := by dsimp only [t]; positivity
  have hRoot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hLog : Real.log t ≤ 2 * Real.sqrt t := by
    have h := Real.log_le_sub_one_of_pos hRoot
    rw [Real.log_sqrt ht.le] at h
    linarith
  have hSquare : (a₃ * Real.sqrt t) ^ 2 = a₃ ^ 2 + 49 * a₃ := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    dsimp only [t]
    field_simp [ha.ne']
  have hBound : a₃ * Real.sqrt t ≤ 1 / 16 := by
    have hA : a₃ ^ 2 ≤ a₃ := by nlinarith
    nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hLog ha.le
  change a₃ * (1 + Real.log t) ≤ _
  nlinarith

theorem gradualClass_bulk_cost_bound {d : ℕ} (hd : 2 ≤ d) :
    25 / (d : ℝ) ^ 3 * (1 + Real.log (1 + (d : ℝ) ^ 3 / 25)) ≤
      25 / (d : ℝ) ^ 3 * (1 + 3 * Real.log d) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hCube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hdR 3
  norm_num at hCube
  have hArg : 1 + (d : ℝ) ^ 3 / 25 ≤ (d : ℝ) ^ 3 := by linarith
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < 1 + (d : ℝ) ^ 3 / 25) hArg
  rw [Real.log_pow] at hLog
  exact mul_le_mul_of_nonneg_left (by simpa using add_le_add_left hLog 1) (by positivity)

theorem gradualClass_middle_cost_bound {d : ℕ} (hd : 49 ≤ d) (hLog : 1 ≤ Real.log d) :
    1 / Real.rpow (d : ℝ) (2 / 3) *
      (1 + Real.log (1 + 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3))) ≤
    1 / Real.rpow (d : ℝ) (2 / 3) * (1 + 6 * Real.log d) := by
  have hdR : (49 : ℝ) ≤ d := by exact_mod_cast hd
  have hdPos : (0 : ℝ) < d := by linarith
  have hRPos : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos hdPos _
  have hDOne : (1 : ℝ) ≤ d := by linarith
  have hR : Real.rpow (d : ℝ) (2 / 3) ≤ d := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hDOne (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hProd : 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3) ≤ (d : ℝ) ^ 5 := by
    calc
      _ ≤ 49 * (d : ℝ) ^ 3 * d := mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (d : ℝ) * (d : ℝ) ^ 3 * d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdR (by positivity))
          (Nat.cast_nonneg d)
      _ = _ := by ring
  have hArg : 1 + 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3) ≤
      2 * (d : ℝ) ^ 5 := by have h := one_le_pow₀ hDOne (n := 5); linarith
  have hLogArg := Real.log_le_log (by positivity :
    (0 : ℝ) < 1 + 49 * (d : ℝ) ^ 3 * Real.rpow (d : ℝ) (2 / 3)) hArg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (d : ℝ) ^ 5 ≠ 0),
    Real.log_pow] at hLogArg
  have hTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / Real.rpow (d : ℝ) (2 / 3))
  norm_num only [Nat.cast_ofNat] at hLogArg
  linarith

theorem gradualClass_initial_cost_bound {n d : ℕ} {C : ℝ} (hn : 49 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (hC : 0 < C)
    (hLog : 1 ≤ Real.log n) (hLower : C * Real.log n ≤ (d : ℝ)) :
    2 / Real.rpow (d : ℝ) (3 / 2) *
      (1 + Real.log (1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2))) ≤
    34 / (C * Real.sqrt d) := by
  have hnR : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnPos : (0 : ℝ) < n := by linarith
  have hdPos : (0 : ℝ) < d := by linarith
  have hRPos : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos hdPos _
  have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hR : Real.rpow (d : ℝ) (3 / 2) ≤ (n : ℝ) ^ 2 := by
    apply le_trans _ (pow_le_pow_left₀ (Nat.cast_nonneg d) hdnR 2)
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hdR (by norm_num : (3 / 2 : ℝ) ≤ (2 : ℕ))
  have hProd : (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2) ≤ (n : ℝ) ^ 15 := by
    calc
      _ ≤ (49 / 2 : ℝ) * (n : ℝ) ^ 12 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (n : ℝ) * (n : ℝ) ^ 12 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : (49 / 2 : ℝ) ≤ n) (by positivity))
          (by positivity)
      _ = _ := by ring
  have hArg : 1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2) ≤
      2 * (n : ℝ) ^ 15 := by
    have h := one_le_pow₀ (by linarith : (1 : ℝ) ≤ n) (n := 15)
    linarith
  have hLogArg := Real.log_le_log (by positivity :
    (0 : ℝ) < 1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 * Real.rpow (d : ℝ) (3 / 2)) hArg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) ^ 15 ≠ 0),
    Real.log_pow] at hLogArg
  have hTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLogN : Real.log n ≤ (d : ℝ) / C := (le_div_iff₀ hC).mpr (by nlinarith)
  have hLogBound : 1 + Real.log (1 + (49 / 2 : ℝ) * (n : ℝ) ^ 12 *
      Real.rpow (d : ℝ) (3 / 2)) ≤ 17 * ((d : ℝ) / C) := by
    norm_num only [Nat.cast_ofNat] at hLogArg
    linarith
  calc
    _ ≤ (2 / Real.rpow (d : ℝ) (3 / 2)) * (17 * ((d : ℝ) / C)) :=
      mul_le_mul_of_nonneg_left hLogBound (by positivity)
    _ = _ := by
      rw [degree_three_halves_eq hd]
      have hD : (0 : ℝ) < d := by exact_mod_cast hd
      have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hD
      field_simp [hD.ne', hRoot.ne', hC.ne']
      norm_num

end CircularLaw
