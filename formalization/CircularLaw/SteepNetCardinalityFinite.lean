import CircularLaw.SteepNetAbsorption

/-!
# The source exponent seven, with explicit finite thresholds

The actual product count, including the separate constant grid, has the
source exponent. `T1` spends four units on its base grid, two on support
entropy and one on the short prefixes. `T2` spends six and a quarter units
on the base grid and three quarter-units on its remaining costs.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem source_kernel_dimension_twice_degree {n d : ℕ} (h : SourceKernelConditions n d) :
    0 < n ∧ 0 < d ∧ 2 * d ≤ n := by
  have hd : 0 < d := by have hLarge := h.degree_large; omega
  have hPower := Nat.pow_le_pow_right hd (by decide : 1 ≤ 4)
  simp only [pow_one] at hPower
  have hDimension := h.dimension_fourth
  exact ⟨by nlinarith, hd, by nlinarith⟩

theorem secondSteepScale_prev_density (n d : ℕ) :
    (secondSteepScale n d - 1 : ℕ) ≤ (1 / Real.rpow (d : ℝ) (2 / 3)) * n := by
  have hRatio : 0 ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3) :=
    div_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg d) (2 / 3))
  have hFloor := Nat.floor_le hRatio
  have hPrev : (secondSteepScale n d - 1 : ℕ) ≤ secondSteepScale n d := Nat.sub_le _ _
  have hPrevR : ((secondSteepScale n d - 1 : ℕ) : ℝ) ≤ secondSteepScale n d := by exact_mod_cast hPrev
  apply hPrevR.trans
  convert hFloor using 1
  ring

theorem steep_net_T1_count_seven {n d : ℕ} {C : ℝ} (h : SourceKernelConditions n d)
    (hCubic : 4 * d ≤ steepStride d ^ 3) (hC : 0 < C)
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ))
    (hLog : 3 ≤ Real.log (d : ℝ)) (hBase : Real.log 121 ≤ Real.log (d : ℝ))
    (hMid : 4 * steepNetMiddleConstant ≤ Real.rpow (d : ℝ) (5 / 6))
    (hHigh : 8 * steepNetHighConstant / C ≤ Real.rpow (d : ℝ) (1 / 12)) :
    ((steepNetCountBound n d (secondSteepScale n d) 1 * steepNetGridCount d 1 : ℕ) : ℝ) ≤
      Real.exp (7 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ)) := by
  have hDimension := source_kernel_dimension_twice_degree h
  have hn := hDimension.1
  have hd := hDimension.2.1
  have hdn : d ≤ n := by omega
  have hLogN : 1 ≤ Real.log (n : ℝ) := by
    have hMonotone := Real.log_le_log (by exact_mod_cast hd : (0 : ℝ) < d) (by exact_mod_cast hdn : (d : ℝ) ≤ n)
    linarith
  have hFirst := firstSteepScale_pos hn hd
  have hSecond := secondSteepScale_valid hd h.dimension_root
  have hN := secondSteepScale_density_lower hd hDimension.2.2
  have hCap : 1 ≤ Real.rpow (d : ℝ) (3 / 2) := Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hT : 0 < 1 / Real.rpow (d : ℝ) (2 / 3) := div_pos zero_lt_one (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  have hTOne : 1 / Real.rpow (d : ℝ) (2 / 3) ≤ 1 := by
    apply (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)).mpr
    exact Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  apply (steep_net_count_entropy_bound hd (by have hp := h.stride_pos; omega : 1 ≤ steepStride d)
    hFirst hSecond.1 hT hTOne (secondSteepScale_prev_density n d)).trans
  apply Real.exp_le_exp.mpr
  have hBudget := steep_net_entropy_budget (next := secondSteepScale n d)
    (t := 1 / Real.rpow (d : ℝ) (2 / 3)) hn hd hdn (by linarith : 1 ≤ Real.log (d : ℝ))
    hLogN (by have hp := h.stride_pos; omega : 1 ≤ steepStride d) hFirst h.dimension_root hCubic
      (le_refl (1 : ℝ)) hCap (steepNetGridCount_log_base_one hd)
  have hSupport := steep_net_T1_support_absorbed hd hN hLog
  have hMiddle := steep_net_T1_middle_absorbed hd hN hMid (by linarith : 0 ≤ Real.log (d : ℝ))
  have hHighBudget := steep_net_T1_high_absorbed hd hC hN hLower (by linarith : 0 ≤ Real.log (n : ℝ))
    hHigh (by linarith : 1 ≤ Real.log (d : ℝ))
  have hBaseCost : (secondSteepScale n d : ℝ) * (Real.log 121 + 3 * Real.log (d : ℝ)) ≤
      4 * (secondSteepScale n d : ℝ) * Real.log (d : ℝ) := by
    have hScaled := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg (secondSteepScale n d) : (0 : ℝ) ≤ secondSteepScale n d)
    linarith
  exact hBudget.trans (by linarith)

theorem steep_net_T2_count_seven {n d : ℕ} {a₃ C : ℝ}
    (ha : 0 < a₃) (haOne : a₃ ≤ 1) (hSize : 2 ≤ a₃ * (n : ℝ))
    (h : SourceKernelConditions n d) (hCubic : 4 * d ≤ steepStride d ^ 3) (hC : 0 < C)
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ))
    (hLog : 1 ≤ Real.log (d : ℝ)) (hBase : 4 * Real.log 121 ≤ Real.log (d : ℝ))
    (hSupport : 8 * smallSetEntropy a₃ / a₃ ≤ Real.log (d : ℝ))
    (hMid : 8 * steepNetMiddleConstant / a₃ ≤ Real.rpow (d : ℝ) (3 / 2))
    (hHigh : 16 * steepNetHighConstant / (a₃ * C) ≤ Real.rpow (d : ℝ) (3 / 4)) :
    ((steepNetCountBound n d (thirdSteepScale n a₃) (Real.rpow (d : ℝ) (3 / 2)) *
      steepNetGridCount d (Real.rpow (d : ℝ) (3 / 2)) : ℕ) : ℝ) ≤
        Real.exp (7 * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ)) := by
  have hDimension := source_kernel_dimension_twice_degree h
  have hn := hDimension.1
  have hd := hDimension.2.1
  have hdn : d ≤ n := by omega
  have hLogN : 1 ≤ Real.log (n : ℝ) := hLog.trans
    (Real.log_le_log (by exact_mod_cast hd : (0 : ℝ) < d) (by exact_mod_cast hdn : (d : ℝ) ≤ n))
  have hFirst := firstSteepScale_pos hn hd
  have hThird := thirdSteepScale_bounds ha hSize
  have hN : a₃ * (n : ℝ) ≤ 2 * thirdSteepScale n a₃ := by linarith [hThird.2.1]
  have hCap : 1 ≤ Real.rpow (d : ℝ) (3 / 2) := Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hPrev : ((thirdSteepScale n a₃ - 1 : ℕ) : ℝ) ≤ a₃ * n :=
    (by exact_mod_cast (Nat.sub_le (thirdSteepScale n a₃) 1) :
      ((thirdSteepScale n a₃ - 1 : ℕ) : ℝ) ≤ thirdSteepScale n a₃).trans hThird.2.2
  apply (steep_net_count_entropy_bound hd (by have hp := h.stride_pos; omega : 1 ≤ steepStride d)
    hFirst hThird.1 ha haOne hPrev).trans
  apply Real.exp_le_exp.mpr
  have hBudget := steep_net_entropy_budget (next := thirdSteepScale n a₃) (t := a₃)
    hn hd hdn hLog hLogN
    (by have hp := h.stride_pos; omega : 1 ≤ steepStride d) hFirst h.dimension_root hCubic
      hCap (le_refl _) (steepNetGridCount_log_base_power hd)
  have hSupportCost := steep_net_T2_support_absorbed ha haOne hN hSupport
  have hMiddle := steep_net_T2_middle_absorbed hd ha hN hMid (by linarith : 0 ≤ Real.log (d : ℝ))
  have hHighBudget := steep_net_T2_high_absorbed hd ha hC hN hLower (by linarith : 0 ≤ Real.log (n : ℝ)) hHigh hLog
  have hBaseCost : (thirdSteepScale n a₃ : ℝ) * (Real.log 121 + 6 * Real.log (d : ℝ)) ≤
      (25 / 4 : ℝ) * (thirdSteepScale n a₃ : ℝ) * Real.log (d : ℝ) := by
    have hScaled := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg (thirdSteepScale n a₃) : (0 : ℝ) ≤ thirdSteepScale n a₃)
    linarith
  exact hBudget.trans (by linarith)

end CircularLaw
