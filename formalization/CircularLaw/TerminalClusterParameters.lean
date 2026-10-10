import CircularLaw.StructuralBranchEnergy

/-!
# The literal terminal cluster fraction and floor loss

The two allowed codimensions give a factor-two comparison for the
cluster fraction. The source terminal floor is retained throughout.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem structuralClusterFraction_inverse_ratio (n L : ℕ) :
    structuralClusterFraction n L = Real.rpow ((n : ℝ) / L) (-(1 / 576)) := by
  unfold structuralClusterFraction
  simp only [Real.rpow_eq_pow]
  rw [show (L : ℝ) / n = ((n : ℝ) / L)⁻¹ by simp only [inv_div]]
  rw [Real.rpow_neg_eq_inv_rpow]

theorem structuralClusterFraction_degree_bounds {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    (1 / 2) * Real.rpow (d : ℝ) (-(1 / 192)) ≤ structuralClusterFraction n L ∧
      structuralClusterFraction n L ≤ Real.rpow (d : ℝ) (-(1 / 192)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hBounds := kernelCodimension_inverse_ratio_bounds hd hn hL
  have hRatio : 0 < (n : ℝ) / L := (pow_pos hdR 3).trans_le hBounds.1
  have hCube : Real.rpow ((d : ℝ) ^ 3) (-(1 / 576)) = Real.rpow (d : ℝ) (-(1 / 192)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (d : ℝ) 3, ← Real.rpow_mul hdR.le]
    norm_num
  have hTwo : (1 / 2 : ℝ) ≤ Real.rpow 2 (-(1 / 576)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-1 : ℝ) ≤ -(1 / 576))
    simpa only [Real.rpow_neg_one, invOf_eq_inv, one_div] using h
  rw [structuralClusterFraction_inverse_ratio]
  constructor
  · calc
      _ ≤ Real.rpow 2 (-(1 / 576)) * Real.rpow (d : ℝ) (-(1 / 192)) :=
        mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hdR.le _)
      _ = Real.rpow (2 * (d : ℝ) ^ 3) (-(1 / 576)) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        exact congrArg (fun t => (2 : ℝ) ^ (-(1 / 576) : ℝ) * t) hCube.symm
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hRatio hBounds.2 (by norm_num)
  · exact hCube ▸ Real.rpow_le_rpow_of_nonpos (pow_pos hdR 3) hBounds.1 (by norm_num)

theorem structuralClusterFraction_pos {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) : 0 < structuralClusterFraction n L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower := Real.rpow_pos_of_pos hdR (-(1 / 192))
  have hBounds := (structuralClusterFraction_degree_bounds hd hn hL).1
  simp only [Real.rpow_eq_pow] at hBounds
  linarith

theorem structuralClusterFraction_log_lower {n d L : ℕ} (hd : 0 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    -Real.log 2 - (1 / 192) * Real.log d ≤ Real.log (structuralClusterFraction n L) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower := Real.rpow_pos_of_pos hdR (-(1 / 192))
  have h := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hPower)
    (structuralClusterFraction_degree_bounds hd hn hL).1
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hPower.ne', Real.log_rpow hdR,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one] at h
  linarith

theorem structuralTerminalExponent_floor_lower (n d L : ℕ) :
    structuralGrowth n L / Real.log d - 1 ≤ (structuralTerminalExponent n d L : ℝ) := by
  have h := Nat.lt_floor_add_one (structuralGrowth n L / Real.log d)
  unfold structuralTerminalExponent
  linarith

theorem structuralTerminalExponent_margin_lower {n d L : ℕ} (hd : 1 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (hDegree : 20 * Real.log d ≤ Real.rpow (d : ℝ) (1 / 96)) :
    8 ≤ structuralTerminalExponent n d L ∧
      Real.rpow (d : ℝ) (1 / 96) / (2 * Real.log d) ≤
        (structuralTerminalExponent n d L : ℝ) - 4 := by
  have hLog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd)
  have hGrowth := (structuralGrowth_degree_bounds (by omega) hn hL).1
  have hFloor := structuralTerminalExponent_floor_lower n d L
  have hRatio : 20 ≤ structuralGrowth n L / Real.log d :=
    (le_div_iff₀ hLog).mpr (hDegree.trans hGrowth)
  have hV : (8 : ℝ) ≤ structuralTerminalExponent n d L := by linarith
  refine ⟨by exact_mod_cast hV, ?_⟩
  have hLower : Real.rpow (d : ℝ) (1 / 96) / Real.log d ≤
      structuralGrowth n L / Real.log d := div_le_div_of_nonneg_right hGrowth hLog.le
  have hTwenty := (le_div_iff₀ hLog).mpr hDegree
  calc
    _ = (Real.rpow (d : ℝ) (1 / 96) / Real.log d) / 2 := by ring
    _ ≤ _ := by linarith

theorem structuralCluster_terminal_margin_lower {n d L : ℕ} (hd : 1 < d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L)
    (hDegree : 20 * Real.log d ≤ Real.rpow (d : ℝ) (1 / 96)) :
    Real.rpow (d : ℝ) (1 / 192) / (4 * Real.log d) ≤
      structuralClusterFraction n L * ((structuralTerminalExponent n d L : ℝ) - 4) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hLog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd)
  have hMargin := (structuralTerminalExponent_margin_lower hd hn hL hDegree).2
  have hFraction := (structuralClusterFraction_degree_bounds (by omega) hn hL).1
  have hProduct : Real.rpow (d : ℝ) (-(1 / 192)) * Real.rpow (d : ℝ) (1 / 96) =
      Real.rpow (d : ℝ) (1 / 192) := by
    rw [positive_degree_power_mul (by omega), show -(1 / 192 : ℝ) + 1 / 96 = 1 / 192 by norm_num]
  calc
    _ = ((1 / 2) * Real.rpow (d : ℝ) (-(1 / 192))) *
        (Real.rpow (d : ℝ) (1 / 96) / (2 * Real.log d)) := by rw [← hProduct]; ring
    _ ≤ _ := mul_le_mul hFraction hMargin
      (div_nonneg (Real.rpow_nonneg hdR.le _) (mul_nonneg (by norm_num) hLog.le))
      (structuralClusterFraction_pos (by omega) hn hL).le

end CircularLaw
