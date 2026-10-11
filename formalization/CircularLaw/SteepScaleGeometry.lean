import CircularLaw.KernelCodimension

/-!
# Finite geometry of the actual source steep scales

Both source codimensions give the minimum size and retained-row bounds.
The least starting exponent precedes the final exponent, and every
geometric or terminal pair has the required size, ratio and density.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem steep_start_precedes_end {p d L n1 : ℕ} (hp : 1 < p) (hd : 0 < d)
    (hThreshold : 1 < 20 * (L : ℝ) / d) (hSquare : p ^ 2 ≤ d) (hSize : 20 * L ≤ n1) :
    steepStartExponent p d L < steepEndExponent p n1 := by
  have hStart : 0 < steepStartExponent p d L := by
    by_contra h
    have hEq : steepStartExponent p d L = 0 := by omega
    have hLower := steepStartExponent_lower (d := d) (L := L) hp
    rw [hEq, Nat.pow_zero, Nat.cast_one] at hLower
    linarith
  have hUpper := steepStartExponent_upper hp hStart
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hSquareR : (p : ℝ) ^ 2 ≤ d := by exact_mod_cast hSquare
  have hNext : ((p ^ (steepStartExponent p d L + 1) : ℕ) : ℝ) <
      (p : ℝ) ^ 2 * (20 * (L : ℝ) / d) := by
    have h := mul_lt_mul_of_pos_left hUpper hpR
    rw [Nat.pow_succ, Nat.cast_mul]
    nlinarith
  have hFactor : (p : ℝ) ^ 2 * (20 * (L : ℝ) / d) ≤ 20 * L := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdR).mpr
    have h := mul_le_mul_of_nonneg_right hSquareR (by positivity : (0 : ℝ) ≤ 20 * L)
    nlinarith
  have hSizeR : (20 : ℝ) * L ≤ n1 := by exact_mod_cast hSize
  have hNextNat : p ^ (steepStartExponent p d L + 1) < n1 := by
    exact_mod_cast hNext.trans_le (hFactor.trans hSizeR)
  have hLog := Nat.le_log_of_pow_le hp (by omega :
    p ^ (steepStartExponent p d L + 1) ≤ n1 - 1)
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hLog

theorem codimension_first_scale_bound {n d L : ℕ} (hd : 20 ≤ d)
    (hn : 4 * d ^ 3 ≤ n) (hL : IsKernelCodimension n d L) :
    20 * L ≤ firstSteepScale n d := by
  have hdPos : 0 < d := by omega
  have hdR : (20 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := by positivity
  have hRootLe : Real.sqrt d ≤ (d : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg (d : ℝ)) (Nat.cast_nonneg d)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    nlinarith
  have hCube := mul_le_mul_of_nonneg_right hdR (sq_nonneg (d : ℝ))
  have hRootScaled := mul_le_mul_of_nonneg_left hRootLe (by positivity : (0 : ℝ) ≤ 20 * d)
  have hDen : (20 : ℝ) * d * Real.sqrt d ≤ (d : ℝ) ^ 3 := by nlinarith
  have hRatio : 20 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (n : ℝ) / ((d : ℝ) * Real.sqrt d) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 3)
      (by positivity : (0 : ℝ) < (d : ℝ) * Real.sqrt d)).mpr
    have hScaled := mul_le_mul_of_nonneg_left hDen (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have hBounds := kernelCodimension_bounds hdPos hn hL
  have hReal : (20 : ℝ) * L ≤ firstSteepScale n d := by
    calc
      _ ≤ 20 * ((n : ℝ) / (d : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hBounds.2 (by norm_num)
      _ = 20 * (n : ℝ) / (d : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) / ((d : ℝ) * Real.sqrt d) := hRatio
      _ ≤ _ := firstSteepScale_lower hdPos
  exact_mod_cast hReal

theorem source_steep_scale_conditions {n d L : ℕ} (hdLarge : 40000 ≤ d)
    (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (hp : 1 < steepStride d)
    (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5) :
    ∀ a ∈ sourceSteepScalePairs n d L, 0 < a.1 ∧ a.1 ≤ a.2 ∧ 100 * d * a.2 ≤ n ∧
      a.2 ≤ steepStride d * a.1 ∧ 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (d : ℝ) * a.1 := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPower := Nat.pow_le_pow_right hd (by decide : 3 ≤ 4)
  have hn3 : 4 * d ^ 3 ≤ n := (Nat.mul_le_mul_left 4 hPower).trans hn
  have hLLarge := kernelCodimension_large_lower hd hn hL
  have hThreshold : 1 < 20 * (L : ℝ) / d := by
    apply (lt_div_iff₀ hdR).mpr
    have hLReal : 2 * (d : ℝ) ≤ L := by exact_mod_cast hLLarge
    nlinarith
  have hSqrtLarge : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt hdR.le]
    exact_mod_cast hdLarge
  have hStrideRoot : (steepStride d : ℝ) ≤ Real.sqrt d := by nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hStrideSquare : (steepStride d) ^ 2 ≤ d := by
    have hSq := pow_le_pow_left₀ (Nat.cast_nonneg (steepStride d)) hStrideRoot 2
    rw [Real.sq_sqrt hdR.le] at hSq
    exact_mod_cast hSq
  have hSize := codimension_first_scale_bound (by omega : 20 ≤ d) hn3 hL
  have hStart := steep_start_precedes_end hp hd hThreshold hStrideSquare hSize
  have hn1 : 1 < firstSteepScale n d := by omega
  have hEnd := steepEndExponent_bounds hp hn1
  have hSmall := firstSteepScale_small hd hDimension hSqrtLarge
  have hStartDensity := (div_le_iff₀ hdR).mp (steepStartExponent_lower (d := d) (L := L) hp)
  have hLB := (kernelCodimension_bounds hd hn3 hL).1
  have hDensityL : 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ 20 * L := by
    calc
      _ = 20 * ((n : ℝ) / (2 * (d : ℝ) ^ 3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLB (by norm_num)
  intro a ha
  have hBounds := steepScalePairs_bounds hp (by omega : 0 < firstSteepScale n d) hStart hEnd.1 a ha
  have hSmallA : 100 * d * a.2 ≤ n :=
    (Nat.mul_le_mul_left (100 * d) hBounds.2.2.1).trans hSmall
  have hPowerSize : (((steepStride d) ^ steepStartExponent (steepStride d) d L : ℕ) : ℝ) ≤ a.1 := by
    exact_mod_cast hBounds.2.2.2.2
  have hScaled := mul_le_mul_of_nonneg_left hPowerSize hdR.le
  have hDensity : 10 * (n : ℝ) / (d : ℝ) ^ 3 ≤ (d : ℝ) * a.1 := by
    nlinarith
  exact ⟨hBounds.1, hBounds.2.1, hSmallA, hBounds.2.2.2.1, hDensity⟩

theorem source_steep_scale_card_le {n d L : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hSmall : 100 * d * firstSteepScale n d ≤ n) :
    (sourceSteepScalePairs n d L).card ≤ n := by
  have h := steepScalePairs_card_le (p := steepStride d)
    (r0 := steepStartExponent (steepStride d) d L) (firstSteepScale_pos hn hd)
  have hScale : firstSteepScale n d ≤ n := by nlinarith
  exact h.trans hScale

end CircularLaw
