import CircularLaw.SteepScaleGeometry

/-!
# The source starting rank and normal rank

Minimality of `r0` gives the strict upper bound on `p^r0`. The literal
floor `qL=floor(a*L)` is large enough under the finite conditions below;
the next module discharges them in the source degree band.
-/

noncomputable section
open Classical

namespace CircularLaw

def sourceNormalRank (a : ℝ) (L : ℕ) : ℕ := ⌊a * (L : ℝ)⌋₊

theorem source_starting_rank_bounds {n d L : ℕ} (hdLarge : 40000 ≤ d)
    (hn : 4 * d ^ 4 ≤ n) (hDimension : (d : ℝ) * Real.sqrt d ≤ n)
    (hL : IsKernelCodimension n d L) (hp : 1 < steepStride d)
    (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5) :
    0 < steepStartExponent (steepStride d) d L ∧
      (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ firstSteepScale n d ∧
      firstSteepScale n d ≤ n ∧
      4 * (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ n ∧
      steepStartExponent (steepStride d) d L <
        steepEndExponent (steepStride d) (firstSteepScale n d) := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn3 : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hd (by decide : 3 ≤ 4))).trans hn
  have hLLarge := kernelCodimension_large_lower hd hn hL
  have hThreshold : 1 < 20 * (L : ℝ) / d := by
    apply (lt_div_iff₀ hdR).mpr
    have hLReal : 2 * (d : ℝ) ≤ L := by exact_mod_cast hLLarge
    nlinarith
  have hStartPos : 0 < steepStartExponent (steepStride d) d L := by
    by_contra h
    have hEq : steepStartExponent (steepStride d) d L = 0 := by omega
    have hLower := steepStartExponent_lower (d := d) (L := L) hp
    rw [hEq, pow_zero, Nat.cast_one] at hLower
    linarith
  have hRoot : (200 : ℝ) ≤ Real.sqrt d := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg (d : ℝ))).mp
    rw [Real.sq_sqrt hdR.le]
    exact_mod_cast hdLarge
  have hStrideRoot : (steepStride d : ℝ) ≤ Real.sqrt d := by nlinarith
  have hSquare : (steepStride d) ^ 2 ≤ d := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (steepStride d)) hStrideRoot 2
    rw [Real.sq_sqrt hdR.le] at h
    exact_mod_cast h
  have hSize := codimension_first_scale_bound (by omega : 20 ≤ d) hn3 hL
  have hBefore := steep_start_precedes_end hp hd hThreshold hSquare hSize
  have hn1 : 1 < firstSteepScale n d := by omega
  have hPower := Nat.pow_le_pow_right (by omega : 0 < steepStride d) hBefore.le
  have hRank : (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ firstSteepScale n d :=
    hPower.trans (steepEndExponent_bounds hp hn1).1.le
  have hSmall := firstSteepScale_small hd hDimension hRoot
  have hFirst : firstSteepScale n d ≤ n := by nlinarith
  have hFour : 4 * (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ n := by
    nlinarith
  exact ⟨hStartPos, hRank, hFirst, hFour, hBefore⟩

theorem source_starting_rank_le_normal {d L : ℕ} {a : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hp : 1 < steepStride d) (hStart : 0 < steepStartExponent (steepStride d) d L)
    (hStride : (steepStride d : ℝ) ≤ Real.sqrt d / 5)
    (hRoot : 8 / a ≤ Real.sqrt d) (hSize : 2 ≤ a * (L : ℝ)) :
    (steepStride d) ^ steepStartExponent (steepStride d) d L ≤ sourceNormalRank a L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRootPos := Real.sqrt_pos.mpr hdR
  have hUpper := steepStartExponent_upper hp hStart
  have hStrideUpper : (steepStride d : ℝ) * (20 * (L : ℝ) / d) ≤
      4 * (L : ℝ) / Real.sqrt d := by
    calc
      _ ≤ (Real.sqrt d / 5) * (20 * (L : ℝ) / d) :=
        mul_le_mul_of_nonneg_right hStride (by positivity)
      _ = _ := by
        rw [show Real.sqrt (d : ℝ) / 5 * (20 * (L : ℝ) / d) =
          (4 * (L : ℝ) * Real.sqrt d) / d by ring]
        apply (div_eq_div_iff hdR.ne' hRootPos.ne').mpr
        have hSq := congrArg (fun b : ℝ => 4 * (L : ℝ) * b) (Real.sq_sqrt hdR.le)
        nlinarith
  have hCoefficient : 4 / Real.sqrt d ≤ a / 2 := by
    have h := (div_le_iff₀ ha).mp hRoot
    apply (div_le_iff₀ hRootPos).mpr
    linarith
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hRankReal : (((steepStride d) ^ steepStartExponent (steepStride d) d L : ℕ) : ℝ) <
      a * (L : ℝ) / 2 := by
    apply hUpper.trans_le
    apply hStrideUpper.trans
    convert hScaled using 1 <;> ring
  have hFloor := Nat.lt_floor_add_one (a * (L : ℝ))
  have hReal : (((steepStride d) ^ steepStartExponent (steepStride d) d L : ℕ) : ℝ) ≤
      sourceNormalRank a L := by
    change _ ≤ (⌊a * (L : ℝ)⌋₊ : ℝ)
    linarith
  exact_mod_cast hReal

theorem sourceNormalRank_le_dimension {n L : ℕ} {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1)
    (hL : L ≤ n) : sourceNormalRank a L ≤ n := by
  have hFloor := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg L : (0 : ℝ) ≤ L))
  have hScaled := mul_le_mul_of_nonneg_right haOne (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hLn : (L : ℝ) ≤ n := by exact_mod_cast hL
  have hReal : (sourceNormalRank a L : ℝ) ≤ n := by
    change (⌊a * (L : ℝ)⌋₊ : ℝ) ≤ n
    linarith
  exact_mod_cast hReal

end CircularLaw
