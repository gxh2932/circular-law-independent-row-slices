import CircularLaw.GaussianForbiddenComparisons
import CircularLaw.SourceStartingRank

/-!
# Uniform parameter ranges for the manuscript Gaussian argument

The literal codimension interval gives the normal dimension and copy-count
ranges needed by uniform non-flatness. The standing logarithmic degree
lower bound makes the inverse codimension ratio dominate log(n), which
supplies the coordinate comparison. Thresholds are uniform in d and L.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_log_codimension_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 288 / Real.rpow (n : ℝ) (1 / 4))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) 288 /
      Real.rpow (n : ℝ) (1 / 4)) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow, Function.comp_apply] using
      ((isLittleO_log_rpow_rpow_atTop (288 : ℝ) (s := 1 / 4) (by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hNat (n : ℕ) : Real.rpow (Real.log (n : ℝ)) 288 = (Real.log (n : ℝ)) ^ (288 : ℕ) := by
    change (Real.log (n : ℝ)) ^ ((288 : ℕ) : ℝ) = (Real.log (n : ℝ)) ^ (288 : ℕ)
    exact Real.rpow_natCast _ _
  simpa only [hNat] using h

theorem eventually_gaussian_codimension_bounds (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d L : ℕ, Real.log (n : ℝ) ≤ d →
      (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L →
      (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 →
      64 ≤ n ∧ B ≤ (L : ℝ) ∧ 0 < L ∧ L ≤ n ∧ Real.sqrt n ≤ (L : ℝ) ∧
      2 * (n : ℝ) / L ≤ Real.rpow (n : ℝ) (1 / 4) ∧
      Real.log (n : ℝ) ≤ (n : ℝ) / L ∧ 12288 ≤ (n : ℝ) / L := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 64, hLog.eventually_ge_atTop 12288,
    eventually_degree_real_power_lower (by norm_num : (0 : ℝ) < 3 / 4) B,
    gaussian_log_codimension_ratio_tendsto_zero.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hLogLarge hPowerLarge hRatio
  intro d L hDegree hLower hUpper
  change 12288 ≤ Real.log (n : ℝ) at hLogLarge
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : (0 : ℝ) < n := by linarith
  have hLogOne : (1 : ℝ) ≤ Real.log n := by linarith
  have hLogPos : 0 < Real.log (n : ℝ) := by linarith
  have hLogPower : 0 < (Real.log (n : ℝ)) ^ 288 := pow_pos hLogPos _
  have hQuarter : 0 < Real.rpow (n : ℝ) (1 / 4) := Real.rpow_pos_of_pos hnPos _
  have hSmall : 2 * (Real.log (n : ℝ)) ^ 288 ≤ Real.rpow (n : ℝ) (1 / 4) := by
    have h := (div_lt_iff₀ hQuarter).mp hRatio
    linarith
  have hLPosR : (0 : ℝ) < L := (div_pos hnPos hLogPower).trans_le hLower
  have hLPos : 0 < L := by exact_mod_cast hLPosR
  have hRatioBound : (n : ℝ) / L ≤ (Real.log (n : ℝ)) ^ 288 := by
    apply (div_le_iff₀ hLPosR).mpr
    have h := (div_le_iff₀ hLogPower).mp hLower
    nlinarith
  have hCopy : 2 * (n : ℝ) / L ≤ Real.rpow (n : ℝ) (1 / 4) := by
    have h := mul_le_mul_of_nonneg_left hRatioBound (by norm_num : (0 : ℝ) ≤ 2)
    convert h.trans hSmall using 1
    ring
  have hPowerIdentity : Real.rpow (n : ℝ) (3 / 4) * Real.rpow (n : ℝ) (1 / 4) = n := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hnPos, show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hThreeQuarter : Real.rpow (n : ℝ) (3 / 4) ≤ (L : ℝ) := by
    apply le_trans _ hLower
    apply (le_div_iff₀ hLogPower).mpr
    have h := mul_le_mul_of_nonneg_left
      (by linarith : (Real.log (n : ℝ)) ^ 288 ≤ Real.rpow (n : ℝ) (1 / 4))
      (Real.rpow_pos_of_pos hnPos (3 / 4)).le
    simp only [Real.rpow_eq_pow] at h hPowerIdentity ⊢
    rw [hPowerIdentity] at h
    exact h
  have hSqrt : Real.sqrt n ≤ (L : ℝ) := by
    apply le_trans _ hThreeQuarter
    simpa only [Real.rpow_eq_pow, Real.sqrt_eq_rpow] using
      Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  have hdOne : (1 : ℝ) ≤ d := hLogOne.trans hDegree
  have hdCubeOne : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdOne
  have hLnR : (L : ℝ) ≤ n := hUpper.trans (div_le_self hnPos.le hdCubeOne)
  have hLn : L ≤ n := by exact_mod_cast hLnR
  have hdCube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    have hSq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hdOne
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ d) (sub_nonneg.mpr hSq)
    nlinarith
  have hDegreeRatio : (d : ℝ) ^ 3 ≤ (n : ℝ) / L := by
    apply (le_div_iff₀ hLPosR).mpr
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 3)).mp hUpper
    nlinarith
  have hLogRatio := hDegree.trans (hdCube.trans hDegreeRatio)
  exact ⟨hn, hPowerLarge.trans hThreeQuarter, hLPos, hLn, hSqrt, hCopy,
    hLogRatio, hLogLarge.trans hLogRatio⟩

theorem sourceNormalRank_small_nonflat {a : ℝ} (ha : 0 < a) (haSmall : a ≤ 1 / 2048)
    {L : ℕ} (hL : 2 / a ≤ (L : ℝ)) :
    0 < sourceNormalRank a L ∧ sourceNormalRank a L ≤ L / 2048 := by
  have hAL : (2 : ℝ) ≤ a * (L : ℝ) := by
    have h := (div_le_iff₀ ha).mp hL
    nlinarith
  have hFloor := Nat.lt_floor_add_one (a * (L : ℝ))
  have hqR : (0 : ℝ) < sourceNormalRank a L := by
    change (0 : ℝ) < (⌊a * (L : ℝ)⌋₊ : ℝ)
    linarith
  have hq : 0 < sourceNormalRank a L := by exact_mod_cast hqR
  have hFloorUpper := Nat.floor_le (mul_nonneg ha.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L))
  have hScaled := mul_le_mul_of_nonneg_right haSmall (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hqScaled : 2048 * (sourceNormalRank a L : ℝ) ≤ L := by
    change 2048 * (⌊a * (L : ℝ)⌋₊ : ℝ) ≤ L
    linarith
  have hqNat : 2048 * sourceNormalRank a L ≤ L := by exact_mod_cast hqScaled
  exact ⟨hq, by omega⟩

theorem eventually_sourceGaussian_ranges_uniform {a C : ℝ}
    (ha : 0 < a) (haSmall : a ≤ 1 / 2048) (hC : 1 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L →
        (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 →
        64 ≤ n ∧ 131072 ≤ L ∧ L ≤ n ∧ Real.sqrt n ≤ (L : ℝ) ∧
        2 * (n : ℝ) / L ≤ Real.rpow (n : ℝ) (1 / 4) ∧
        Real.log (n : ℝ) ≤ (n : ℝ) / L ∧ 12288 ≤ (n : ℝ) / L ∧
        0 < sourceNormalRank a L ∧ sourceNormalRank a L ≤ L / 2048 := by
  filter_upwards [eventually_gaussian_codimension_bounds (max 131072 (2 / a)),
    eventually_ge_atTop 64] with n hRanges hn
  intro d hBand L hLower hUpper
  have hLogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hDegree : Real.log (n : ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_right hC hLogNonneg
    linarith [hBand.1]
  obtain ⟨hn, hL, hLPos, hLn, hSqrt, hCopies, hLogRatio, hRatioLarge⟩ :=
    hRanges d L hDegree hLower hUpper
  have hLLargeR : (131072 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLLarge : 131072 ≤ L := by exact_mod_cast hLLargeR
  have hRank := sourceNormalRank_small_nonflat ha haSmall ((le_max_right _ _).trans hL)
  exact ⟨hn, hLLarge, hLn, hSqrt, hCopies, hLogRatio, hRatioLarge, hRank.1, hRank.2⟩

end CircularLaw
