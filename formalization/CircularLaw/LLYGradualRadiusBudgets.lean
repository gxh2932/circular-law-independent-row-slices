import CircularLaw.LLYSteepGeometry
import CircularLaw.AlmostConstantRanks

/-!
# The gradual radius automatically fits the minimum-value threshold

The lower bound on the proved norm constant includes the dense rank-one
case. No additional image-threshold comparison is needed at rho²/n.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_gradual_norm_constant_ge_four_sqrt {n d r k₁ : ℕ} (hd : 0 < d) :
    4 * Real.sqrt n ≤ llyGradualNormConstant n d r k₁ := by
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hFirst : (1 : ℝ) ≤ if k₁ = 1 then 1 else (6 * (d : ℝ)) ^ (r + 1) := by
    split_ifs
    · exact le_refl _
    · exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 6 * d)
  have hDegree := Real.one_le_rpow hdOne (by norm_num : (0 : ℝ) ≤ 3 / 4)
  unfold llyGradualNormConstant
  calc
    _ = 4 * Real.sqrt n * 1 * 1 := by ring
    _ ≤ 4 * Real.sqrt n * (if k₁ = 1 then 1 else (6 * (d : ℝ)) ^ (r + 1)) *
        (d : ℝ) ^ (3 / 4 : ℝ) := by gcongr

theorem lly_gradual_norm_constant_ge_four {n d r k₁ : ℕ} (hn : 0 < n) (hd : 0 < d) :
    4 ≤ llyGradualNormConstant n d r k₁ := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hRoot : 1 ≤ Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnOne
  exact (show (4 : ℝ) ≤ 4 * Real.sqrt n by linarith).trans (lly_gradual_norm_constant_ge_four_sqrt hd)

theorem lly_gradual_radius_smallest_threshold {n d r k₁ : ℕ} (hn : 0 < n) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁)) :
    (ρ / Real.sqrt n) * ρ / Real.sqrt n <
      2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) := by
  have hB := lly_gradual_norm_constant_pos hn hd (r := r) (k₁ := k₁)
  have hBGe := lly_gradual_norm_constant_ge_four hn hd (r := r) (k₁ := k₁)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hRootOne : 1 ≤ Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnOne
  have hQuotient : ρ / Real.sqrt n ≤ 1 / (5 * llyGradualNormConstant n d r k₁) := by
    apply (div_le_iff₀ hRoot).mpr
    convert hRadius using 1
    ring
  have hSquare := pow_le_pow_left₀ (div_nonneg hρ hRoot.le) hQuotient 2
  have hProduct : 1 ≤ (d : ℝ) * Real.sqrt n := by nlinarith only [hdOne, hRootOne]
  have hStrict : (1 / (5 * llyGradualNormConstant n d r k₁)) ^ 2 <
      2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) := by
    apply (lt_div_iff₀ (by positivity : 0 < 25 * llyGradualNormConstant n d r k₁)).mpr
    have hCancel : (1 / (5 * llyGradualNormConstant n d r k₁)) ^ 2 *
        (25 * llyGradualNormConstant n d r k₁) = 1 / llyGradualNormConstant n d r k₁ := by
      field_simp
      ring
    rw [hCancel]
    have hInv : 1 / llyGradualNormConstant n d r k₁ ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hBGe
    nlinarith only [hInv, hProduct]
  exact (show (ρ / Real.sqrt n) * ρ / Real.sqrt n ≤
      (1 / (5 * llyGradualNormConstant n d r k₁)) ^ 2 by
    convert hSquare using 1
    ring).trans_lt hStrict

theorem lly_first_rank_column_budget {n d k₁ : ℕ} (hd : 0 < d)
    (hk₁ : k₁ ≤ almostConstantRank n d) : (d : ℝ) * k₁ ≤ (n : ℝ) / 9 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRank : (k₁ : ℝ) ≤ almostConstantRank n d := by exact_mod_cast hk₁
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mp
    (hRank.trans (almostConstantRank_upper hd))
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) n]

end CircularLaw
