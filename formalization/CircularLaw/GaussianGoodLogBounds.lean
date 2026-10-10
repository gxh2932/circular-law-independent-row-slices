import CircularLaw.GaussianSmallestPolynomial
import CircularLaw.GaussianUniformQuantiles
import CircularLaw.BottomRankLogEntropy

/-!
# Deterministic logarithmic bounds outside actual Gaussian bad events

The lowest 2*sqrt(n) ranks contribute at most 4*sqrt(n)*log(n).
All remaining ranks obey the checked logarithmic rank bound. Summing
the bottom R ranks gives the entropy term R*(log(16*n/R)+1).
-/

noncomputable section
open Classical
open scoped NNReal BigOperators

namespace CircularLaw

theorem gaussian_good_polynomial_singular_pos {n : ℕ} (hn : 0 < n) (z : ℂ)
    (x : GaussianSquareSample n) (hGood : x ∉ gaussianSmallestPolynomialBad z n) (j : Fin n) :
    0 < orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (inv_pos.mpr (sq_pos_of_pos hnR)).trans_le
    (le_of_not_gt (fun h => hGood ⟨j, h⟩))

theorem gaussian_good_polynomial_negative_log_bound {n : ℕ} (hn : 0 < n) (z : ℂ)
    (x : GaussianSquareSample n) (hGood : x ∉ gaussianSmallestPolynomialBad z n) (j : Fin n) :
    hermitizationNegativeLog
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j) ≤ 2 * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLower : ((n : ℝ) ^ 2)⁻¹ ≤
      orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j :=
    le_of_not_gt (fun h => hGood ⟨j, h⟩)
  have hLog := Real.log_le_log (inv_pos.mpr (sq_pos_of_pos hnR)) hLower
  rw [Real.log_inv, Real.log_pow] at hLog
  norm_num only [Nat.cast_ofNat] at hLog
  change max (-Real.log (orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j)) 0 ≤ _
  apply max_le
  · linarith
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn))

theorem gaussian_rank_log_nonneg {n : ℕ} (hn : 0 < n) (j : Fin n) :
    0 ≤ Real.log (16 * (n : ℝ) / ((n - j.val : ℕ) : ℝ)) := by
  have hRank : (0 : ℝ) < (n - j.val : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt j.isLt
  apply Real.log_nonneg
  apply (le_div_iff₀ hRank).mpr
  have hLe : ((n - j.val : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n j.val
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem gaussian_good_uniform_negative_log_rank_bound {n : ℕ} (hn : 2 ≤ Nat.sqrt n)
    (z : ℂ) (x : GaussianSquareSample n) (hGood : x ∉ gaussianUniformQuantileBad z n)
    (j : Fin n) (hRank : 2 * Nat.sqrt n < n - j.val) :
    hermitizationNegativeLog
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j) ≤
        Real.log (16 * (n : ℝ) / ((n - j.val : ℕ) : ℝ)) := by
  have hnPos : 0 < n := (Nat.zero_le j.val).trans_lt j.isLt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hR : (0 : ℝ) < (n - j.val : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt j.isLt
  have hLog := Real.log_le_log (div_pos hR (by positivity))
    (gaussian_good_uniform_quantile_rank_lower hn z x hGood j hRank)
  rw [Real.log_div hR.ne' (by positivity : 16 * (n : ℝ) ≠ 0)] at hLog
  change max (-Real.log (orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j)) 0 ≤ _
  apply max_le
  · rw [Real.log_div (by positivity : 16 * (n : ℝ) ≠ 0) hR.ne']
    linarith
  · exact gaussian_rank_log_nonneg hnPos j

theorem bottom_rank_indicator_sum_le {n R q : ℕ} (P : ℝ) (hP : 0 ≤ P) :
    (∑ j ∈ bottomLogIndices n R, if n - j.val ≤ q then P else 0) ≤ (q : ℝ) * P := by
  let S := (bottomLogIndices n R).filter (fun j => n - j.val ≤ q)
  have hSubset : S ⊆ bottomLogIndices n q := by
    intro j hj
    have hRank := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hjn := j.isLt
    omega
  have hCard : (S.card : ℝ) ≤ q := by
    exact_mod_cast (Finset.card_le_card hSubset).trans (bottomLogIndices_card_le n q)
  rw [← Finset.sum_filter]
  change (∑ _j ∈ S, P) ≤ _
  simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hCard hP

theorem gaussian_good_bottom_negative_log_bound {n R : ℕ} (hn : 2 ≤ Nat.sqrt n)
    (hRn : R ≤ n) (z : ℂ) (x : GaussianSquareSample n)
    (hMin : x ∉ gaussianSmallestPolynomialBad z n)
    (hQuantile : x ∉ gaussianUniformQuantileBad z n) :
    empiricalBottomNegativeLog
      (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x)) R ≤
        (4 * (Nat.sqrt n : ℝ) * Real.log n) / n +
          ((R : ℝ) / n) * (Real.log (16 * (n : ℝ) / R) + 1) := by
  have hnPos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [hn0] at hn
  have hP : 0 ≤ 2 * Real.log (n : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hnPos))
  have hPoint (j : Fin n) :
      hermitizationNegativeLog (squareSingularValuesNNReal (normalizedShiftedGaussianMatrix z x) j) ≤
        (if n - j.val ≤ 2 * Nat.sqrt n then 2 * Real.log n else 0) +
          Real.log (16 * (n : ℝ) / ((n - j.val : ℕ) : ℝ)) := by
    by_cases hRank : n - j.val ≤ 2 * Nat.sqrt n
    · rw [if_pos hRank]
      exact (gaussian_good_polynomial_negative_log_bound hnPos z x hMin j).trans
        (le_add_of_nonneg_right (gaussian_rank_log_nonneg hnPos j))
    · rw [if_neg hRank, zero_add]
      exact gaussian_good_uniform_negative_log_rank_bound hn z x hQuantile j (lt_of_not_ge hRank)
  have hSum := Finset.sum_le_sum (s := bottomLogIndices n R) (fun j _ => hPoint j)
  rw [Finset.sum_add_distrib] at hSum
  have hBound := hSum.trans (add_le_add
    (bottom_rank_indicator_sum_le (n := n) (R := R) (q := 2 * Nat.sqrt n) _ hP)
    (bottom_rank_log_ratio_sum_bound hRn (by positivity : (0 : ℝ) < 16 * n)))
  have hMean := div_le_div_of_nonneg_right hBound (Nat.cast_nonneg n)
  convert hMean using 1
  push_cast
  ring

end CircularLaw
