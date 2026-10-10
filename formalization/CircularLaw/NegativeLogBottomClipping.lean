import CircularLaw.BottomLogGeometry

/-!
# Negative-log clipping error supported on a bottom interval

When every positive prefix value has negative logarithm at most T, the
full clipping error is nonnegative and bounded by the bottom logarithmic
sum. This implication uses the literal finite means and bottom indices.
-/

noncomputable section
open Classical
open scoped NNReal BigOperators

namespace CircularLaw

theorem empirical_negative_log_clipping_bounds {n : ℕ} (s : Fin n → ℝ≥0)
    (hPos : ∀ j, 0 < s j) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ empiricalNonnegativeMean s hermitizationNegativeLog -
      empiricalNonnegativeMean s (clippedNegativeLog T) := by
  unfold empiricalNonnegativeMean
  rw [← finiteMean_sub]
  apply finiteMean_nonneg
  intro j
  rw [clippedNegativeLog_eq_min hT (hPos j)]
  exact sub_nonneg.mpr (min_le_left _ _)

theorem empirical_negative_log_clipping_le_bottom {n R : ℕ} (s : Fin n → ℝ≥0)
    (hPos : ∀ j, 0 < s j) {T : ℝ} (hT : 0 ≤ T)
    (hPrefix : ∀ j, j ∉ bottomLogIndices n R → hermitizationNegativeLog (s j) ≤ T) :
    empiricalNonnegativeMean s hermitizationNegativeLog -
      empiricalNonnegativeMean s (clippedNegativeLog T) ≤ empiricalBottomNegativeLog s R := by
  have hPoint (j : Fin n) : hermitizationNegativeLog (s j) - clippedNegativeLog T (s j) ≤
      if j ∈ bottomLogIndices n R then hermitizationNegativeLog (s j) else 0 := by
    rw [clippedNegativeLog_eq_min hT (hPos j)]
    by_cases hj : j ∈ bottomLogIndices n R
    · rw [if_pos hj]
      exact sub_le_self _ (le_min (le_max_right _ _) hT)
    · rw [if_neg hj, min_eq_left (hPrefix j hj), sub_self]
  unfold empiricalNonnegativeMean empiricalBottomNegativeLog
  rw [← finiteMean_sub]
  unfold finiteMean
  simp only [Fintype.card_fin]
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hPoint j)
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] at hSum
  exact div_le_div_of_nonneg_right hSum (Nat.cast_nonneg n)

end CircularLaw
