import CircularLaw.RegularizedDistanceConcentration
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Pointwise logarithmic comparison on good and bad distance events

The good event has both distances at least half their reference mean.
The exceptional event uses their literal interval `[eta,U]` instead.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem log_sub_le_distance_div_lower {a x y : ℝ} (ha : 0 < a)
    (hay : a ≤ y) (hyx : y ≤ x) :
    Real.log x - Real.log y ≤ (x - y) / a := by
  have hy : 0 < y := ha.trans_le hay
  have hx : 0 < x := hy.trans_le hyx
  calc
    _ = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
    _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
    _ = (x - y) / y := by field_simp [hy.ne']
    _ ≤ (x - y) / a := div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) ha hay

theorem abs_log_sub_log_le_distance_div_lower {a x y : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hay : a ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / a := by
  by_cases h : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (ha.trans_le hay) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_le_distance_div_lower ha hay h
  · rw [abs_sub_comm (Real.log x), abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (ha.trans_le hax) (le_of_not_ge h))),
      abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    exact log_sub_le_distance_div_lower ha hax (le_of_not_ge h)

theorem abs_log_sub_log_le_range {η U x y : ℝ} (hη : 0 < η)
    (hx : η ≤ x) (hy : η ≤ y) (hxU : x ≤ U) (hyU : y ≤ U) :
    |Real.log x - Real.log y| ≤ Real.log (U / η) := by
  have hU : 0 < U := (hη.trans_le hx).trans_le hxU
  have hLogx := Real.log_le_log hη hx
  have hLogy := Real.log_le_log hη hy
  have hLogUx := Real.log_le_log (hη.trans_le hx) hxU
  have hLogUy := Real.log_le_log (hη.trans_le hy) hyU
  rw [Real.log_div hU.ne' hη.ne']
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_comparison_good_bad_pointwise {η U x y m : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hx : η ≤ x) (hy : η ≤ y) (hxU : x ≤ U) (hyU : y ≤ U) :
    |Real.log x - Real.log y| ≤
      (2 / m) * (|x - m| + |y - m|) +
        if x < m / 2 ∨ y < m / 2 then Real.log (U / η) else 0 := by
  by_cases hBad : x < m / 2 ∨ y < m / 2
  · rw [if_pos hBad]
    have hNonneg : 0 ≤ (2 / m) * (|x - m| + |y - m|) := by positivity
    linarith [abs_log_sub_log_le_range hη hx hy hxU hyU]
  · rw [if_neg hBad, add_zero]
    have hxm : m / 2 ≤ x := le_of_not_gt (fun h => hBad (Or.inl h))
    have hym : m / 2 ≤ y := le_of_not_gt (fun h => hBad (Or.inr h))
    have hTriangle : |x - y| ≤ |x - m| + |y - m| := by
      simpa only [sub_add_sub_cancel, abs_sub_comm] using abs_add_le (x - m) (m - y)
    calc
      _ ≤ |x - y| / (m / 2) := abs_log_sub_log_le_distance_div_lower (by linarith) hxm hym
      _ = (2 / m) * |x - y| := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hTriangle (by positivity)

end CircularLaw
