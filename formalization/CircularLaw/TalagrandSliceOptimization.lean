import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# The scalar interpolation step in Talagrand's dimension induction

For each relative slice probability `r` in `[0,1]`, an explicit
interpolation weight gives `exp(c*(1-lambda)^2-lambda*log(r)) <= 2-r`.
We use the absolute constant `c=1/64`. This is the scalar input to
the combinatorial-distance induction, not the concentration theorem.

Reference: Terence Tao, 254A Notes 1, Concentration of measure, 2010.
https://terrytao.wordpress.com/2010/01/03/254a-notes-1-concentration-of-measure/
-/

noncomputable section
open Classical

namespace CircularLaw

theorem talagrand_small_slice_exponential {r : ℝ} (hr : r ≤ 3 / 4) :
    Real.exp (1 / 64) ≤ 2 - r := by
  have hLog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  have hExponent : (1 : ℝ) / 64 ≤ Real.log (5 / 4) := by norm_num at hLog; linarith
  calc
    _ ≤ Real.exp (Real.log (5 / 4)) := Real.exp_le_exp.mpr hExponent
    _ = 5 / 4 := Real.exp_log (by norm_num)
    _ ≤ _ := by linarith

theorem talagrand_large_slice_logarithmic {r : ℝ} (hr : 3 / 4 < r) (hr1 : r ≤ 1) :
    (1 - (4 * r - 3)) ^ 2 / 64 - (4 * r - 3) * Real.log r ≤ Real.log (2 - r) := by
  have hr0 : 0 < r := by linarith
  have hOther : 0 < 2 - r := by linarith
  have hWeight : 0 ≤ 4 * r - 3 := by linarith
  have hLogR := Real.one_sub_inv_le_log_of_pos hr0
  have hLogOther := Real.one_sub_inv_le_log_of_pos hOther
  have hProduct := mul_le_mul_of_nonneg_left hLogR hWeight
  have hRatio : (1 - (4 * r - 3)) ^ 2 / 64 - (4 * r - 3) * (1 - r⁻¹) ≤
      1 - (2 - r)⁻¹ := by
    have hPolynomial : 0 ≤ (1 - r) ^ 2 * (7 + 16 * (1 - r) + (1 - r) ^ 2) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith [sq_nonneg (1 - r)]
    field_simp
    nlinarith
  linarith

def talagrandSliceWeight (r : ℝ) : ℝ := if r ≤ 3 / 4 then 0 else 4 * r - 3

theorem talagrandSliceWeight_bounds {r : ℝ} (hr1 : r ≤ 1) :
    0 ≤ talagrandSliceWeight r ∧ talagrandSliceWeight r ≤ 1 := by
  unfold talagrandSliceWeight
  split_ifs <;> constructor <;> linarith

theorem talagrandSliceWeight_exponential {r : ℝ} (hr1 : r ≤ 1) :
    Real.exp ((1 - talagrandSliceWeight r) ^ 2 / 64 - talagrandSliceWeight r * Real.log r) ≤ 2 - r := by
  unfold talagrandSliceWeight
  split_ifs with hSmall
  · simpa only [sub_zero, one_pow, zero_mul] using talagrand_small_slice_exponential hSmall
  · have hOther : 0 < 2 - r := by linarith
    calc
      _ ≤ Real.exp (Real.log (2 - r)) := Real.exp_le_exp.mpr
        (talagrand_large_slice_logarithmic (lt_of_not_ge hSmall) hr1)
      _ = _ := Real.exp_log hOther

theorem talagrand_slice_interpolation {r : ℝ} (hr1 : r ≤ 1) :
    ∃ weight : ℝ, 0 ≤ weight ∧ weight ≤ 1 ∧
      Real.exp ((1 - weight) ^ 2 / 64 - weight * Real.log r) ≤ 2 - r :=
  ⟨talagrandSliceWeight r, (talagrandSliceWeight_bounds hr1).1,
    (talagrandSliceWeight_bounds hr1).2, talagrandSliceWeight_exponential hr1⟩

theorem talagrand_one_coordinate_moment {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a + (1 - a) * Real.exp (1 / 64) ≤ 1 / a := by
  have hExp : Real.exp (1 / 64) ≤ 2 := by
    simpa only [sub_zero] using talagrand_small_slice_exponential (r := 0) (by norm_num)
  have hWeighted := mul_le_mul_of_nonneg_left hExp (sub_nonneg.mpr ha1)
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (a - 1)]

theorem talagrand_probability_absorption {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    (1 / b) * (2 - p / b) ≤ 1 / p := by
  field_simp
  nlinarith [sq_nonneg (b - p)]

end CircularLaw
