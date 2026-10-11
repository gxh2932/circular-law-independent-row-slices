import CircularLaw.PlanarCosine

/-!
# The normalized single-vector Gaussian bound

The truncated difference length normalizes the cosine coefficient. For
positive total moment and radii `0 < r₀ ≤ r`, the planar integral is uniformly
bounded by `96 / (r * sqrt A)`, independently of the nonzero direction vector.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace CircularLaw

theorem gaussian_radius_sqrt_le {r : ℝ} (hr : 0 < r) :
    Real.sqrt (Real.pi / (r ^ 2 / 4)) ≤ 4 / r := by
  have hEq : Real.pi / (r ^ 2 / 4) = (4 * Real.pi) / r ^ 2 := by ring
  rw [hEq, Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  apply div_le_div_of_nonneg_right _ hr.le
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩

theorem truncated_cosine_coefficient_sqrt_le {A m : ℝ} (hA : 0 < A) (hm : 0 < m) :
    Real.sqrt (Real.pi / (8 * (A / (2 * m ^ 2)))) ≤ m / Real.sqrt A := by
  have hEq : Real.pi / (8 * (A / (2 * m ^ 2))) = (Real.pi / 4) * (m ^ 2 / A) := by
    field_simp
    norm_num
  rw [hEq, Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg m), Real.sqrt_sq hm.le]
  have hPi : Real.sqrt (Real.pi / 4) ≤ 1 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  exact mul_le_of_le_one_left (by positivity) hPi

theorem truncated_cosine_scale_arithmetic {ρ r m A : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hA : 0 < A)
    (hmρ : m ≤ ρ) (hmr : m ≤ r) :
    (8 / ρ + 16 / r) * (m / Real.sqrt A) * (4 / r) ≤ 96 / (r * Real.sqrt A) := by
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have h1 : m / ρ ≤ 1 := (div_le_one hρ).mpr hmρ
  have h2 : m / r ≤ 1 := (div_le_one hr).mpr hmr
  have hWeighted : 8 * (m / ρ) + 16 * (m / r) ≤ 24 := by linarith
  have h := mul_le_mul_of_nonneg_right hWeighted (by positivity : 0 ≤ 4 / (r * Real.sqrt A))
  convert h using 1 <;> field_simp
  all_goals ring

theorem truncated_planar_cosine_integral_le (v : ℂ) (hv : v ≠ 0)
    {r₀ r A : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hA : 0 < A) :
    (∫ t : ℂ, planarCosineKernel (r ^ 2 / 4)
      (A / (2 * (min ‖v‖ r₀) ^ 2)) v t) ≤ 96 / (r * Real.sqrt A) := by
  have hrPos : 0 < r := hr₀.trans_le hr
  have hρ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hm : 0 < min ‖v‖ r₀ := lt_min hρ hr₀
  have hb : 0 < r ^ 2 / 4 := by positivity
  have ha : 0 < A / (2 * (min ‖v‖ r₀) ^ 2) := by positivity
  have h := planarCosineKernel_integral_le_clean hb ha v hv
  have hS := gaussian_radius_sqrt_le hrPos
  have hCoeff := truncated_cosine_coefficient_sqrt_le hA hm
  have hFirst : 2 * Real.pi / ‖v‖ + 4 * Real.sqrt (Real.pi / (r ^ 2 / 4)) ≤
      8 / ‖v‖ + 16 / r := by
    have hPi := div_le_div_of_nonneg_right
      (show 2 * Real.pi ≤ 8 by nlinarith [Real.pi_le_four]) hρ.le
    calc
      _ ≤ 8 / ‖v‖ + 4 * (4 / r) :=
        add_le_add hPi (mul_le_mul_of_nonneg_left hS (by norm_num))
      _ = _ := by ring
  have hProduct := mul_le_mul
    (mul_le_mul hFirst hCoeff (Real.sqrt_nonneg _) (by positivity)) hS
    (Real.sqrt_nonneg _) (by positivity)
  exact (h.trans hProduct).trans
    (truncated_cosine_scale_arithmetic hρ hrPos hA
      (min_le_left _ _) ((min_le_right _ _).trans hr))

end CircularLaw
