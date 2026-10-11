import CircularLaw.ShiftedSquarePrefixComparison
import CircularLaw.FixedShiftIntermediateTheorem

/-!
# The finite upper cap and logarithmic regularization cost

The raw shift is z*sqrt(d). At eta=tau/n with 0<tau<=1, the upper
cap and its logarithmic ratio have the exact dimension dependence used
in Section 9. The estimates do not assume a smallest singular value.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem rowReplacementUpperBound_shifted_le {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (z : ℂ) {η : ℝ} (hη : 0 < η) (hηOne : η ≤ 1) :
    rowReplacementUpperBound n η (‖z‖ * Real.sqrt d) ≤
      2 * (1 + ‖z‖) * Real.sqrt n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hRootOne : (1 : ℝ) ≤ Real.sqrt n := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hnOne
  have hRootD : Real.sqrt (d : ℝ) ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast hdn)
  have hRootCap : Real.sqrt n ≤ (1 + ‖z‖) * Real.sqrt n := by
    nlinarith [mul_nonneg (norm_nonneg z) (Real.sqrt_nonneg (n : ℝ))]
  have hEtaCap := hηOne.trans (hRootOne.trans hRootCap)
  have hRowCap : Real.sqrt n + ‖z‖ * Real.sqrt d ≤ (1 + ‖z‖) * Real.sqrt n := by
    nlinarith only [mul_le_mul_of_nonneg_left hRootD (norm_nonneg z)]
  have hEtaSq := pow_le_pow_left₀ hη.le hEtaCap 2
  have hRowSq := pow_le_pow_left₀
    (by positivity : 0 ≤ Real.sqrt n + ‖z‖ * Real.sqrt d) hRowCap 2
  unfold rowReplacementUpperBound
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg ((1 + ‖z‖) * Real.sqrt n)]

theorem shifted_replacement_log_ratio_bound {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (z : ℂ) {τ : ℝ} (hτ : 0 < τ) (hτOne : τ ≤ 1) :
    Real.log (rowReplacementUpperBound n (τ / n) (‖z‖ * Real.sqrt d) / (τ / n)) ≤
      Real.log (2 * (1 + ‖z‖)) + (3 / 2 : ℝ) * Real.log n - Real.log τ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hη : 0 < τ / n := div_pos hτ hnR
  have hηOne : τ / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr (hτOne.trans hnOne)
  have hUpper := rowReplacementUpperBound_shifted_le hn hdn z hη hηOne
  have hPos : 0 < rowReplacementUpperBound n (τ / n) (‖z‖ * Real.sqrt d) :=
    hη.trans_le (rowReplacementUpperBound_ge_regularization n hη _)
  have hLog := Real.log_le_log (div_pos hPos hη)
    (div_le_div_of_nonneg_right hUpper hη.le)
  have hCap : (2 * (1 + ‖z‖) : ℝ) ≠ 0 := by positivity
  have hRoot : (Real.sqrt (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  rw [Real.log_div (mul_ne_zero hCap hRoot) hη.ne', Real.log_mul hCap hRoot,
    Real.log_sqrt hnR.le, Real.log_div hτ.ne' hnR.ne'] at hLog
  linarith

theorem shifted_replacement_power_cutoff_log_bound {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (z : ℂ) {B : ℝ} (hB : 0 ≤ B) :
    Real.log (rowReplacementUpperBound n (Real.rpow (n : ℝ) (-B) / n)
      (‖z‖ * Real.sqrt d) / (Real.rpow (n : ℝ) (-B) / n)) ≤
      Real.log (2 * (1 + ‖z‖)) + (B + 3 / 2) * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < Real.rpow (n : ℝ) (-B) := Real.rpow_pos_of_pos hnR _
  have hτOne : Real.rpow (n : ℝ) (-B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (neg_nonpos.mpr hB)
  have h := shifted_replacement_log_ratio_bound hn hdn z hτ hτOne
  simp only [Real.rpow_eq_pow] at h ⊢
  rw [Real.log_rpow hnR] at h
  nlinarith only [h]

end CircularLaw
