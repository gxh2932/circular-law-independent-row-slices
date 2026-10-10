import CircularLaw.SteepNetEntropy

/-!
# Polynomial bounds for the actual integer grid counts

The base grid has degree three for `T1` and degree six for `T2`.
The middle and high grids retain their larger ranges, whose shorter
coordinate prefixes will absorb their logarithmic costs.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem steepNetGridCount_le_polynomial {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 1 ≤ R) :
    (steepNetGridCount d R : ℝ) ≤ 121 * (d : ℝ) ^ 3 * R ^ 2 := by
  have hD : 1 ≤ Real.rpow (d : ℝ) (3 / 2) :=
    Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)
  have hQ : 1 ≤ Real.rpow (d : ℝ) (3 / 2) * R := by nlinarith
  have hRadius := gridBoxRadius_upper (k := steepNetResolution d) (by linarith : 0 ≤ R)
  have hResolution := mul_le_mul_of_nonneg_right (steepNetResolution_upper hd) (by linarith : 0 ≤ R)
  have hSide : 2 * (gridBoxRadius (steepNetResolution d) R : ℝ) + 1 ≤
      11 * Real.rpow (d : ℝ) (3 / 2) * R := by nlinarith
  have hSquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    2 * (gridBoxRadius (steepNetResolution d) R : ℝ) + 1) hSide 2
  change (((2 * gridBoxRadius (steepNetResolution d) R + 1) ^ 2 : ℕ) : ℝ) ≤ _
  push_cast
  apply hSquare.trans_eq
  calc
    _ = 121 * Real.rpow (d : ℝ) (3 / 2) ^ 2 * R ^ 2 := by ring
    _ = _ := by rw [degree_three_halves_sq hd]

theorem steepNetGridCount_base_one {d : ℕ} (hd : 0 < d) :
    (steepNetGridCount d 1 : ℝ) ≤ 121 * (d : ℝ) ^ 3 := by
  simpa only [one_pow, mul_one] using steepNetGridCount_le_polynomial hd (le_refl (1 : ℝ))

theorem steepNetGridCount_base_power {d : ℕ} (hd : 0 < d) :
    (steepNetGridCount d (Real.rpow (d : ℝ) (3 / 2)) : ℝ) ≤ 121 * (d : ℝ) ^ 6 := by
  have h := steepNetGridCount_le_polynomial (R := Real.rpow (d : ℝ) (3 / 2)) hd
    (Real.one_le_rpow (by exact_mod_cast hd : (1 : ℝ) ≤ d) (by norm_num : (0 : ℝ) ≤ 3 / 2))
  rw [degree_three_halves_sq hd] at h
  convert h using 1
  ring

theorem steepNetGridCount_middle {d : ℕ} (hd : 0 < d) {cap : ℝ}
    (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2)) :
    (steepNetGridCount d (4 * (d : ℝ) * cap) : ℝ) ≤ 1936 * (d : ℝ) ^ 8 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 1 ≤ 4 * (d : ℝ) * cap := by nlinarith
  have hSquare := pow_le_pow_left₀ (by linarith : 0 ≤ cap) hCapUpper 2
  rw [degree_three_halves_sq hd] at hSquare
  apply (steepNetGridCount_le_polynomial hd hR).trans
  have hScaled := mul_le_mul_of_nonneg_left hSquare (by positivity : (0 : ℝ) ≤ 1936 * (d : ℝ) ^ 5)
  convert hScaled using 1 <;> ring

theorem steepNetGridCount_high {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {cap : ℝ}
    (hCap : 1 ≤ cap) (hCapUpper : cap ≤ Real.rpow (d : ℝ) (3 / 2)) :
    (steepNetGridCount d ((n : ℝ) ^ 6 * cap) : ℝ) ≤ 121 * (d : ℝ) ^ 6 * (n : ℝ) ^ 12 := by
  have hnSix : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have hR : 1 ≤ (n : ℝ) ^ 6 * cap := by nlinarith
  have hSquare := pow_le_pow_left₀ (by linarith : 0 ≤ cap) hCapUpper 2
  rw [degree_three_halves_sq hd] at hSquare
  apply (steepNetGridCount_le_polynomial hd hR).trans
  have hScaled := mul_le_mul_of_nonneg_left hSquare
    (by positivity : (0 : ℝ) ≤ 121 * (d : ℝ) ^ 3 * (n : ℝ) ^ 12)
  convert hScaled using 1 <;> ring

theorem steepNetGridCount_log_le {d : ℕ} {R A : ℝ}
    (hCount : (steepNetGridCount d R : ℝ) ≤ A) :
    Real.log (steepNetGridCount d R) ≤ Real.log A :=
  Real.log_le_log (by exact_mod_cast steepNetGridCount_pos d R : (0 : ℝ) < steepNetGridCount d R) hCount

end CircularLaw
