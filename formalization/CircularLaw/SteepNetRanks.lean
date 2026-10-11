import CircularLaw.SteepGridPolynomial

/-!
# Density bounds for the literal net prefixes

Both ceilings are retained. Subtracting one bounds their strict prefixes
by the unrounded ratios. Cubic floor-stride growth gives a quarter-power
lower bound, sufficient to absorb the high-prefix cost in the lower band.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem positive_degree_power_mul {d : ℕ} (hd : 0 < d) (a b : ℝ) :
    Real.rpow (d : ℝ) a * Real.rpow (d : ℝ) b = Real.rpow (d : ℝ) (a + b) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_add (by exact_mod_cast hd : (0 : ℝ) < d)]

theorem positive_degree_power_log {d : ℕ} (hd : 0 < d) (a : ℝ) :
    Real.log (Real.rpow (d : ℝ) a) = a * Real.log (d : ℝ) := by
  simp only [Real.rpow_eq_pow]
  exact Real.log_rpow (by exact_mod_cast hd : (0 : ℝ) < d) a

theorem steepStride_quarter_power_lower {d : ℕ}
    (hp : 1 ≤ steepStride d) (hCubic : 4 * d ≤ steepStride d ^ 3) :
    Real.rpow (d : ℝ) (1 / 4) ≤ steepStride d := by
  have hFourth : d ≤ steepStride d ^ 4 := by
    apply (show d ≤ 4 * d by omega).trans
    exact hCubic.trans (Nat.pow_le_pow_right (by omega : 0 < steepStride d) (by decide : 3 ≤ 4))
  have hReal : (d : ℝ) ≤ (steepStride d : ℝ) ^ 4 := by exact_mod_cast hFourth
  have hPower := Real.rpow_le_rpow (Nat.cast_nonneg d) hReal (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hRoot : Real.rpow ((steepStride d : ℝ) ^ 4) (1 / 4) = (steepStride d : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (steepStride d : ℝ) 4,
      ← Real.rpow_mul (Nat.cast_nonneg (steepStride d))]
    norm_num
  simpa only [← Real.rpow_eq_pow, hRoot] using hPower

theorem terminalSteepSize_prev_upper {p n1 : ℕ} (hp : 0 < p) (hn1 : 0 < n1) :
    (terminalSteepSize p n1 - 1 : ℕ) ≤ (n1 : ℝ) / p := by
  have hRatio : 0 ≤ (n1 : ℝ) / p := by positivity
  have hTerminal : 0 < terminalSteepSize p n1 := Nat.ceil_pos.mpr (by positivity)
  have hCeil := Nat.ceil_lt_add_one hRatio
  rw [Nat.cast_sub hTerminal, Nat.cast_one]
  change (⌈(n1 : ℝ) / p⌉₊ : ℝ) - 1 ≤ _
  linarith

theorem steep_net_high_prefix_density {n d : ℕ} (hd : 0 < d)
    (hp : 1 ≤ steepStride d) (hn1 : 0 < firstSteepScale n d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (hCubic : 4 * d ≤ steepStride d ^ 3) :
    (terminalSteepSize (steepStride d) (firstSteepScale n d) - 1 : ℕ) ≤
      2 * (n : ℝ) / Real.rpow (d : ℝ) (7 / 4) := by
  have hpR : (0 : ℝ) < steepStride d := by exact_mod_cast (by omega : 0 < steepStride d)
  have hD : 0 < Real.rpow (d : ℝ) (3 / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hQuarter := steepStride_quarter_power_lower hp hCubic
  have hProduct : Real.rpow (d : ℝ) (7 / 4) ≤ Real.rpow (d : ℝ) (3 / 2) * steepStride d := by
    have h := mul_le_mul_of_nonneg_left hQuarter hD.le
    rw [positive_degree_power_mul hd] at h
    norm_num at h
    exact h
  calc
    _ ≤ (firstSteepScale n d : ℝ) / steepStride d :=
      terminalSteepSize_prev_upper (by omega : 0 < steepStride d) hn1
    _ ≤ (2 * (n : ℝ) / Real.rpow (d : ℝ) (3 / 2)) / steepStride d := by
      apply div_le_div_of_nonneg_right _ hpR.le
      simpa only [← degree_three_halves_eq hd] using firstSteepScale_upper hd hDimension
    _ = 2 * (n : ℝ) / (Real.rpow (d : ℝ) (3 / 2) * steepStride d) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (by exact_mod_cast hd) _) hProduct

theorem secondSteepScale_density_lower {n d : ℕ} (hd : 0 < d) (hDimension : 2 * d ≤ n) :
    (n : ℝ) ≤ 2 * (secondSteepScale n d : ℝ) * Real.rpow (d : ℝ) (2 / 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < Real.rpow (d : ℝ) (2 / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hDUpper : Real.rpow (d : ℝ) (2 / 3) ≤ (d : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hdR (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hN : (2 : ℝ) * d ≤ n := by exact_mod_cast hDimension
  have hRatio : 2 ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3) := (le_div_iff₀ hD).mpr (by linarith)
  have hFloor := Nat.lt_floor_add_one ((n : ℝ) / Real.rpow (d : ℝ) (2 / 3))
  have hHalf : (n : ℝ) / Real.rpow (d : ℝ) (2 / 3) ≤ 2 * secondSteepScale n d := by
    change _ ≤ 2 * (⌊(n : ℝ) / Real.rpow (d : ℝ) (2 / 3)⌋₊ : ℝ)
    linarith
  exact (div_le_iff₀ hD).mp hHalf

end CircularLaw
