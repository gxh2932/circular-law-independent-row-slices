import CircularLaw.SourceRemainingClasses
import CircularLaw.SourceStartingRank

/-!
# Finite compatibility of the almost-constant ranks

The rank `n0` equals the literal real floor. Its position between `n1`
and `n3`, positivity of `n3`, and the half-dimension bound follow from
explicit degree and dimension inequalities, with no rounding omitted.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem almostConstantRank_eq_floor (n d : ℕ) :
    almostConstantRank n d = ⌊(n : ℝ) / (16 * (d : ℝ))⌋₊ := by
  rw [show 16 * (d : ℝ) = ((16 * d : ℕ) : ℝ) by simp only [Nat.cast_mul, Nat.cast_ofNat],
    Nat.floor_div_natCast, Nat.floor_natCast]
  rfl

theorem secondSteepScale_valid {n d : ℕ} (hd : 0 < d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) :
    0 < secondSteepScale n d ∧ secondSteepScale n d ≤ n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hDenPos : 0 < Real.rpow (d : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hDenLower : 1 ≤ Real.rpow (d : ℝ) (2 / 3 : ℝ) :=
    Real.one_le_rpow hdR (by norm_num)
  have hDenUpper : Real.rpow (d : ℝ) (2 / 3 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by
    rw [← degree_three_halves_eq hd]
    exact Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)
  have hRatioLower : 1 ≤ (n : ℝ) / Real.rpow (d : ℝ) (2 / 3 : ℝ) :=
    (le_div_iff₀ hDenPos).mpr (by simpa only [one_mul] using hDenUpper.trans hDimension)
  have hFloorLower : 1 ≤ secondSteepScale n d := by
    apply (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤
      (n : ℝ) / Real.rpow (d : ℝ) (2 / 3 : ℝ))).mpr
    simpa only [Nat.cast_one] using hRatioLower
  have hFloorUpper := Nat.floor_le (by positivity : (0 : ℝ) ≤
    (n : ℝ) / Real.rpow (d : ℝ) (2 / 3 : ℝ))
  have hRatioUpper := div_le_self (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hDenLower
  have hUpper : (secondSteepScale n d : ℝ) ≤ n := hFloorUpper.trans hRatioUpper
  exact ⟨by omega, by exact_mod_cast hUpper⟩

theorem almostConstantRank_upper {n d : ℕ} (hd : 0 < d) :
    (almostConstantRank n d : ℝ) ≤ (n : ℝ) / (16 * d) := by
  have h : (almostConstantRank n d : ℝ) * (16 * d) ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n (16 * d)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
  exact h

theorem firstSteepScale_le_almostConstantRank {n d : ℕ} (hd : 0 < d)
    (hSmall : 100 * d * firstSteepScale n d ≤ n) :
    firstSteepScale n d ≤ almostConstantRank n d := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 16 * d)).mpr
  nlinarith

theorem thirdSteepScale_bounds {n : ℕ} {a₃ : ℝ} (ha : 0 < a₃)
    (hSize : 2 ≤ a₃ * (n : ℝ)) :
    0 < thirdSteepScale n a₃ ∧ a₃ * (n : ℝ) / 2 ≤ thirdSteepScale n a₃ ∧
      (thirdSteepScale n a₃ : ℝ) ≤ a₃ * n := by
  have hFloor := Nat.lt_floor_add_one (a₃ * (n : ℝ))
  have hLower : a₃ * (n : ℝ) / 2 ≤ thirdSteepScale n a₃ := by
    change _ ≤ (⌊a₃ * (n : ℝ)⌋₊ : ℝ)
    linarith
  have hPositive : (0 : ℝ) < thirdSteepScale n a₃ := by linarith
  exact ⟨by exact_mod_cast hPositive, hLower,
    Nat.floor_le (mul_nonneg ha.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n))⟩

theorem thirdSteepScale_half {n : ℕ} {a₃ : ℝ} (ha : 0 ≤ a₃) (haHalf : a₃ ≤ 1 / 2) :
    2 * thirdSteepScale n a₃ ≤ n := by
  have hFloor := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have hScaled := mul_le_mul_of_nonneg_right haHalf (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hReal : (2 : ℝ) * thirdSteepScale n a₃ ≤ n := by
    change 2 * (⌊a₃ * (n : ℝ)⌋₊ : ℝ) ≤ n
    linarith
  exact_mod_cast hReal

theorem almostConstantRank_le_thirdSteepScale {n d : ℕ} (hd : 0 < d)
    {a₃ : ℝ} (ha : 0 < a₃) (hDegree : 1 / (8 * a₃) ≤ (d : ℝ))
    (hSize : 2 ≤ a₃ * (n : ℝ)) : almostConstantRank n d ≤ thirdSteepScale n a₃ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hScaled := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * a₃)).mp hDegree
  have hCoefficient : 1 / (16 * (d : ℝ)) ≤ a₃ / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
    nlinarith
  have hRatio : (n : ℝ) / (16 * d) ≤ a₃ * n / 2 := by
    calc
      _ = (1 / (16 * (d : ℝ))) * n := by ring
      _ ≤ (a₃ / 2) * n := mul_le_mul_of_nonneg_right hCoefficient (Nat.cast_nonneg n)
      _ = _ := by ring
  have hReal := (almostConstantRank_upper (n := n) hd).trans
    (hRatio.trans (thirdSteepScale_bounds ha hSize).2.1)
  exact_mod_cast hReal

end CircularLaw
