import CircularLaw.WitnessDegreeRates

/-!
# The literal first steep scale

`n1` is the natural ceiling of `n/d^(3/2)`. The bounds retain this
rounding and identify its witness density with the scale `n/sqrt(d)`.
-/

noncomputable section
open Classical

namespace CircularLaw

def firstSteepScale (n d : ℕ) : ℕ :=
  ⌈(n : ℝ) / Real.rpow (d : ℝ) (3 / 2)⌉₊

theorem degree_three_halves_eq {d : ℕ} (hd : 0 < d) :
    Real.rpow (d : ℝ) (3 / 2) = (d : ℝ) * Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [Real.rpow_eq_pow]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hdR,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem firstSteepScale_lower {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / ((d : ℝ) * Real.sqrt d) ≤ firstSteepScale n d := by
  rw [firstSteepScale, ← degree_three_halves_eq hd]
  exact Nat.le_ceil _

theorem firstSteepScale_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < firstSteepScale n d := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hn) (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

theorem firstSteepScale_upper {n d : ℕ} (hd : 0 < d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) :
    (firstSteepScale n d : ℝ) ≤ 2 * n / ((d : ℝ) * Real.sqrt d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDen : (0 : ℝ) < (d : ℝ) * Real.sqrt d := by positivity
  have hRatio : (1 : ℝ) ≤ n / ((d : ℝ) * Real.sqrt d) :=
    (le_div_iff₀ hDen).mpr (by simpa only [one_mul] using hDimension)
  have hCeil := Nat.ceil_lt_add_one (le_trans zero_le_one hRatio)
  rw [firstSteepScale, degree_three_halves_eq hd]
  rw [show 2 * (n : ℝ) / ((d : ℝ) * Real.sqrt d) =
    2 * ((n : ℝ) / ((d : ℝ) * Real.sqrt d)) by ring]
  linarith

theorem firstSteepScale_density_lower {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / Real.sqrt d ≤ (d : ℝ) * firstSteepScale n d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := by positivity
  have h := (div_le_iff₀ (mul_pos hdR hRoot)).mp (firstSteepScale_lower (n := n) hd)
  apply (div_le_iff₀ hRoot).mpr
  nlinarith

theorem firstSteepScale_density_upper {n d : ℕ} (hd : 0 < d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) :
    (d : ℝ) * firstSteepScale n d ≤ 2 * n / Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : (0 : ℝ) < Real.sqrt d := by positivity
  have h := (le_div_iff₀ (mul_pos hdR hRoot)).mp (firstSteepScale_upper hd hDimension)
  apply (le_div_iff₀ hRoot).mpr
  nlinarith

theorem firstSteepScale_small {n d : ℕ} (hd : 0 < d)
    (hDimension : (d : ℝ) * Real.sqrt d ≤ n) (hRoot : (200 : ℝ) ≤ Real.sqrt d) :
    100 * d * firstSteepScale n d ≤ n := by
  have hRootPos : (0 : ℝ) < Real.sqrt d := by linarith
  have hUpper := (le_div_iff₀ hRootPos).mp (firstSteepScale_density_upper hd hDimension)
  have hScaled := mul_le_mul_of_nonneg_left hRoot
    (by positivity : (0 : ℝ) ≤ (d : ℝ) * firstSteepScale n d)
  have hReal : (100 : ℝ) * d * firstSteepScale n d ≤ n := by nlinarith
  exact_mod_cast hReal

end CircularLaw
