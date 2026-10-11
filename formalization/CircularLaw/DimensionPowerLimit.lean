import CircularLaw.GaussianEnergyConvergence

/-!
# Finite dimension-power ratios and their actual limits

An exponent at most the normalization exponent gives a ratio at most
one in positive dimension. It converges to one at equality and to zero
at every strictly smaller exponent.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem dimension_power_ratio_eq_inverse_pow {n d m : ℕ} (hn : 0 < n) (hd : d ≤ m) :
    (n : ℝ) ^ d / (n : ℝ) ^ m = (1 / (n : ℝ)) ^ (m - d) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hPow : (n : ℝ) ^ m = (n : ℝ) ^ d * (n : ℝ) ^ (m - d) := by
    conv_lhs => rw [← Nat.add_sub_of_le hd, pow_add]
  rw [hPow]
  simp only [div_pow, one_pow]
  field_simp

theorem dimension_power_ratio_le_one {n d m : ℕ} (hn : 0 < n) (hd : d ≤ m) :
    (n : ℝ) ^ d / (n : ℝ) ^ m ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_one (pow_pos hnR m)).mpr
  exact pow_le_pow_right₀ hnOne hd

theorem dimension_power_ratio_le_inverse {n d m : ℕ} (hn : 0 < n) (hd : d < m) :
    (n : ℝ) ^ d / (n : ℝ) ^ m ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (pow_pos hnR m) hnR).mpr
  rw [← pow_succ, one_mul]
  exact pow_le_pow_right₀ hnOne (Nat.succ_le_of_lt hd)

theorem dimension_power_ratio_tendsto (d m : ℕ) (hd : d ≤ m) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ d / (n : ℝ) ^ m) atTop
      (𝓝 (if d = m then 1 else 0)) := by
  have hEq : (fun n : ℕ => (n : ℝ) ^ d / (n : ℝ) ^ m) =ᶠ[atTop]
      fun n : ℕ => (1 / (n : ℝ)) ^ (m - d) :=
    (eventually_gt_atTop 0).mono (fun _ hn => dimension_power_ratio_eq_inverse_pow hn hd)
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (m - d)
  have hValue : (0 : ℝ) ^ (m - d) = if d = m then 1 else 0 := by
    by_cases hdm : d = m
    · subst m
      simp
    · have hPos : m - d ≠ 0 := by omega
      simp [hdm, hPos]
  rw [hValue] at h
  exact h.congr' hEq.symm

end CircularLaw
