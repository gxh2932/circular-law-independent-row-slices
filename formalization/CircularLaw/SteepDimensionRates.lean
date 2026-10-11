import CircularLaw.FirstScaleWitnessFailure
import CircularLaw.SteepStrideRates

/-!
# Dimension conditions and scale-union prefactors

Every fixed power of a polylogarithmic degree is negligible compared
with the dimension. This also absorbs the scale-count prefactor into
the `n/d^3` exponent without any vector net count.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_polylog_power_dimension (power : ℝ) (k : ℕ) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (d : ℝ) ≤ Real.rpow (Real.log n) power → A * (d : ℝ) ^ k ≤ n := by
  have hSmall : ∀ᶠ n : ℕ in atTop,
      Real.rpow (Real.log n) (power * k) / n < 1 / A :=
    (log_power_div_self_tendsto_zero (power * k)).eventually
      (gt_mem_nhds (div_pos zero_lt_one hA))
  filter_upwards [hSmall, eventually_ge_atTop 2] with n hSmall hn
  intro d hUpper
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hPower : (d : ℝ) ^ k ≤ Real.rpow (Real.log n) (power * k) := by
    calc
      _ ≤ (Real.rpow (Real.log n) power) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg d) hUpper k
      _ = _ := by
        simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using
          (Real.rpow_mul hLog power (k : ℝ)).symm
  have hScaled := mul_le_mul_of_nonneg_left hPower hA.le
  have hBound := (div_lt_div_iff₀ hnR hA).mp hSmall
  nlinarith

theorem eventually_steep_scale_prefactor (power : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ Real.rpow (Real.log n) power →
        Real.log n ≤ (5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3 := by
  have hRate := uniqueWitnessRate_pos
  have hSmall : ∀ᶠ n : ℕ in atTop,
      Real.rpow (Real.log n) (1 + power * 3) / n < 5 * uniqueWitnessRate / 2 :=
    (log_power_div_self_tendsto_zero (1 + power * 3)).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 5 * uniqueWitnessRate / 2))
  filter_upwards [hSmall, eventually_ge_atTop 2] with n hSmall hn
  intro d hd hUpper
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hPower : (d : ℝ) ^ 3 ≤ Real.rpow (Real.log n) (power * 3) := by
    calc
      _ ≤ (Real.rpow (Real.log n) power) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg d) hUpper 3
      _ = _ := by
        exact (Real.rpow_natCast _ 3).symm.trans (Real.rpow_mul hLog.le power 3).symm
  have hProduct : Real.log n * (d : ℝ) ^ 3 ≤ Real.rpow (Real.log n) (1 + power * 3) := by
    calc
      _ ≤ Real.log n * Real.rpow (Real.log n) (power * 3) :=
        mul_le_mul_of_nonneg_left hPower hLog.le
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_add hLog, Real.rpow_one]
  have hBound := (div_lt_iff₀ hnR).mp hSmall
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 3)).mpr
  linarith

theorem steep_witness_prefactor_absorbed {n d : ℕ} (hn : 0 < n)
    (hLog : Real.log n ≤ (5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) :
    (n : ℝ) * Real.exp (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3) ≤
      Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = Real.exp (Real.log n) * Real.exp (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3) := by
      rw [Real.exp_log hnR]
    _ = Real.exp (Real.log n + (-5 * uniqueWitnessRate * n / (d : ℝ) ^ 3)) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [show -5 * uniqueWitnessRate * (n : ℝ) / (d : ℝ) ^ 3 =
        -2 * ((5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) by ring]
      rw [show -(5 * uniqueWitnessRate / 2) * (n : ℝ) / (d : ℝ) ^ 3 =
        -((5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) by ring]
      linarith

end CircularLaw
