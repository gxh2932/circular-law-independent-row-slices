import CircularLaw.LLYSecondSourceEntropy

/-!
# Polynomial decay of the actual rare first-rank exponent

The source ceiling implies n1*d is at least a positive multiple of
sqrt(n) whenever d<=n. Thus its exponential remainder is below every
prescribed polynomial rate, uniformly over the actual degree window.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem lly_source_first_rank_decay_lower {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) {a : ℝ} (ha : 0 < a) :
    a * Real.sqrt (48 * Real.log 2) * Real.sqrt n ≤ (llySourceFirstRank n d a : ℝ) * d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hFirst := mul_le_mul_of_nonneg_right (lly_source_first_rank_degree_lower (n := n) hd a)
    (Real.sqrt_nonneg d)
  have hEpsilon := mul_le_mul_of_nonneg_left (lly_source_epsilon_degree_lower hn hd)
    (by positivity : 0 ≤ a * (n : ℝ))
  have hCompare := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by exact_mod_cast hdn : (d : ℝ) ≤ n))
      (by positivity : 0 ≤ (llySourceFirstRank n d a : ℝ) * d)
  apply (mul_le_mul_iff_left₀ hRoot).mp
  calc
    _ = a * Real.sqrt (48 * Real.log 2) * (n : ℝ) := by
      rw [mul_assoc, Real.mul_self_sqrt hnR.le]
    _ ≤ (llySourceFirstRank n d a : ℝ) * d * Real.sqrt d := by nlinarith only [hFirst, hEpsilon]
    _ ≤ _ := hCompare

theorem eventually_lly_source_first_rank_exponential_polynomial {a A : ℝ}
    (ha : 0 < a) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ n →
      Real.exp (-(llySourceFirstRank n d a : ℝ) * d / 32) ≤ (n : ℝ) ^ (-A) := by
  have hCoefficient : 0 < a * Real.sqrt (48 * Real.log 2) / 32 := by
    apply div_pos (mul_pos ha (Real.sqrt_pos.mpr ?_)) (by norm_num)
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  filter_upwards [eventually_ge_atTop 2,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 2)
      hCoefficient 0 (A + 1) (by linarith)] with n hn hBudget
  intro d hd hdn
  change 0 + (A + 1) * Real.log (n : ℝ) ≤
    (a * Real.sqrt (48 * Real.log 2) / 32) * (n : ℝ) ^ (1 / 2 : ℝ) at hBudget
  rw [zero_add, ← Real.sqrt_eq_rpow] at hBudget
  have hFirst := lly_source_first_rank_decay_lower hn hd hdn ha
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)]
  apply Real.exp_le_exp.mpr
  nlinarith only [hBudget, hFirst, Real.log_natCast_nonneg n]

end CircularLaw
