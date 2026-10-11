import CircularLaw.SparsePatternPowerLimits

/-!
# Sparse pattern budgets with a real effective degree

A principal minor keeps the ambient Bernoulli probability. Its effective
degree is its own dimension times that probability, which can be real.
The falling-factorial, dimension and degree budgets remain separate.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem real_power_ratio_eq_inverse_pow {D : ℝ} (hD : D ≠ 0) {e m : ℕ}
    (hE : e ≤ m) : D ^ e / D ^ m = (1 / D) ^ (m - e) := by
  have hPow : D ^ m = D ^ e * D ^ (m - e) := by
    conv_lhs => rw [← Nat.add_sub_of_le hE, pow_add]
  rw [hPow]
  simp only [div_pow, one_pow]
  field_simp

theorem real_power_ratio_le_one {D : ℝ} (hD : 1 ≤ D) {e m : ℕ} (hE : e ≤ m) :
    D ^ e / D ^ m ≤ 1 := by
  apply (div_le_one (pow_pos (by linarith) m)).mpr
  exact pow_le_pow_right₀ hD hE

theorem real_power_ratio_tendsto (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (e m : ℕ) (hE : e ≤ m) :
    Tendsto (fun n => D n ^ e / D n ^ m) atTop (𝓝 (if e = m then 1 else 0)) := by
  have h := (tendsto_inv_atTop_zero.comp hD).pow (m - e)
  have hValue : (0 : ℝ) ^ (m - e) = if e = m then 1 else 0 := by
    by_cases hem : e = m
    · subst m
      simp
    · have hPos : m - e ≠ 0 := by omega
      simp [hem, hPos]
  rw [hValue] at h
  apply h.congr'
  filter_upwards [hD.eventually_gt_atTop 0] with n hn
  simpa only [one_div] using (real_power_ratio_eq_inverse_pow hn.ne' hE).symm

def sparseRealEvenPatternBudget (n v e m : ℕ) (D : ℝ) : ℝ :=
  ((n.descFactorial v : ℝ) / (n : ℝ) ^ v) *
    ((n : ℝ) ^ v / (n : ℝ) ^ (e + 1)) * (D ^ e / D ^ m)

theorem inverse_sqrt_real_even_power {D : ℝ} (hD : 0 ≤ D) (m : ℕ) :
    ((Real.sqrt D)⁻¹) ^ (2 * m) = 1 / D ^ m := by
  rw [pow_mul, inv_pow, Real.sq_sqrt hD]
  simp only [one_div, inv_pow]

theorem sparse_real_even_pattern_scale_identity {n : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 0 < D) (v e m : ℕ) :
    (((Real.sqrt D)⁻¹) ^ (2 * m) / (n : ℝ)) *
      (n.descFactorial v : ℝ) * (D / n) ^ e = sparseRealEvenPatternBudget n v e m D := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inverse_sqrt_real_even_power hD.le, div_pow]
  unfold sparseRealEvenPatternBudget
  rw [pow_succ]
  field_simp

theorem sparse_real_even_pattern_budget_nonneg (n v e m : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ sparseRealEvenPatternBudget n v e m D := by
  unfold sparseRealEvenPatternBudget
  positivity

theorem sparse_real_even_pattern_budget_le_one {n v e m : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 1 ≤ D) (hV : v ≤ e + 1) (hE : e ≤ m) :
    sparseRealEvenPatternBudget n v e m D ≤ 1 := by
  have hF : (n.descFactorial v : ℝ) / (n : ℝ) ^ v ≤ 1 := by
    apply (div_le_one (pow_pos (by exact_mod_cast hn) v)).mpr
    exact_mod_cast Nat.descFactorial_le_pow n v
  have hN := dimension_power_ratio_le_one hn hV
  have hDegree := real_power_ratio_le_one hD hE
  unfold sparseRealEvenPatternBudget
  have hFN : (n.descFactorial v : ℝ) / (n : ℝ) ^ v *
      ((n : ℝ) ^ v / (n : ℝ) ^ (e + 1)) ≤ 1 := by
    nlinarith [show 0 ≤ (n.descFactorial v : ℝ) / (n : ℝ) ^ v by positivity,
      show 0 ≤ (n : ℝ) ^ v / (n : ℝ) ^ (e + 1) by positivity]
  nlinarith [show 0 ≤ D ^ e / D ^ m by positivity]

theorem sparse_real_even_pattern_budget_tendsto (q : ℕ → ℕ) (D : ℕ → ℝ)
    (hQ : Tendsto q atTop atTop) (hD : Tendsto D atTop atTop)
    (v e m : ℕ) (hV : v ≤ e + 1) (hE : e ≤ m) :
    Tendsto (fun n => sparseRealEvenPatternBudget (q n) v e m (D n)) atTop
      (𝓝 (if v = e + 1 ∧ e = m then 1 else 0)) := by
  have h := (((fixed_desc_factorial_ratio_tendsto v).comp hQ).mul
    ((dimension_power_ratio_tendsto v (e + 1) hV).comp hQ)).mul
    (real_power_ratio_tendsto D hD e m hE)
  by_cases hv : v = e + 1 <;> by_cases he : e = m <;>
    simpa only [sparseRealEvenPatternBudget, hv, he, if_true, if_false,
      and_true, and_false, false_and, true_and, one_mul, mul_one, zero_mul, mul_zero,
      Function.comp_apply] using h

theorem sparse_real_even_nonleading_budget_tendsto_zero (q : ℕ → ℕ) (D : ℕ → ℝ)
    (hQ : Tendsto q atTop atTop) (hD : Tendsto D atTop atTop)
    (v e m : ℕ) (hV : v ≤ e + 1) (hE : e ≤ m)
    (hNonleading : ¬ (v = e + 1 ∧ e = m)) :
    Tendsto (fun n => sparseRealEvenPatternBudget (q n) v e m (D n)) atTop (𝓝 0) := by
  simpa only [if_neg hNonleading] using
    sparse_real_even_pattern_budget_tendsto q D hQ hD v e m hV hE

theorem inverse_sqrt_real_degree_tendsto_zero (D : ℕ → ℝ) (hD : Tendsto D atTop atTop) :
    Tendsto (fun n => (Real.sqrt (D n))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hD)

end CircularLaw
