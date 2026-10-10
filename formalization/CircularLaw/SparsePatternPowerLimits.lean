import CircularLaw.FiniteKernelColorings
import CircularLaw.DimensionPowerLimit

/-!
# The two powers controlling sparse Bernoulli patterns

For a word of length 2m, a pattern with v vertices and e distinct entries
has normalization bounded by its falling-factorial ratio, the dimension
ratio n^v/n^(e+1), and the degree ratio d^e/d^m. Under v <= e+1 and e <= m,
these ratios are bounded and their product tends to zero unless both
inequalities are equalities. This keeps dimension and sparse degree as
separate parameters.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sparseEvenPatternBudget (n d v e m : ℕ) : ℝ :=
  ((n.descFactorial v : ℝ) / (n : ℝ) ^ v) *
    ((n : ℝ) ^ v / (n : ℝ) ^ (e + 1)) * ((d : ℝ) ^ e / (d : ℝ) ^ m)

theorem inverse_sqrt_nat_even_power (d m : ℕ) :
    ((Real.sqrt (d : ℝ))⁻¹) ^ (2 * m) = 1 / (d : ℝ) ^ m := by
  rw [pow_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp only [one_div, inv_pow]

theorem sparse_even_pattern_scale_identity {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (v e m : ℕ) :
    (((Real.sqrt (d : ℝ))⁻¹) ^ (2 * m) / (n : ℝ)) *
      (n.descFactorial v : ℝ) * ((d : ℝ) / n) ^ e = sparseEvenPatternBudget n d v e m := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [inverse_sqrt_nat_even_power, div_pow]
  unfold sparseEvenPatternBudget
  rw [pow_succ]
  field_simp

theorem sparse_even_pattern_budget_nonneg (n d v e m : ℕ) :
    0 ≤ sparseEvenPatternBudget n d v e m := by
  unfold sparseEvenPatternBudget
  positivity

theorem sparse_even_pattern_budget_le_one {n d v e m : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hV : v ≤ e + 1) (hE : e ≤ m) : sparseEvenPatternBudget n d v e m ≤ 1 := by
  have hF : (n.descFactorial v : ℝ) / (n : ℝ) ^ v ≤ 1 := by
    apply (div_le_one (pow_pos (by exact_mod_cast hn) v)).mpr
    exact_mod_cast Nat.descFactorial_le_pow n v
  have hN := dimension_power_ratio_le_one hn hV
  have hD := dimension_power_ratio_le_one hd hE
  unfold sparseEvenPatternBudget
  have hFN : (n.descFactorial v : ℝ) / (n : ℝ) ^ v *
      ((n : ℝ) ^ v / (n : ℝ) ^ (e + 1)) ≤ 1 := by
    nlinarith [show 0 ≤ (n.descFactorial v : ℝ) / (n : ℝ) ^ v by positivity,
      show 0 ≤ (n : ℝ) ^ v / (n : ℝ) ^ (e + 1) by positivity]
  nlinarith [show 0 ≤ (d : ℝ) ^ e / (d : ℝ) ^ m by positivity]

theorem sparse_even_pattern_budget_tendsto (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (v e m : ℕ) (hV : v ≤ e + 1) (hE : e ≤ m) :
    Tendsto (fun n => sparseEvenPatternBudget n (d n) v e m) atTop
      (𝓝 (if v = e + 1 ∧ e = m then 1 else 0)) := by
  have h := ((fixed_desc_factorial_ratio_tendsto v).mul
    (dimension_power_ratio_tendsto v (e + 1) hV)).mul
    ((dimension_power_ratio_tendsto e m hE).comp hDegree)
  by_cases hv : v = e + 1 <;> by_cases he : e = m <;>
    simpa only [sparseEvenPatternBudget, hv, he, if_true, if_false,
      and_true, and_false, false_and, true_and, one_mul, mul_one, zero_mul, mul_zero,
      Function.comp_apply] using h

theorem sparse_even_nonleading_budget_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (v e m : ℕ) (hV : v ≤ e + 1) (hE : e ≤ m)
    (hNonleading : ¬ (v = e + 1 ∧ e = m)) :
    Tendsto (fun n => sparseEvenPatternBudget n (d n) v e m) atTop (𝓝 0) := by
  simpa only [if_neg hNonleading] using
    sparse_even_pattern_budget_tendsto d hDegree v e m hV hE

end CircularLaw
