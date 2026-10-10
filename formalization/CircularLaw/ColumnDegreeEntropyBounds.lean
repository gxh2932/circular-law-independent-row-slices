import CircularLaw.GraphGrowthBudget
import CircularLaw.BinomialEntropy
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Entropy bounds for the uniform column-degree event

The fixed-set exponential tail absorbs the number of column subsets.
The constant eight leaves both a cubic ambient-size loss and a geometric
degree loss, so summing all nonempty cardinalities costs at most one.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem choose_le_ambient_log_entropy {N m ell : ℕ}
    (hmN : m ≤ N) (hell : 0 < ell) (hellm : ell ≤ m) :
    (m.choose ell : ℝ) ≤ Real.exp ((ell : ℝ) * (1 + Real.log ((N : ℝ) / ell))) := by
  have hm : 0 < m := by omega
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hePos : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hLog : Real.log ((m : ℝ) / ell) ≤ Real.log ((N : ℝ) / ell) :=
    Real.log_le_log (div_pos hmPos hePos)
      (div_le_div_of_nonneg_right (by exact_mod_cast hmN) hePos.le)
  have hLogEq : Real.log (Real.exp 1 * m / ell) = 1 + Real.log ((m : ℝ) / ell) := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne' (div_pos hmPos hePos).ne', Real.log_exp]
  apply (choose_le_exp_entropy hm hell hellm).trans
  apply Real.exp_le_exp.mpr
  rw [hLogEq]
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hLog) hePos.le

theorem positive_card_log_degree_lower {N ell : ℕ}
    (hell : 0 < ell) (hellN : ell ≤ N) {d : ℝ} (hd : 1 ≤ d) :
    Real.log (N : ℝ) ≤ (ell : ℝ) * (d + Real.log ((N : ℝ) / ell)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hOne : 1 ≤ (ell : ℝ) := by exact_mod_cast hell
  have hL : 0 ≤ Real.log ((N : ℝ) / ell) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ he).mpr
    simpa only [one_mul] using (show (ell : ℝ) ≤ N by exact_mod_cast hellN)
  have hMono := logarithmic_degree_budget_mono hn (d := 0) (by norm_num)
    (by norm_num : (0 : ℝ) < 1) he hOne hL
  simp only [div_one, zero_add, one_mul] at hMono
  nlinarith [mul_le_mul_of_nonneg_left hd he.le]

theorem column_degree_entropy_exponent_le {N ell : ℕ}
    (hell : 0 < ell) (hellN : ell ≤ N) {d : ℝ} (hd : 1 ≤ d) :
    (ell : ℝ) * (1 + Real.log ((N : ℝ) / ell)) +
        (ell : ℝ) * d * (Real.exp 1 - 1) -
          8 * ell * (d + Real.log ((N : ℝ) / ell)) ≤
      -3 * Real.log (N : ℝ) - 2 * d * ell := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hL : 0 ≤ Real.log ((N : ℝ) / ell) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ he).mpr
    simpa only [one_mul] using (show (ell : ℝ) ≤ N by exact_mod_cast hellN)
  have hMean := mul_le_mul_of_nonneg_left
    (sub_le_sub_right Real.exp_one_lt_three.le 1) (mul_nonneg he.le (by linarith : 0 ≤ d))
  have hEntropy := positive_card_log_degree_lower hell hellN hd
  nlinarith [mul_le_mul_of_nonneg_left hd he.le, mul_nonneg he.le hL]

theorem geometric_positive_powers_sum_le_one {q : ℝ} (hq : 0 ≤ q) (hqHalf : q ≤ 1 / 2) (L : ℕ) :
    (∑ j ∈ Finset.range L, q ^ (j + 1)) ≤ 1 := by
  have hSharp : ∀ m : ℕ, (∑ j ∈ Finset.range m, q ^ (j + 1)) ≤ 1 - q ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hPower := mul_le_mul_of_nonneg_right hqHalf (pow_nonneg hq m)
      linarith
  exact (hSharp L).trans (sub_le_self _ (pow_nonneg hq L))

theorem sum_positive_degree_exponentials_le_one {d : ℝ} (hd : 1 ≤ d) (L : ℕ) :
    (∑ j ∈ Finset.range L, Real.exp (-2 * d * ((j + 1 : ℕ) : ℝ))) ≤ 1 := by
  have hHalf : Real.exp (-2 * d) ≤ 1 / 2 := by
    rw [show -2 * d = -(2 * d) by ring, Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hExp := Real.add_one_le_exp (2 * d)
    linarith
  have hPoint (j : ℕ) : Real.exp (-2 * d * ((j + 1 : ℕ) : ℝ)) = (Real.exp (-2 * d)) ^ (j + 1) := by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [hPoint]
  exact geometric_positive_powers_sum_le_one (Real.exp_pos _).le hHalf L

end CircularLaw
