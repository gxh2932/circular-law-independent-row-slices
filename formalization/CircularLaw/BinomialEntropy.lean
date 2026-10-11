import CircularLaw.RowWitnessBounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Entropy bounds for binomial coefficients

The weighted binomial theorem and `1+x <= exp(x)` give the finite
`choose(n,t) <= (e*n/t)^t` estimate needed for the witness union bound.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem binomial_term_le_power {n t : ℕ} (htn : t ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    (n.choose t : ℝ) * x ^ t ≤ (1 + x) ^ n := by
  rw [add_comm (1 : ℝ) x, add_pow]
  have h := Finset.single_le_sum
    (f := fun m => x ^ m * (1 : ℝ) ^ (n - m) * (n.choose m : ℝ))
    (fun _ _ => by positivity) (Finset.mem_range.mpr (by omega : t < n + 1))
  simpa only [one_pow, mul_one, mul_comm] using h

theorem choose_le_exp_ratio_power {n t : ℕ} (hn : 0 < n) (ht : 0 < t) (htn : t ≤ n) :
    (n.choose t : ℝ) ≤ (Real.exp 1 * n / t) ^ t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hx : (0 : ℝ) < (t : ℝ) / n := div_pos htR hnR
  have hTerm := binomial_term_le_power htn hx.le
  have hExponential : (1 + (t : ℝ) / n) ^ n ≤ Real.exp (t : ℝ) := by
    calc
      _ ≤ (Real.exp ((t : ℝ) / n)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by
          have h := Real.add_one_le_exp ((t : ℝ) / n)
          linarith) n
      _ = _ := by rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hnR.ne']
  have h := hTerm.trans hExponential
  have hDiv := (le_div_iff₀ (pow_pos hx t)).mpr h
  calc
    _ ≤ Real.exp (t : ℝ) / ((t : ℝ) / n) ^ t := hDiv
    _ = (Real.exp 1 / ((t : ℝ) / n)) ^ t := by
      rw [div_pow (Real.exp 1) ((t : ℝ) / n), ← Real.exp_nat_mul, mul_one]
    _ = _ := by congr 1; field_simp

theorem choose_le_exp_entropy {n t : ℕ} (hn : 0 < n) (ht : 0 < t) (htn : t ≤ n) :
    (n.choose t : ℝ) ≤ Real.exp ((t : ℝ) * Real.log (Real.exp 1 * n / t)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hBase : (0 : ℝ) < Real.exp 1 * n / t := by positivity
  apply (choose_le_exp_ratio_power hn ht htn).trans_eq
  rw [Real.exp_nat_mul, Real.exp_log hBase]

theorem choose_pair_entropy {n s t : ℕ} (hn : 0 < n) (ht : 0 < t) (htn : t ≤ n) :
    (n.choose t : ℝ) * t.choose s ≤
      Real.exp ((t : ℝ) * (Real.log (Real.exp 1 * n / t) + Real.log 2)) := by
  have hSecond : (t.choose s : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast Nat.choose_le_two_pow t s
  calc
    _ ≤ Real.exp ((t : ℝ) * Real.log (Real.exp 1 * n / t)) * (2 : ℝ) ^ t :=
      mul_le_mul (choose_le_exp_entropy hn ht htn) hSecond
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [show (2 : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log 2) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)], ← Real.exp_add]
      congr 1
      ring

end CircularLaw
