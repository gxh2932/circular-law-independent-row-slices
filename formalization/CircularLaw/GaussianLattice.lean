import CircularLaw.TruncatedSymmetrization
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Gaussian lattice bounds

A sum-integral comparison bounds Gaussian samples on the positive integers.
Combining the two tails gives a bound for the integer lattice, used to control
the Gaussian weights of the periods of a cosine kernel.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace CircularLaw

theorem gaussian_antitoneOn_nonneg {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Ici 0) := by
  intro x hx y _ hxy
  apply Real.exp_le_exp.mpr
  have hSq := pow_le_pow_left₀ hx hxy 2
  nlinarith

theorem gaussian_positive_nat_partial_sum_le {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.exp (-c * ((n : ℝ) + 1) ^ 2)) ≤ Real.sqrt (Real.pi / c) := by
  have hAnti : AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Icc 0 (N : ℝ)) :=
    (gaussian_antitoneOn_nonneg hc.le).mono (fun _ hx => hx.1)
  have h := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := N)
    (by simpa only [zero_add] using hAnti)
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h
  have hInt := setIntegral_le_integral (s := Ioc (0 : ℝ) (N : ℝ))
    (integrable_exp_neg_mul_sq hc) (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg N), integral_gaussian] at hInt
  exact h.trans hInt

theorem gaussian_positive_nat_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * ((n : ℝ) + 1) ^ 2)) :=
  summable_of_sum_range_le (fun _ => (Real.exp_pos _).le)
    (gaussian_positive_nat_partial_sum_le hc)

theorem gaussian_positive_nat_tsum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * ((n : ℝ) + 1) ^ 2)) ≤ Real.sqrt (Real.pi / c) :=
  Real.tsum_le_of_sum_range_le (fun _ => (Real.exp_pos _).le)
    (gaussian_positive_nat_partial_sum_le hc)

theorem gaussian_integer_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  have hPos : Summable (fun n : ℕ => Real.exp (-c * ((n : ℤ) + 1 : ℤ) ^ 2)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using gaussian_positive_nat_summable hc
  have hNeg : Summable (fun n : ℕ => Real.exp (-c * (-((n : ℤ) + 1) : ℤ) ^ 2)) := by
    simpa only [Int.cast_neg, neg_sq] using hPos
  exact Summable.of_add_one_of_neg_add_one
    (f := fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) hPos hNeg

theorem gaussian_integer_tsum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)) ≤ 1 + 2 * Real.sqrt (Real.pi / c) := by
  have hPos : Summable (fun n : ℕ => Real.exp (-c * ((n : ℤ) + 1 : ℤ) ^ 2)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using gaussian_positive_nat_summable hc
  have hNeg : Summable (fun n : ℕ => Real.exp (-c * (-((n : ℤ) + 1) : ℤ) ^ 2)) := by
    simpa only [Int.cast_neg, neg_sq] using hPos
  rw [tsum_of_add_one_of_neg_add_one
    (f := fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) hPos hNeg]
  simp only [Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero,
    Int.cast_neg, neg_sq, Int.cast_add, Int.cast_natCast, Int.cast_one]
  have h := gaussian_positive_nat_tsum_le hc
  linarith

theorem translated_integer_sq_lower (n : ℤ) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (n : ℝ) ^ 2 / 4 ≤ (x + n) ^ 2 := by
  by_cases hn : n = 0
  · simp only [hn, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero]
    exact sq_nonneg _
  · have hN : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hTriangle : |(n : ℝ)| ≤ |x + n| + |x| := by
      simpa only [add_sub_cancel_left] using (abs_sub (x + (n : ℝ)) x)
    have hLower : |(n : ℝ)| / 2 ≤ |x + n| := by linarith
    have hSq := pow_le_pow_left₀ (by positivity : 0 ≤ |(n : ℝ)| / 2) hLower 2
    simpa only [div_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hSq

end CircularLaw
