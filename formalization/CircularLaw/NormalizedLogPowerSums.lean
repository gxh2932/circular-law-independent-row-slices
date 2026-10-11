import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite normalized logarithmic power sums

The actual sum over positive integer ranks is bounded uniformly by a
constant times the square root of the retained fraction. The proof uses
logarithm versus a small power and a telescoping inverse-square-root sum.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem log_nat_power_le_sqrt {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 0 < k) :
    Real.log x ^ k ≤ (2 * (k : ℝ)) ^ k * Real.sqrt x := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hkPos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hLog := Real.log_le_rpow_div hxPos.le (by positivity : 0 < (1 : ℝ) / (2 * k))
  have hPower := pow_le_pow_left₀ (Real.log_nonneg hx) hLog k
  have hRoot : (x ^ ((1 : ℝ) / (2 * k))) ^ k = Real.sqrt x := by
    rw [← Real.rpow_mul_natCast hxPos.le]
    have hExponent : (1 : ℝ) / (2 * k) * k = 1 / 2 := by field_simp
    rw [hExponent, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ (x ^ ((1 : ℝ) / (2 * k)) / ((1 : ℝ) / (2 * k))) ^ k := hPower
    _ = _ := by rw [div_div_eq_mul_div, div_one, mul_pow, hRoot]; ring

theorem inverse_sqrt_nat_successor_le_difference (j : ℕ) :
    (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ ≤
      2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) := by
  have hPos : 0 < Real.sqrt ((j + 1 : ℕ) : ℝ) := by positivity
  rw [← one_div]
  apply (div_le_iff₀ hPos).mpr
  have hOld := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hNew := Real.sq_sqrt (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ (j + 1 : ℕ))
  push_cast at *
  nlinarith [sq_nonneg (Real.sqrt ((j : ℝ) + 1) - Real.sqrt (j : ℝ))]

theorem sum_inverse_sqrt_nat_successors_le (L : ℕ) :
    (∑ j ∈ Finset.range L, (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹) ≤ 2 * Real.sqrt (L : ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hStep := inverse_sqrt_nat_successor_le_difference L
    exact (add_le_add ih hStep).trans_eq (by ring)

theorem normalized_log_power_range_sum_le {N : ℝ} (hN : 0 < N)
    (L : ℕ) (hL : (L : ℝ) ≤ N) {k : ℕ} (hk : 0 < k) :
    (∑ j ∈ Finset.range L, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ k) / N ≤
      2 * (2 * (k : ℝ)) ^ k * Real.sqrt ((L : ℝ) / N) := by
  have hTerms : (∑ j ∈ Finset.range L, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ k) ≤
      (2 * (k : ℝ)) ^ k * Real.sqrt N *
        (∑ j ∈ Finset.range L, (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hg : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have hgN : ((j + 1 : ℕ) : ℝ) ≤ N := by
      have hNat : j + 1 ≤ L := by simpa only [Finset.mem_range] using hj
      exact (by exact_mod_cast hNat : ((j + 1 : ℕ) : ℝ) ≤ L).trans hL
    have hRatio : 1 ≤ N / ((j + 1 : ℕ) : ℝ) := by
      apply (le_div_iff₀ hg).mpr
      simpa only [one_mul] using hgN
    have hPoint := log_nat_power_le_sqrt hRatio hk
    rw [Real.sqrt_div hN.le, div_eq_mul_inv] at hPoint
    simpa only [mul_assoc] using hPoint
  have hSum := hTerms.trans (mul_le_mul_of_nonneg_left (sum_inverse_sqrt_nat_successors_le L)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg N)))
  have hRatio : Real.sqrt N * Real.sqrt (L : ℝ) / N = Real.sqrt ((L : ℝ) / N) := by
    rw [Real.sqrt_div (Nat.cast_nonneg L), div_eq_mul_inv, div_eq_mul_inv,
      mul_comm (Real.sqrt N), mul_assoc, ← div_eq_mul_inv, Real.sqrt_div_self]
  apply (div_le_div_of_nonneg_right hSum hN.le).trans_eq
  calc
    _ = 2 * (2 * (k : ℝ)) ^ k * (Real.sqrt N * Real.sqrt (L : ℝ) / N) := by ring
    _ = _ := by rw [hRatio]

theorem normalized_log_power_subset_sum_le {N : ℝ} (hN : 0 < N)
    (L : ℕ) (hL : (L : ℝ) ≤ N) (S : Finset ℕ) (hS : S ⊆ Finset.range L)
    {k : ℕ} (hk : 0 < k) :
    (∑ j ∈ S, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ k) / N ≤
      2 * (2 * (k : ℝ)) ^ k * Real.sqrt ((L : ℝ) / N) := by
  apply (div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hS ?_) hN.le).trans
    (normalized_log_power_range_sum_le hN L hL hk)
  intro j hj _
  have hg : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hgN : ((j + 1 : ℕ) : ℝ) ≤ N := by
    have hNat : j + 1 ≤ L := by simpa only [Finset.mem_range] using hj
    exact (by exact_mod_cast hNat : ((j + 1 : ℕ) : ℝ) ≤ L).trans hL
  exact pow_nonneg (Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa using hgN))) k

end CircularLaw
