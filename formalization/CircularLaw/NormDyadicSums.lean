import CircularLaw.NormHeavyDyadicCover
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Finite geometric budgets for heavy coordinate levels

The sets of levels are arbitrary finite subsets of the natural numbers.
An upper threshold bounds their increasing powers, and a lower threshold
bounds their reciprocal powers, without a logarithmic level-count loss.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem finite_dyadic_power_sum_bound (S : Finset ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hS : ∀ k ∈ S, (2 : ℝ) ^ k ≤ t) : (∑ k ∈ S, (2 : ℝ) ^ k) ≤ 2 * t := by
  by_cases hNonempty : S.Nonempty
  · have hSubset : S ⊆ Finset.range (S.max' hNonempty + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S k hk))
    calc
      _ ≤ ∑ k ∈ Finset.range (S.max' hNonempty + 1), (2 : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun k _ _ => by positivity)
      _ = (2 : ℝ) ^ (S.max' hNonempty + 1) - 1 := by
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
        norm_num
      _ ≤ 2 * (2 : ℝ) ^ S.max' hNonempty := by
        rw [pow_succ]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hS _ (Finset.max'_mem S hNonempty)) (by norm_num)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hNonempty, Finset.sum_empty]
    positivity

theorem finite_dyadic_power_ratio_sum_bound (S : Finset ℕ) {t : ℝ} (ht : 0 < t)
    (hS : ∀ k ∈ S, (2 : ℝ) ^ k ≤ t) : (∑ k ∈ S, (2 : ℝ) ^ k / t) ≤ 2 := by
  rw [← Finset.sum_div]
  exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using finite_dyadic_power_sum_bound S t ht.le hS)

theorem finite_dyadic_reciprocal_sum_bound (S : Finset ℕ) (hNonempty : S.Nonempty) :
    (∑ k ∈ S, 1 / (2 : ℝ) ^ k) ≤ 2 / (2 : ℝ) ^ S.min' hNonempty := by
  have hSubset : S ⊆ Finset.Ico (S.min' hNonempty) (S.max' hNonempty + 1) := by
    intro k hk
    exact Finset.mem_Ico.mpr ⟨Finset.min'_le S k hk, Nat.lt_succ_of_le (Finset.le_max' S k hk)⟩
  calc
    _ = ∑ k ∈ S, (1 / 2 : ℝ) ^ k := by simp only [div_pow, one_pow]
    _ ≤ ∑ k ∈ Finset.Ico (S.min' hNonempty) (S.max' hNonempty + 1), (1 / 2 : ℝ) ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun k _ _ => by positivity)
    _ ≤ (1 / 2 : ℝ) ^ S.min' hNonempty / (1 - 1 / 2) :=
      geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    _ = _ := by rw [div_pow, one_pow]; ring

theorem finite_dyadic_lower_ratio_sum_bound (S : Finset ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hS : ∀ k ∈ S, t ≤ (2 : ℝ) ^ k) : (∑ k ∈ S, t / (2 : ℝ) ^ k) ≤ 2 := by
  by_cases hNonempty : S.Nonempty
  · have hMin := hS _ (Finset.min'_mem S hNonempty)
    have hPow : 0 < (2 : ℝ) ^ S.min' hNonempty := by positivity
    calc
      _ = t * ∑ k ∈ S, 1 / (2 : ℝ) ^ k := by rw [Finset.mul_sum]; simp only [mul_one_div]
      _ ≤ t * (2 / (2 : ℝ) ^ S.min' hNonempty) :=
        mul_le_mul_of_nonneg_left (finite_dyadic_reciprocal_sum_bound S hNonempty) ht
      _ ≤ _ := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hPow).mpr (by linarith)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hNonempty, Finset.sum_empty]
    norm_num

end CircularLaw
