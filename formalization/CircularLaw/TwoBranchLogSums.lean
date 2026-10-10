import CircularLaw.NormalizedLogPowerSums
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Summing the actual two-branch logarithmic schedule

The small branch ends at the literal integer floor of N*theta. Both
branches are summed over their actual rank sets. No continuum or
asymptotic replacement of the integer cutoff is used.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normalizedTwoBranchLogIncrement (B θ N : ℝ) (g : ℕ) : ℝ :=
  if (g : ℝ) ≤ N * θ then B * Real.log (N / g) ^ 8 / N
  else Real.log (N / g) ^ 2 / N

theorem normalized_two_branch_log_increment_nonneg {B θ N : ℝ}
    (hB : 0 ≤ B) (hN : 0 < N) (g : ℕ) :
    0 ≤ normalizedTwoBranchLogIncrement B θ N g := by
  unfold normalizedTwoBranchLogIncrement
  split_ifs <;> positivity

theorem normalized_two_branch_log_sum_le {B θ N : ℝ}
    (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hθOne : θ ≤ 1) (hN : 0 < N)
    (L : ℕ) (hL : (L : ℝ) ≤ N) :
    (∑ j ∈ Finset.range L, normalizedTwoBranchLogIncrement B θ N (j + 1)) ≤
      32 * Real.sqrt ((L : ℝ) / N) + 2 * B * (16 : ℝ) ^ 8 * Real.sqrt θ := by
  let S := (Finset.range L).filter (fun j => ((j + 1 : ℕ) : ℝ) ≤ N * θ)
  let T := (Finset.range L).filter (fun j => ¬ ((j + 1 : ℕ) : ℝ) ≤ N * θ)
  let M : ℕ := ⌊N * θ⌋₊
  have hM : (M : ℝ) ≤ N :=
    (Nat.floor_le (mul_nonneg hN.le hθ)).trans (mul_le_of_le_one_right hN.le hθOne)
  have hMFraction : (M : ℝ) / N ≤ θ := by
    apply (div_le_iff₀ hN).mpr
    simpa only [M, mul_comm] using Nat.floor_le (mul_nonneg hN.le hθ)
  have hS : S ⊆ Finset.range M := by
    intro j hj
    have hRank := (Finset.mem_filter.mp hj).2
    have hFloor : j + 1 ≤ M := Nat.le_floor hRank
    exact Finset.mem_range.mpr (by omega)
  have hT : T ⊆ Finset.range L := Finset.filter_subset _ _
  have hSmall : (∑ j ∈ S, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ 8) / N ≤
      2 * (16 : ℝ) ^ 8 * Real.sqrt ((M : ℝ) / N) := by
    convert normalized_log_power_subset_sum_le hN M hM S hS (by decide : 0 < (8 : ℕ)) using 1
    norm_num
  have hSmallTheta : (∑ j ∈ S, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ 8) / N ≤
      2 * (16 : ℝ) ^ 8 * Real.sqrt θ :=
    hSmall.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hMFraction) (by positivity))
  have hLarge : (∑ j ∈ T, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ 2) / N ≤
      32 * Real.sqrt ((L : ℝ) / N) := by
    convert normalized_log_power_subset_sum_le hN L hL T hT (by decide : 0 < (2 : ℕ)) using 1
    norm_num
  have hSplit : (∑ j ∈ Finset.range L, normalizedTwoBranchLogIncrement B θ N (j + 1)) =
      B * ((∑ j ∈ S, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ 8) / N) +
        (∑ j ∈ T, Real.log (N / ((j + 1 : ℕ) : ℝ)) ^ 2) / N := by
    unfold normalizedTwoBranchLogIncrement S T
    rw [Finset.sum_ite]
    simp only [← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [hSplit]
  exact (add_le_add (mul_le_mul_of_nonneg_left hSmallTheta hB) hLarge).trans_eq (by ring)

end CircularLaw
