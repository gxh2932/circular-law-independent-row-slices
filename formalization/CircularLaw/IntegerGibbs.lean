import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exponential reference weights on the integer lattice

The entropy argument compares every finite partial entropy sum with these
weights. Their total mass is controlled without assuming finite support for
the law being compared.
-/

noncomputable section

namespace CircularLaw

def integerGibbsKernel (α : ℝ) (r j : ℤ) : ℝ :=
  Real.exp (-α * |(j : ℝ) - (r : ℝ)|)

theorem integerGibbsKernel_pos (α : ℝ) (r j : ℤ) :
    0 < integerGibbsKernel α r j := Real.exp_pos _

theorem integerGibbsKernel_translate (α : ℝ) (r j : ℤ) :
    integerGibbsKernel α r j = integerGibbsKernel α 0 (j - r) := by
  simp [integerGibbsKernel, Int.cast_sub]

theorem integerGibbsKernel_nat (α : ℝ) (n : ℕ) :
    integerGibbsKernel α 0 n = Real.exp (-α) ^ n := by
  simp only [integerGibbsKernel, Int.cast_natCast, Int.cast_zero, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem integerGibbsKernel_neg_nat (α : ℝ) (n : ℕ) :
    integerGibbsKernel α 0 (-(n : ℤ)) = Real.exp (-α) ^ n := by
  rw [integerGibbsKernel, Int.cast_neg, Int.cast_natCast, Int.cast_zero, sub_zero,
    abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem integerGibbsKernel_summable {α : ℝ} (hα : 0 < α) (r : ℤ) :
    Summable (integerGibbsKernel α r) := by
  have hq : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_geometric_of_lt_one (Real.exp_nonneg (-α)) hq
  have hnat : Summable (fun n : ℕ => integerGibbsKernel α 0 n) := by
    simpa only [integerGibbsKernel_nat] using hg
  have hneg : Summable (fun n : ℕ => integerGibbsKernel α 0 (-(n : ℤ))) := by
    simpa only [integerGibbsKernel_neg_nat] using hg
  have hzero := Summable.of_nat_of_neg hnat hneg
  have hshift := (Equiv.subRight r).summable_iff.mpr hzero
  simpa only [Function.comp_def, Equiv.subRight_apply,
    ← integerGibbsKernel_translate] using hshift

theorem integerGibbsKernel_tsum {α : ℝ} (hα : 0 < α) (r : ℤ) :
    (∑' j : ℤ, integerGibbsKernel α r j) = 2 / (1 - Real.exp (-α)) - 1 := by
  have hq : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_geometric_of_lt_one (Real.exp_nonneg (-α)) hq
  have hnat : Summable (fun n : ℕ => integerGibbsKernel α 0 n) := by
    simpa only [integerGibbsKernel_nat] using hg
  have hneg : Summable (fun n : ℕ => integerGibbsKernel α 0 (-(n : ℤ))) := by
    simpa only [integerGibbsKernel_neg_nat] using hg
  calc
    (∑' j : ℤ, integerGibbsKernel α r j) =
        ∑' j : ℤ, integerGibbsKernel α 0 (j - r) :=
      tsum_congr (integerGibbsKernel_translate α r)
    _ = ∑' j : ℤ, integerGibbsKernel α 0 j :=
      (Equiv.subRight r).tsum_eq _
    _ = 2 / (1 - Real.exp (-α)) - 1 := by
      rw [hnat.tsum_of_nat_of_neg hneg]
      simp only [integerGibbsKernel_nat, integerGibbsKernel_neg_nat]
      rw [tsum_geometric_of_lt_one (Real.exp_nonneg (-α)) hq]
      simp only [integerGibbsKernel, Int.cast_zero, sub_self, abs_zero, mul_zero, Real.exp_zero]
      ring

theorem integerGibbsKernel_tsum_le {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1) (r : ℤ) :
    (∑' j : ℤ, integerGibbsKernel α r j) ≤ 4 / α := by
  let q := Real.exp (-α)
  have hqPos : 0 < q := Real.exp_pos _
  have hqOne : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - q := sub_pos.mpr hqOne
  have hprod : q * Real.exp α = 1 := by simp [q, Real.exp_neg]
  have hExp := Real.add_one_le_exp α
  have hqBound : (1 + α) * q ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hExp hqPos.le]
  have hαDen : α * (1 - q) ≤ 1 - q :=
    (mul_le_mul_of_nonneg_right hαOne hden.le).trans_eq (one_mul _)
  have hdenLower : α ≤ 2 * (1 - q) := by nlinarith
  rw [integerGibbsKernel_tsum hα]
  change 2 / (1 - q) - 1 ≤ 4 / α
  have hRatio : 2 / (1 - q) ≤ 4 / α :=
    (div_le_div_iff₀ hden hα).mpr (by nlinarith)
  linarith

theorem integerGibbsWeight_partial_mass {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1)
    (r : ℤ) (S : Finset ℤ) :
    (∑ j ∈ S, (α / 4) * integerGibbsKernel α r j) ≤ 1 := by
  have hsum := (integerGibbsKernel_summable hα r).sum_le_tsum S
    (fun j _ => (integerGibbsKernel_pos α r j).le)
  have hαFour : 0 ≤ α / 4 := by positivity
  calc
    (∑ j ∈ S, (α / 4) * integerGibbsKernel α r j) =
        (α / 4) * ∑ j ∈ S, integerGibbsKernel α r j := by rw [Finset.mul_sum]
    _ ≤ (α / 4) * (∑' j : ℤ, integerGibbsKernel α r j) :=
      mul_le_mul_of_nonneg_left hsum hαFour
    _ ≤ (α / 4) * (4 / α) :=
      mul_le_mul_of_nonneg_left (integerGibbsKernel_tsum_le hα hαOne r) hαFour
    _ = 1 := by field_simp

end CircularLaw
