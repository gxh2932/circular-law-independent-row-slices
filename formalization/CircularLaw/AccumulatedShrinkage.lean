import CircularLaw.LevelRefinement
import CircularLaw.WitnessSelection

/-!
# Accumulated factor-two level shrinkage

Actual shrinking events are counted along a finite run of nested level
sizes. Each such event contributes a factor two to the final contraction.
Double counting and the checked finite selection estimate produce many
coordinates with many contractions.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def shrinkCount (m : ℕ → ℕ) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => 2 * m (t + 1) ≤ m t)).card

theorem shrinkCount_zero (m : ℕ → ℕ) : shrinkCount m 0 = 0 := by
  simp only [shrinkCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty]

theorem shrinkCount_succ (m : ℕ → ℕ) (T : ℕ) :
    shrinkCount m (T + 1) =
      if 2 * m (T + 1) ≤ m T then shrinkCount m T + 1 else shrinkCount m T := by
  by_cases h : 2 * m (T + 1) ≤ m T <;>
    simp [shrinkCount, Finset.range_add_one, Finset.filter_insert, h]

theorem shrinkCount_le (m : ℕ → ℕ) (T : ℕ) : shrinkCount m T ≤ T :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range T)

theorem shrinkCount_power_contraction (m : ℕ → ℕ) (hMono : ∀ t, m (t + 1) ≤ m t) (T : ℕ) :
    2 ^ shrinkCount m T * m T ≤ m 0 := by
  induction T with
  | zero => simp only [shrinkCount_zero, pow_zero, one_mul, le_refl]
  | succ T ih =>
    rw [shrinkCount_succ]
    split_ifs with h
    · rw [pow_succ]
      calc
        2 ^ shrinkCount m T * 2 * m (T + 1) = 2 ^ shrinkCount m T * (2 * m (T + 1)) :=
          Nat.mul_assoc _ _ _
        _ ≤ 2 ^ shrinkCount m T * m T := Nat.mul_le_mul_left _ h
        _ ≤ m 0 := ih
    · exact (Nat.mul_le_mul_left _ (hMono T)).trans ih

theorem shrinkCount_real_contraction (m : ℕ → ℕ) (hMono : ∀ t, m (t + 1) ≤ m t) (T : ℕ) :
    (m T : ℝ) ≤ (m 0 : ℝ) * Real.rpow 2 (-(shrinkCount m T : ℝ)) := by
  have hCount := shrinkCount_power_contraction m hMono T
  have hR : (2 : ℝ) ^ shrinkCount m T * (m T : ℝ) ≤ m 0 := by exact_mod_cast hCount
  have hNeg : Real.rpow 2 (-(shrinkCount m T : ℝ)) =
      ((2 : ℝ) ^ shrinkCount m T)⁻¹ := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (shrinkCount m T : ℝ))
  rw [hNeg]
  have hp : 0 < (2 : ℝ) ^ shrinkCount m T := pow_pos (by norm_num) _
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using hR

def coordinateShrinkCount {ι : Type*} (m : ℕ → ι → ℕ) (T : ℕ) (i : ι) : ℕ :=
  shrinkCount (fun t => m t i) T

def shrinkingAt {ι : Type*} [Fintype ι] (m : ℕ → ι → ℕ) (t : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => 2 * m (t + 1) i ≤ m t i)

theorem coordinateShrinkCount_sum {ι : Type*} [Fintype ι] (m : ℕ → ι → ℕ) (T : ℕ) :
    (∑ i, coordinateShrinkCount m T i) = ∑ t ∈ Finset.range T, (shrinkingAt m t).card := by
  simp only [coordinateShrinkCount, shrinkCount, shrinkingAt, Finset.card_filter]
  rw [Finset.sum_comm]

theorem coordinateShrinkCount_sum_lower {ι : Type*} [Fintype ι]
    (m : ℕ → ι → ℕ) (T : ℕ) {B : ℝ}
    (hCount : ∀ t < T, B ≤ (shrinkingAt m t).card) :
    B * (T : ℝ) ≤ ∑ i, (coordinateShrinkCount m T i : ℝ) := by
  rw [← Nat.cast_sum, coordinateShrinkCount_sum, Nat.cast_sum]
  have h := Finset.sum_le_sum (fun t ht => hCount t (Finset.mem_range.mp ht))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using h

theorem many_coordinates_shrink {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (m : ℕ → Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hCount : ∀ t < T, B ≤ (shrinkingAt m t).card) :
    (3 / 4 : ℝ) * B ≤
      (largeWitnessRows (coordinateShrinkCount m T) (B / (4 * (n : ℝ)) * T)).card := by
  apply large_witness_rows_card_lower (coordinateShrinkCount m T)
    (by exact_mod_cast hn) (by exact_mod_cast hT) hB
  · simp only [Fintype.card_fin, le_refl]
  · intro i
    exact_mod_cast shrinkCount_le (fun t => m t i) T
  · exact coordinateShrinkCount_sum_lower m T hCount

theorem many_shrinking_coordinate_contraction {n T : ℕ}
    (m : ℕ → Fin n → ℕ) (hMono : ∀ t i, m (t + 1) i ≤ m t i)
    (hInitial : ∀ i, m 0 i ≤ n) {B : ℝ} (i : Fin n)
    (hi : i ∈ largeWitnessRows (coordinateShrinkCount m T) (B / (4 * (n : ℝ)) * T)) :
    (m T i : ℝ) ≤ (n : ℝ) * Real.rpow 2 (-(B / (4 * (n : ℝ)) * T)) := by
  have hContract := shrinkCount_real_contraction (fun t => m t i) (fun t => hMono t i) T
  have hThreshold := (mem_largeWitnessRows _ _ i).mp hi
  have hPower : Real.rpow 2 (-(coordinateShrinkCount m T i : ℝ)) ≤
      Real.rpow 2 (-(B / (4 * (n : ℝ)) * T)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hInitialR : (m 0 i : ℝ) ≤ n := by exact_mod_cast hInitial i
  exact hContract.trans ((mul_le_mul_of_nonneg_right hInitialR
    (Real.rpow_nonneg (by norm_num) _)).trans
    (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg n)))

end CircularLaw
