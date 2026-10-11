import CircularLaw.EmpiricalNegativeLogUI

/-!
# The literal bottom-row logarithmic sum

Indices are zero-based, so the bottom `r` values have `n-r ≤ j.val`.
Their count is at most `r`, including totalized dimensions and oversized
deletion counts. Splitting at a threshold gives the source bottom-tail bound.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

def bottomLogIndices (n r : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => n - r ≤ j.val)

theorem bottomLogIndices_card_le (n r : ℕ) : (bottomLogIndices n r).card ≤ r := by
  let f : {j : Fin n // n - r ≤ j.val} → Fin r :=
    fun j => ⟨j.val.val - (n - r), by have h := j.val.isLt; have h' := j.property; omega⟩
  have hInj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    have hVal := congrArg Fin.val h
    have hi := i.property
    have hj := j.property
    dsimp only [f] at hVal
    omega
  have hCard := Fintype.card_le_of_injective f hInj
  simpa only [Fintype.card_subtype, Fintype.card_fin, bottomLogIndices] using hCard

def empiricalBottomNegativeLog {n : ℕ} (s : Fin n → ℝ≥0) (r : ℕ) : ℝ :=
  (∑ j ∈ bottomLogIndices n r, hermitizationNegativeLog (s j)) / n

def empiricalBottomHasZero {n : ℕ} (s : Fin n → ℝ≥0) (r : ℕ) : Prop :=
  ∃ j ∈ bottomLogIndices n r, s j = 0

def EmpiricalBottomLogTailEvent {n : ℕ} (s : Fin n → ℝ≥0) (r : ℕ) (ε : ℝ) : Prop :=
  empiricalBottomHasZero s r ∨ ε < empiricalBottomNegativeLog s r

theorem empirical_bottom_negative_log_bound {n : ℕ} (s : Fin n → ℝ≥0) (r : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    empiricalBottomNegativeLog s r ≤ T * ((r : ℝ) / n) + empiricalNegativeLogTail s T := by
  let tail : Fin n → ℝ := fun j =>
    if T < hermitizationNegativeLog (s j) then hermitizationNegativeLog (s j) else 0
  have hTail0 (j : Fin n) : 0 ≤ tail j := by
    dsimp [tail]
    split_ifs
    · exact le_max_right _ _
    · exact le_refl _
  have hPoint (j : Fin n) : hermitizationNegativeLog (s j) ≤ T + tail j := by
    dsimp [tail]
    split_ifs with h
    · linarith
    · simpa only [add_zero] using le_of_not_gt h
  have hTailSum : (∑ j ∈ bottomLogIndices n r, tail j) ≤ ∑ j, tail j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hTail0 j)
  have hCard : ((bottomLogIndices n r).card : ℝ) ≤ r := by
    exact_mod_cast bottomLogIndices_card_le n r
  have hSum : (∑ j ∈ bottomLogIndices n r, hermitizationNegativeLog (s j)) ≤
      (r : ℝ) * T + ∑ j, tail j := by
    calc
      _ ≤ ∑ j ∈ bottomLogIndices n r, (T + tail j) := Finset.sum_le_sum (fun j _ => hPoint j)
      _ = ((bottomLogIndices n r).card : ℝ) * T + ∑ j ∈ bottomLogIndices n r, tail j := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hCard hT) hTailSum
  calc
    _ ≤ ((r : ℝ) * T + ∑ j, tail j) / n := div_le_div_of_nonneg_right hSum (Nat.cast_nonneg _)
    _ = _ := by
      unfold empiricalNegativeLogTail empiricalNonnegativeMean finiteMean
      simp only [Fintype.card_fin]
      dsimp only [tail]
      ring

end CircularLaw
