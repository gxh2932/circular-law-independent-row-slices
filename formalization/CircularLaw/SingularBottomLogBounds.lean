import CircularLaw.BottomLogGeometry
import CircularLaw.IntermediateSingularValueTheorem
import CircularLaw.SquareSingularSecondMoment

/-!
# The smallest and intermediate scales in the bottom logarithmic tail

The exact bottom q0 indices pay the smallest-singular-value cost. Every
other bottom index pays the checked intermediate scale. No relation
between the deletion count r and q0 is needed for this upper bound.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem negative_log_le_of_exp_lower {s L : ℝ} (hL : 0 ≤ L)
    (hLower : Real.exp (-L) ≤ s) : max (-Real.log s) 0 ≤ L := by
  have hLog := Real.log_le_log (Real.exp_pos (-L)) hLower
  rw [Real.log_exp] at hLog
  exact max_le (by linarith) hL

theorem square_bottom_negative_log_bound_of_minimum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (hMinimum : ∀ j, τ ≤ orderedSquareSingularValues A j) :
    empiricalBottomNegativeLog (squareSingularValuesNNReal A) r ≤
      (r : ℝ) * max (-Real.log τ) 0 / n := by
  have hPoint (j : Fin n) : hermitizationNegativeLog (squareSingularValuesNNReal A j) ≤
      max (-Real.log τ) 0 := by
    exact max_le_max (neg_le_neg (Real.log_le_log hτ (hMinimum j))) le_rfl
  have hCard : ((bottomLogIndices n r).card : ℝ) ≤ r :=
    by exact_mod_cast bottomLogIndices_card_le n r
  unfold empiricalBottomNegativeLog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ _j ∈ bottomLogIndices n r, max (-Real.log τ) 0 :=
      Finset.sum_le_sum (fun j _ => hPoint j)
    _ = ((bottomLogIndices n r).card : ℝ) * max (-Real.log τ) 0 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hCard (le_max_right _ _)

theorem square_bottom_negative_log_bound_of_two_scales {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) (hq : q < n)
    {τ L : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L)
    (hMinimum : ∀ j, τ ≤ orderedSquareSingularValues A j)
    (hIntermediate : Real.exp (-L) ≤ orderedSquareSingularValues A ⟨n - q - 1, by omega⟩) :
    empiricalBottomNegativeLog (squareSingularValuesNNReal A) r ≤
      ((q : ℝ) * max (-Real.log τ) 0 + (r : ℝ) * L) / n := by
  let T := bottomLogIndices n q
  let S := bottomLogIndices n r
  let b := max (-Real.log τ) 0
  let w : Fin n → ℝ := fun j => if j ∈ T then b else 0
  have hb : 0 ≤ b := le_max_right _ _
  have hw (j : Fin n) : 0 ≤ w j := by dsimp [w]; split_ifs <;> positivity
  have hPoint (j : Fin n) : hermitizationNegativeLog (squareSingularValuesNNReal A j) ≤ w j + L := by
    by_cases hj : j ∈ T
    · have hLog := Real.log_le_log hτ (hMinimum j)
      have hB := max_le_max (neg_le_neg hLog) (le_refl (0 : ℝ))
      change max (-Real.log (orderedSquareSingularValues A j)) 0 ≤ _
      rw [show w j = b from if_pos hj]
      exact hB.trans (le_add_of_nonneg_right hL)
    · have hjIndex : j ≤ (⟨n - q - 1, by omega⟩ : Fin n) := by
        have hjNot : ¬n - q ≤ j.val := by
          simpa only [T, bottomLogIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hj
        change j.val ≤ n - q - 1
        omega
      have hLower := hIntermediate.trans (orderedSquareSingularValues_antitone A hjIndex)
      change max (-Real.log (orderedSquareSingularValues A j)) 0 ≤ _
      rw [show w j = 0 from if_neg hj, zero_add]
      exact negative_log_le_of_exp_lower hL hLower
  have hWeightSum : (∑ j : Fin n, w j) = (T.card : ℝ) * b := by
    simp [w]
  have hSCard : (S.card : ℝ) ≤ r := by exact_mod_cast bottomLogIndices_card_le n r
  have hTCard : (T.card : ℝ) ≤ q := by exact_mod_cast bottomLogIndices_card_le n q
  have hSum : (∑ j ∈ S, hermitizationNegativeLog (squareSingularValuesNNReal A j)) ≤
      (q : ℝ) * b + (r : ℝ) * L := by
    calc
      _ ≤ ∑ j ∈ S, (w j + L) := Finset.sum_le_sum (fun j _ => hPoint j)
      _ = (∑ j ∈ S, w j) + (S.card : ℝ) * L := by simp [Finset.sum_add_distrib]
      _ ≤ (∑ j : Fin n, w j) + (r : ℝ) * L :=
        add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun j _ _ => hw j)) (mul_le_mul_of_nonneg_right hSCard hL)
      _ = (T.card : ℝ) * b + (r : ℝ) * L := by rw [hWeightSum]
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hTCard hb) _
  exact div_le_div_of_nonneg_right hSum (Nat.cast_nonneg n)

theorem row_slice_bottom_log_bound_on_intermediate_event {n d : ℕ}
    (rows : RowSliceMatrix n d) (ζ : ℂ) (r : ℕ) {τ R : ℝ}
    (hτ : 0 < τ) (hR : 0 ≤ R)
    (hMinimum : ∀ j, τ ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j)
    (hIntermediate : IntermediateSingularValueEvent ζ R rows) :
    empiricalBottomNegativeLog (squareSingularValuesNNReal (fullShiftedSliceMatrix ζ rows)) r ≤
      ((intermediateDeletionCount n d : ℝ) * max (-Real.log τ) 0 +
        (r : ℝ) * R * Real.rpow (d : ℝ) (1 / 96)) / n := by
  obtain ⟨hq, hScale⟩ := hIntermediate
  have hScale' : Real.exp (-(R * Real.rpow (d : ℝ) (1 / 96))) ≤
      orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows)
        ⟨n - intermediateDeletionCount n d - 1, by omega⟩ := by
    simpa only [neg_mul, intermediateSingularIndex] using hScale
  simpa only [intermediateSingularIndex, mul_assoc] using
    square_bottom_negative_log_bound_of_two_scales _ r hq hτ
      (mul_nonneg hR (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hMinimum hScale'

end CircularLaw
