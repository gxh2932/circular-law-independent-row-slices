import CircularLaw.BernoulliHermitizationPositiveTail
import CircularLaw.RowRestrictionDeterminantTails

/-!
# Normalized determinant error with the literal logarithmic tails

The bottom-index sum is exactly the finite tail in the row interlacing
bound. A positive square singular lower bound ensures invertibility.
These identities apply before any probabilistic limiting argument.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators NNReal

namespace CircularLaw

theorem bottomLogIndices_sum_eq_fin_tail {n r : ℕ} (hrn : r ≤ n) (g : Fin n → ℝ) :
    (∑ j ∈ bottomLogIndices n r, g j) =
      ∑ j : Fin r, g ⟨n - r + j.val, by have hj := j.isLt; omega⟩ := by
  let rank : (j : Fin n) → j ∈ bottomLogIndices n r → Fin r := fun j hj =>
    ⟨j.val - (n - r), by
      have hIndex := (Finset.mem_filter.mp hj).2
      have hn := j.isLt
      omega⟩
  apply Finset.sum_bij rank
  · intro j hj
    exact Finset.mem_univ _
  · intro i hi j hj hEq
    apply Fin.ext
    have hVal := congrArg Fin.val hEq
    have hiIndex := (Finset.mem_filter.mp hi).2
    have hjIndex := (Finset.mem_filter.mp hj).2
    dsimp only [rank] at hVal
    omega
  · intro k _
    let j : Fin n := ⟨n - r + k.val, by have hk := k.isLt; omega⟩
    have hj : j ∈ bottomLogIndices n r := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by dsimp [j]; omega⟩
    refine ⟨j, hj, ?_⟩
    apply Fin.ext
    dsimp only [rank, j]
    omega
  · intro j hj
    apply congrArg g
    apply Fin.ext
    have hIndex := (Finset.mem_filter.mp hj).2
    dsimp only [rank]
    omega

theorem square_det_ne_zero_of_singular_lower_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {τ : ℝ} (hτ : 0 < τ)
    (hLower : ∀ j, τ ≤ orderedSquareSingularValues A j) : A.det ≠ 0 := by
  intro hDet
  obtain ⟨j, hj⟩ := (square_singular_has_zero_iff_det_zero A).mpr hDet
  have hValue : orderedSquareSingularValues A j = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) hj
  have h := hLower j
  rw [hValue] at h
  linarith

theorem row_restriction_normalized_det_error_bound {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n)
    (hmn : m ≤ n) (hDet : A.det ≠ 0) :
    |(Real.log ‖A.det‖ - matrixRowLogVolume (matrixRowRestriction A f)) / n| ≤
      squareTopPositiveLog A (n - m) + empiricalBottomNegativeLog (squareSingularValuesNNReal A) (n - m) := by
  have h := div_le_div_of_nonneg_right
    (row_restriction_log_det_volume_abs_bound A f hmn hDet) (Nat.cast_nonneg n)
  rw [add_div] at h
  have hBottom : (∑ j : Fin (n - m), max (-Real.log (orderedSquareSingularValues A
      ⟨m + j.val, by have hj := j.isLt; omega⟩)) 0) / n =
      empiricalBottomNegativeLog (squareSingularValuesNNReal A) (n - m) := by
    unfold empiricalBottomNegativeLog
    rw [bottomLogIndices_sum_eq_fin_tail (Nat.sub_le n m)]
    simp only [Nat.sub_sub_self hmn]
    rfl
  rw [← square_top_positive_log_eq_of_le A (Nat.sub_le n m), hBottom] at h
  have hnReal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simpa only [abs_div, abs_of_nonneg hnReal] using h

end CircularLaw
