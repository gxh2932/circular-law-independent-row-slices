import CircularLaw.RegularizedRowLogRemoval
import CircularLaw.SquareSingularDeterminant

/-!
# Log volumes of actual row restrictions

Row deletion interlacing transfers the square smallest singular-value
lower bound to every retained row. This supplies the exact regularization
removal estimate for the retained matrix, and compares its log volume
with the leading and trailing square singular-value sums.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem matrix_row_log_volume_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    matrixRowLogVolume A = ∑ j : Fin m, Real.log (orderedRectangularSingularValues A j) := by
  let e : Fin m ≃ Fin (Fintype.card (Fin m)) := finCongr (Fintype.card_fin m).symm
  rw [matrixRowLogVolume, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem row_restriction_singular_value_lower_bound {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n) (hn : 0 < n)
    {τ : ℝ} (hSmallest : τ ≤ orderedSquareSingularValues A ⟨n - 1, by omega⟩) :
    ∀ j, τ ≤ orderedMatrixSingularValues (matrixRowRestriction A f) j := by
  have hmn := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at hmn
  intro j
  let i : Fin m := ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
  let l : Fin n := ⟨i.val + (n - m), by omega⟩
  have hLast : l ≤ (⟨n - 1, by omega⟩ : Fin n) := by
    change l.val ≤ n - 1
    exact Nat.le_pred_of_lt l.isLt
  have h := ambient_singular_value_le_row_restriction A f i l rfl
  exact hSmallest.trans ((orderedSquareSingularValues_antitone A hLast).trans h)

theorem row_restriction_regularized_log_removal {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 < τ)
    (hSmallest : τ ≤ orderedSquareSingularValues A ⟨n - 1, by omega⟩) :
    0 ≤ (regularizedRowPotential (matrixRowRestriction A f) (τ / n) -
      matrixRowLogVolume (matrixRowRestriction A f)) / n ∧
    (regularizedRowPotential (matrixRowRestriction A f) (τ / n) -
      matrixRowLogVolume (matrixRowRestriction A f)) / n ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hmn := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at hmn
  exact regularized_row_log_removal_at_tau_over_dimension _ hn hmn hτ
    (row_restriction_singular_value_lower_bound A f hn hSmallest)

theorem row_restriction_log_volume_interlace {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n)
    (hmn : m ≤ n) (hDet : A.det ≠ 0) :
    (∑ i : Fin m, Real.log (orderedSquareSingularValues A
      ⟨i.val + (n - m), by omega⟩)) ≤ matrixRowLogVolume (matrixRowRestriction A f) ∧
    matrixRowLogVolume (matrixRowRestriction A f) ≤
      ∑ i : Fin m, Real.log (orderedSquareSingularValues A (Fin.castLE hmn i)) := by
  rw [matrix_row_log_volume_fin]
  have hPositive := square_singular_values_pos_of_det_ne_zero A hDet
  constructor
  · apply Finset.sum_le_sum
    intro i _
    let l : Fin n := ⟨i.val + (n - m), by omega⟩
    exact Real.log_le_log (hPositive l)
      (ambient_singular_value_le_row_restriction A f i l rfl)
  · apply Finset.sum_le_sum
    intro i _
    let l : Fin n := ⟨i.val + (n - m), by omega⟩
    have hLower := ambient_singular_value_le_row_restriction A f i l rfl
    exact Real.log_le_log ((hPositive l).trans_le hLower)
      (row_restriction_singular_value_le A f i (Fin.castLE hmn i) rfl)

end CircularLaw
