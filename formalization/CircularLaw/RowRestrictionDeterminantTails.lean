import CircularLaw.RowRestrictionLogVolume
import Mathlib.Algebra.BigOperators.Fin

/-!
# Square determinant versus retained row volume

The exact deletion count determines both tails. Interlacing bounds the
log-volume error by the top positive and bottom negative logarithms of
the original square matrix, with no rounding or limiting argument.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem fin_sum_split_retained_rows {m n : ℕ} (hmn : m ≤ n) (g : Fin n → ℝ) :
    (∑ j, g j) = (∑ j : Fin m, g (Fin.castLE hmn j)) +
      ∑ j : Fin (n - m), g ⟨m + j.val, by omega⟩ := by
  let e : Fin (m + (n - m)) ≃ Fin n := finCongr (Nat.add_sub_of_le hmn)
  rw [← e.sum_comp, Fin.sum_univ_add]
  congr 1

theorem fin_sum_split_deleted_rows {m n : ℕ} (hmn : m ≤ n) (g : Fin n → ℝ) :
    (∑ j, g j) = (∑ j : Fin (n - m), g (Fin.castLE (Nat.sub_le n m) j)) +
      ∑ j : Fin m, g ⟨j.val + (n - m), by omega⟩ := by
  let e : Fin ((n - m) + m) ≃ Fin n := finCongr (Nat.sub_add_cancel hmn)
  rw [← e.sum_comp, Fin.sum_univ_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg g
  apply Fin.ext
  exact Nat.add_comm _ _

theorem row_restriction_log_det_volume_tail_bounds {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n)
    (hmn : m ≤ n) (hDet : A.det ≠ 0) :
    -(∑ j : Fin (n - m), max (-Real.log (orderedSquareSingularValues A
      ⟨m + j.val, by omega⟩)) 0) ≤ Real.log ‖A.det‖ - matrixRowLogVolume (matrixRowRestriction A f) ∧
    Real.log ‖A.det‖ - matrixRowLogVolume (matrixRowRestriction A f) ≤
      ∑ j : Fin (n - m), max (Real.log (orderedSquareSingularValues A
        (Fin.castLE (Nat.sub_le n m) j))) 0 := by
  rw [square_log_norm_det_eq_singular_log_sum A hDet]
  have hInterlace := row_restriction_log_volume_interlace A f hmn hDet
  constructor
  · have hSum := fin_sum_split_retained_rows hmn (fun j => Real.log (orderedSquareSingularValues A j))
    have hTail : -(∑ j : Fin (n - m), max (-Real.log (orderedSquareSingularValues A
        ⟨m + j.val, by omega⟩)) 0) ≤
        ∑ j : Fin (n - m), Real.log (orderedSquareSingularValues A ⟨m + j.val, by omega⟩) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro j _
      have h := le_max_left (-Real.log (orderedSquareSingularValues A ⟨m + j.val, by omega⟩)) 0
      linarith
    linarith [hInterlace.2]
  · have hSum := fin_sum_split_deleted_rows hmn (fun j => Real.log (orderedSquareSingularValues A j))
    have hTop : (∑ j : Fin (n - m), Real.log (orderedSquareSingularValues A
        (Fin.castLE (Nat.sub_le n m) j))) ≤
        ∑ j : Fin (n - m), max (Real.log (orderedSquareSingularValues A
          (Fin.castLE (Nat.sub_le n m) j))) 0 :=
      Finset.sum_le_sum (fun j _ => le_max_left _ _)
    linarith [hInterlace.1]

theorem row_restriction_log_det_volume_abs_bound {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin m ↪ Fin n)
    (hmn : m ≤ n) (hDet : A.det ≠ 0) :
    |Real.log ‖A.det‖ - matrixRowLogVolume (matrixRowRestriction A f)| ≤
      (∑ j : Fin (n - m), max (Real.log (orderedSquareSingularValues A
        (Fin.castLE (Nat.sub_le n m) j))) 0) +
      ∑ j : Fin (n - m), max (-Real.log (orderedSquareSingularValues A
        ⟨m + j.val, by omega⟩)) 0 := by
  have hBounds := row_restriction_log_det_volume_tail_bounds A f hmn hDet
  have hTop : 0 ≤ ∑ j : Fin (n - m), max (Real.log (orderedSquareSingularValues A
      (Fin.castLE (Nat.sub_le n m) j))) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hBottom : 0 ≤ ∑ j : Fin (n - m), max (-Real.log (orderedSquareSingularValues A
      ⟨m + j.val, by omega⟩)) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  exact abs_le.mpr ⟨by linarith [hBounds.1], by linarith [hBounds.2]⟩

end CircularLaw
