import CircularLaw.ColumnSingularInterlacing

/-!
# Singular values of an actual square principal submatrix

Deleting `n-m` rows and then `n-m` columns gives a total singular-index
loss of `2*(n-m)`. The upper comparison has no index loss. These are
deterministic statements for arbitrary complex matrices and embeddings.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem principal_singular_value_le {m n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin m ↪ Fin n) (i : Fin m) (j : Fin n) (hIndex : i.val = j.val) :
    orderedSquareSingularValues (A.submatrix f f) i ≤ orderedSquareSingularValues A j := by
  calc
    _ = orderedRectangularSingularValues
        (matrixColumnRestriction (matrixRowRestriction A f) f) i := rfl
    _ ≤ orderedRectangularSingularValues (matrixRowRestriction A f) i :=
      column_restriction_singular_value_le _ f i
    _ ≤ orderedRectangularSingularValues A j :=
      row_restriction_singular_value_le A f i j hIndex
    _ = _ := rfl

theorem ambient_singular_value_le_principal {m n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin m ↪ Fin n) (i : Fin m) (j : Fin n)
    (hIndex : j.val = i.val + 2 * (n - m)) :
    orderedSquareSingularValues A j ≤ orderedSquareSingularValues (A.submatrix f f) i := by
  have hmn : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
  let l : Fin m := ⟨i.val + (n - m), by have := j.isLt; omega⟩
  calc
    _ = orderedRectangularSingularValues A j := rfl
    _ ≤ orderedRectangularSingularValues (matrixRowRestriction A f) l :=
      ambient_singular_value_le_row_restriction A f l j (by dsimp [l]; omega)
    _ ≤ orderedRectangularSingularValues
        (matrixColumnRestriction (matrixRowRestriction A f) f) i :=
      ambient_singular_value_le_column_restriction _ f i l rfl
    _ = _ := rfl

theorem principal_singular_values_interlace {m n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin m ↪ Fin n) (i : Fin m) (j l : Fin n)
    (hSame : i.val = j.val) (hShift : l.val = i.val + 2 * (n - m)) :
    orderedSquareSingularValues A l ≤ orderedSquareSingularValues (A.submatrix f f) i ∧
      orderedSquareSingularValues (A.submatrix f f) i ≤ orderedSquareSingularValues A j :=
  ⟨ambient_singular_value_le_principal A f i l hShift,
    principal_singular_value_le A f i j hSame⟩

end CircularLaw
