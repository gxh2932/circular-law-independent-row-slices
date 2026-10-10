import CircularLaw.MatrixColumnRestriction

/-!
# Exact singular-value interlacing when columns are deleted

The erased-coordinate map has codomain dimension exactly `n-k`. On its
kernel the actual row-Gram quadratic forms agree. The checked spectral
dimension argument therefore gives the exact shifted lower comparison;
coordinate-energy domination gives the same-position upper comparison.
-/

noncomputable section
open Classical
open scoped Matrix InnerProductSpace

namespace CircularLaw

theorem column_restriction_singular_value_le {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) (i : Fin m) :
    orderedRectangularSingularValues (matrixColumnRestriction A f) i ≤
      orderedRectangularSingularValues A i := by
  apply Real.sqrt_le_sqrt
  exact symmetric_ordered_eigenvalues_le_of_quadratic
    (Matrix.isHermitian_iff_isSymmetric.mp
      (Matrix.isHermitian_mul_conjTranspose_self (matrixColumnRestriction A f)))
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A))
    finrank_euclideanSpace (column_restriction_quadratic_le A f)
    ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩

theorem ambient_singular_value_le_column_restriction {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) (i j : Fin m)
    (hIndex : j.val = i.val + (n - k)) :
    orderedRectangularSingularValues A j ≤
      orderedRectangularSingularValues (matrixColumnRestriction A f) i := by
  apply Real.sqrt_le_sqrt
  apply symmetric_shifted_eigenvalues_le_on_kernel
    (Matrix.isHermitian_iff_isSymmetric.mp
      (Matrix.isHermitian_mul_conjTranspose_self (matrixColumnRestriction A f)))
    (Matrix.isHermitian_iff_isSymmetric.mp (Matrix.isHermitian_mul_conjTranspose_self A))
    finrank_euclideanSpace (finrank_euclideanSpace.trans (erasedColumnIndices_card f))
    (erasedColumnMap A f) _
    ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ hIndex
  intro v hv
  exact (column_restriction_quadratic_eq_on_kernel A f v hv).le

theorem column_restriction_singular_values_interlace {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin k ↪ Fin n) (i j : Fin m)
    (hIndex : j.val = i.val + (n - k)) :
    orderedRectangularSingularValues A j ≤
        orderedRectangularSingularValues (matrixColumnRestriction A f) i ∧
      orderedRectangularSingularValues (matrixColumnRestriction A f) i ≤
        orderedRectangularSingularValues A i :=
  ⟨ambient_singular_value_le_column_restriction A f i j hIndex,
    column_restriction_singular_value_le A f i⟩

end CircularLaw
