import CircularLaw.PrincipalEigenvalueInterlacing
import CircularLaw.SquareSliceSingularValues

/-!
# Exact singular-value interlacing when rows are deleted

The retained row Gram is the actual principal submatrix of `A A*`.
Both sides of Cauchy interlacing apply, with an index loss equal to the
number of deleted rows. Width, rank deficiency and deterministic shifts
are unrestricted. Column deletion requires the additional kernel step.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

def orderedRectangularSingularValues {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ) : Fin n → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩)

theorem orderedRectangularSingularValues_nonneg {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℂ) (j : Fin n) :
    0 ≤ orderedRectangularSingularValues A j := Real.sqrt_nonneg _

theorem orderedRectangularSingularValues_antitone {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℂ) : Antitone (orderedRectangularSingularValues A) := by
  intro i j hij
  exact Real.sqrt_le_sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀_antitone hij)

theorem rectangular_singular_values_eq_square {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    orderedRectangularSingularValues A = orderedSquareSingularValues A := rfl

def matrixRowRestriction {m n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ) (f : Fin m ↪ Fin n) :
    Matrix (Fin m) (Fin k) ℂ := A.submatrix f id

theorem matrixRowRestriction_gram {m n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ)
    (f : Fin m ↪ Fin n) :
    matrixRowRestriction A f * (matrixRowRestriction A f).conjTranspose =
      (A * A.conjTranspose).submatrix f f := by
  ext i j
  simp only [matrixRowRestriction, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.conjTranspose_apply, id_eq]

theorem row_restriction_singular_value_le {m n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ)
    (f : Fin m ↪ Fin n) (i : Fin m) (j : Fin n) (hIndex : i.val = j.val) :
    orderedRectangularSingularValues (matrixRowRestriction A f) i ≤
      orderedRectangularSingularValues A j := by
  apply Real.sqrt_le_sqrt
  have h := hermitian_principal_eigenvalues_le (A * A.conjTranspose)
    (Matrix.isHermitian_mul_conjTranspose_self A) f
    ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ hIndex
  simpa only [matrixRowRestriction_gram] using h

theorem ambient_singular_value_le_row_restriction {m n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℂ) (f : Fin m ↪ Fin n) (i : Fin m) (j : Fin n)
    (hIndex : j.val = i.val + (n - m)) :
    orderedRectangularSingularValues A j ≤
      orderedRectangularSingularValues (matrixRowRestriction A f) i := by
  apply Real.sqrt_le_sqrt
  have h := hermitian_principal_shifted_eigenvalues_le (A * A.conjTranspose)
    (Matrix.isHermitian_mul_conjTranspose_self A) f
    ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩
    (by simpa only [Fintype.card_fin] using hIndex)
  simpa only [matrixRowRestriction_gram] using h

theorem row_restriction_singular_values_interlace {m n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℂ) (f : Fin m ↪ Fin n) (i : Fin m) (j l : Fin n)
    (hSame : i.val = j.val) (hShift : l.val = i.val + (n - m)) :
    orderedRectangularSingularValues A l ≤
        orderedRectangularSingularValues (matrixRowRestriction A f) i ∧
      orderedRectangularSingularValues (matrixRowRestriction A f) i ≤
        orderedRectangularSingularValues A j :=
  ⟨ambient_singular_value_le_row_restriction A f i l hShift,
    row_restriction_singular_value_le A f i j hSame⟩

end CircularLaw
