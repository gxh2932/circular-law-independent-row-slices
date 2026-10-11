import CircularLaw.RowAdditionLogIncrement
import CircularLaw.RectangularAdjointSingularValues

/-!
# The actual column-insertion singular-product bound

Taking the adjoint turns column insertion into row insertion. The
rectangular adjoint singular-value identity transfers the old and new
products back to the original matrix, with every index and dimension
bound retained. The new projection acts on the original column vector.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

def hybridCandidateColumn {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) Unit ℂ :=
  fun i _ => c i

def hybridInsertedColumns {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (c : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Unit ⊕ Fin m) ℂ :=
  Matrix.fromCols (hybridCandidateColumn c) A

def insertedColumnLeadingSingularProduct {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hNext : r + 1 ≤ n) (c : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∏ j : Fin (r + 1), orderedMatrixSingularValues (hybridInsertedColumns A c)
    (leadingSingularIndex hNext j)

theorem row_adjoint_vector_involutive {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    rowAdjointVector (rowAdjointVector v) = v := by
  ext j
  simp only [row_adjoint_vector_apply, star_star]

theorem hybrid_candidate_column_conjTranspose {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) :
    (hybridCandidateColumn c).conjTranspose = hybridCandidateRow (rowAdjointVector c) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hybridCandidateColumn, hybridCandidateRow,
    row_adjoint_vector_apply]

theorem hybrid_inserted_columns_conjTranspose {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (c : EuclideanSpace ℂ (Fin n)) :
    (hybridInsertedColumns A c).conjTranspose = hybridInsertedRows A.conjTranspose (rowAdjointVector c) := by
  rw [hybridInsertedColumns, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    hybrid_candidate_column_conjTranspose]
  rfl

theorem leading_row_singular_product_conjTranspose {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) :
    leadingRowSingularProduct A hRow = leadingRowSingularProduct A.conjTranspose hCol := by
  apply Finset.prod_congr rfl
  intro j _
  exact ordered_matrix_singular_values_conjTranspose A
    (leadingSingularIndex hRow j) (leadingSingularIndex hCol j) rfl

theorem leading_row_log_prefix_conjTranspose {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) :
    leadingRowLogPrefix A hRow = leadingRowLogPrefix A.conjTranspose hCol := by
  apply Finset.sum_congr rfl
  intro j _
  rw [ordered_matrix_singular_values_conjTranspose A
    (leadingSingularIndex hRow j) (leadingSingularIndex hCol j) rfl]

theorem inserted_column_product_eq_adjoint_row_product {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (c : EuclideanSpace ℂ (Fin n)) :
    insertedColumnLeadingSingularProduct A hNext c =
      insertedLeadingSingularProduct A.conjTranspose hCol (rowAdjointVector c) := by
  apply Finset.prod_congr rfl
  intro j _
  rw [← hybrid_inserted_columns_conjTranspose]
  exact ordered_matrix_singular_values_conjTranspose (hybridInsertedColumns A c)
    (leadingSingularIndex hNext j) (insertedLeadingSingularIndex hCol j) rfl

theorem column_addition_leading_singular_product_bound {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (c : EuclideanSpace ℂ (Fin n)) :
    ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection c‖ *
      leadingRowSingularProduct A hRow ≤ insertedColumnLeadingSingularProduct A hNext c := by
  have hBound := row_addition_leading_singular_product_bound A.conjTranspose hCol (rowAdjointVector c)
  rw [row_adjoint_vector_involutive,
    ← leading_row_singular_product_conjTranspose A hRow hCol,
    ← inserted_column_product_eq_adjoint_row_product A hCol hNext c] at hBound
  exact hBound

theorem column_addition_product_bound_of_projection {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (c : EuclideanSpace ℂ (Fin n)) {η : ℝ}
    (hThreshold : η ≤ ‖(LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin).starProjection
      c‖) :
    η * leadingRowSingularProduct A hRow ≤ insertedColumnLeadingSingularProduct A hNext c :=
  (mul_le_mul_of_nonneg_right hThreshold (leading_row_singular_product_nonneg A hRow)).trans
    (column_addition_leading_singular_product_bound A hRow hCol hNext c)

end CircularLaw
