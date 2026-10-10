import CircularLaw.ColumnAdditionLogIncrement
import CircularLaw.ReindexedMatrixSingularValues
import CircularLaw.ColumnSingularInterlacing
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

/-!
# Insertion at the manuscript's last row or column

The disjoint-union insertion is reindexed exactly to a matrix's last
finite index. Thus the checked product and logarithmic increment apply
to the literal matrix with its last row or column deleted.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

def insertedIndexToLast (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm Unit (Fin n)).trans
    ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans finSuccEquivLast.symm)

theorem inserted_index_to_last_new (n : ℕ) (u : Unit) :
    insertedIndexToLast n (Sum.inl u) = Fin.last n := by
  simp [insertedIndexToLast]

theorem inserted_index_to_last_old {n : ℕ} (i : Fin n) :
    insertedIndexToLast n (Sum.inr i) = Fin.castSucc i := by
  simp [insertedIndexToLast]

def lastRowVector {n m : ℕ} (B : Matrix (Fin (n + 1)) (Fin m) ℂ) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (fun j => B (Fin.last n) j)

def lastColumnVector {n m : ℕ} (B : Matrix (Fin n) (Fin (m + 1)) ℂ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => B i (Fin.last m))

theorem last_row_matrix_decomposition {n m : ℕ} (B : Matrix (Fin (n + 1)) (Fin m) ℂ) :
    Matrix.reindex (insertedIndexToLast n).symm (Equiv.refl (Fin m)) B =
      hybridInsertedRows (B.submatrix Fin.castSucc id) (lastRowVector B) := by
  ext i j
  cases i with
  | inl u => simp [Matrix.reindex_apply, inserted_index_to_last_new, hybridInsertedRows,
      hybridCandidateRow, lastRowVector]
  | inr i => simp [Matrix.reindex_apply, inserted_index_to_last_old, hybridInsertedRows]

theorem last_column_matrix_decomposition {n m : ℕ} (B : Matrix (Fin n) (Fin (m + 1)) ℂ) :
    Matrix.reindex (Equiv.refl (Fin n)) (insertedIndexToLast m).symm B =
      hybridInsertedColumns (B.submatrix id Fin.castSucc) (lastColumnVector B) := by
  ext i j
  cases j with
  | inl u => simp [Matrix.reindex_apply, inserted_index_to_last_new, hybridInsertedColumns,
      hybridCandidateColumn, lastColumnVector]
  | inr j => simp [Matrix.reindex_apply, inserted_index_to_last_old, hybridInsertedColumns]

theorem last_row_leading_log_prefix {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1) :
    leadingRowLogPrefix B hNew =
      insertedLeadingLogPrefix (B.submatrix Fin.castSucc id) hOld (lastRowVector B) := by
  apply Finset.sum_congr rfl
  intro j _
  have hSing := ordered_matrix_singular_values_reindex B (insertedIndexToLast n).symm (Equiv.refl (Fin m))
    (leadingSingularIndex hNew j) (insertedLeadingSingularIndex hOld j) rfl
  rw [last_row_matrix_decomposition] at hSing
  rw [hSing]

theorem last_column_leading_log_prefix {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hNew : r + 1 ≤ n) :
    leadingRowLogPrefix B hNew =
      insertedColumnLeadingLogPrefix (B.submatrix id Fin.castSucc) hNew (lastColumnVector B) := by
  apply Finset.sum_congr rfl
  intro j _
  have hSing := ordered_matrix_singular_values_reindex B (Equiv.refl (Fin n)) (insertedIndexToLast m).symm
    (leadingSingularIndex hNew j) (leadingSingularIndex hNew j) rfl
  rw [last_column_matrix_decomposition] at hSing
  rw [hSing]

theorem last_row_normalized_log_increment_of_projection {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r + 1 ≤ n + 1)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld)
    {N δ : ℝ} (hN : 0 < N)
    (hProjection : Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows (B.submatrix Fin.castSucc id) hOld).toEuclideanLin).starProjection
        (rowAdjointVector (lastRowVector B))‖) :
    leadingRowLogPrefix B hNew / N ≤
      leadingRowLogPrefix (B.submatrix Fin.castSucc id) hOld / N + δ := by
  rw [last_row_leading_log_prefix B hOld hNew]
  exact row_addition_normalized_log_increment_of_projection _ hOld _ hProd hN hProjection

theorem last_column_normalized_log_increment_of_projection {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (hOldRow : r ≤ n) (hOldCol : r ≤ m) (hNew : r + 1 ≤ n)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix id Fin.castSucc) hOldRow)
    {N δ : ℝ} (hN : 0 < N)
    (hProjection : Real.exp (-N * δ) ≤
      ‖(LinearMap.ker (leadingCompressedRows (B.submatrix id Fin.castSucc).conjTranspose hOldCol).toEuclideanLin).starProjection
        (lastColumnVector B)‖) :
    leadingRowLogPrefix B hNew / N ≤
      leadingRowLogPrefix (B.submatrix id Fin.castSucc) hOldRow / N + δ := by
  rw [last_column_leading_log_prefix B hNew]
  exact column_addition_normalized_log_increment_of_projection _ hOldRow hOldCol hNew _ hProd hN hProjection

theorem last_row_singular_value_le {n m : ℕ} (B : Matrix (Fin (n + 1)) (Fin m) ℂ)
    (i : Fin (Fintype.card (Fin n))) (j : Fin (Fintype.card (Fin (n + 1)))) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues (B.submatrix Fin.castSucc id) i ≤ orderedMatrixSingularValues B j := by
  let k : Fin (Fintype.card (Unit ⊕ Fin n)) := ⟨j.val, by
    simpa only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.add_comm] using j.isLt⟩
  have hSing := ordered_matrix_singular_values_reindex B (insertedIndexToLast n).symm (Equiv.refl (Fin m)) j k rfl
  rw [last_row_matrix_decomposition] at hSing
  rw [hSing]
  exact inserted_row_singular_value_le _ _ i k hIndex

theorem last_column_singular_value_le {n m : ℕ} (B : Matrix (Fin n) (Fin (m + 1)) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    orderedMatrixSingularValues (B.submatrix id Fin.castSucc) i ≤ orderedMatrixSingularValues B i := by
  let f : Fin m ↪ Fin (m + 1) := ⟨Fin.castSucc, Fin.castSucc_injective m⟩
  exact column_restriction_singular_value_le B f ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩

theorem last_row_same_prefix_product_le {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r ≤ n + 1) :
    leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld ≤ leadingRowSingularProduct B hNew := by
  apply Finset.prod_le_prod
  · intro j _
    exact ordered_matrix_singular_values_nonneg _ _
  · intro j _
    exact last_row_singular_value_le B (leadingSingularIndex hOld j) (leadingSingularIndex hNew j) rfl

theorem last_column_same_prefix_product_le {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (h : r ≤ n) :
    leadingRowSingularProduct (B.submatrix id Fin.castSucc) h ≤ leadingRowSingularProduct B h := by
  apply Finset.prod_le_prod
  · intro j _
    exact ordered_matrix_singular_values_nonneg _ _
  · intro j _
    exact last_column_singular_value_le B (leadingSingularIndex h j)

theorem last_row_same_prefix_log_le {r n m : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin m) ℂ) (hOld : r ≤ n) (hNew : r ≤ n + 1)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix Fin.castSucc id) hOld) :
    leadingRowLogPrefix B hNew ≤ leadingRowLogPrefix (B.submatrix Fin.castSucc id) hOld := by
  have hGrowth := last_row_same_prefix_product_le B hOld hNew
  have hNewProd := hProd.trans_le hGrowth
  rw [leading_row_log_prefix_eq_neg_log_product _ hOld hProd.ne',
    leading_row_log_prefix_eq_neg_log_product B hNew hNewProd.ne']
  exact neg_le_neg (Real.log_le_log hProd hGrowth)

theorem last_column_same_prefix_log_le {r n m : ℕ}
    (B : Matrix (Fin n) (Fin (m + 1)) ℂ) (h : r ≤ n)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix id Fin.castSucc) h) :
    leadingRowLogPrefix B h ≤ leadingRowLogPrefix (B.submatrix id Fin.castSucc) h := by
  have hGrowth := last_column_same_prefix_product_le B h
  have hNewProd := hProd.trans_le hGrowth
  rw [leading_row_log_prefix_eq_neg_log_product _ h hProd.ne',
    leading_row_log_prefix_eq_neg_log_product B h hNewProd.ne']
  exact neg_le_neg (Real.log_le_log hProd hGrowth)

end CircularLaw
