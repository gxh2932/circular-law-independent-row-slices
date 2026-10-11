import CircularLaw.ColumnSingularInterlacing
import CircularLaw.RowAdditionLogIncrement

/-!
# Retained singular products under simultaneous row and column restriction

Injective restriction decreases each same-position singular value. It
therefore decreases the retained product. A positive restricted product
remains positive in the larger matrix and gives the reverse inequality
for the actual negative-log prefix.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem matrix_injective_restriction_singular_value_le {a m b k : ℕ}
    (B : Matrix (Fin b) (Fin k) ℂ) (f : Fin a ↪ Fin b) (g : Fin m ↪ Fin k)
    (i : Fin (Fintype.card (Fin a))) (j : Fin (Fintype.card (Fin b))) (hIndex : i.val = j.val) :
    orderedMatrixSingularValues (B.submatrix f g) i ≤ orderedMatrixSingularValues B j := by
  have hRow := row_restriction_singular_value_le (matrixColumnRestriction B g) f
    ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ hIndex
  exact hRow.trans (column_restriction_singular_value_le B g
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩)

theorem matrix_injective_restriction_retained_product_le {r a m b k : ℕ}
    (B : Matrix (Fin b) (Fin k) ℂ) (f : Fin a ↪ Fin b) (g : Fin m ↪ Fin k)
    (hOld : r ≤ a) (hNew : r ≤ b) :
    leadingRowSingularProduct (B.submatrix f g) hOld ≤ leadingRowSingularProduct B hNew := by
  unfold leadingRowSingularProduct
  exact Finset.prod_le_prod (fun _ _ => ordered_matrix_singular_values_nonneg _ _)
    (fun j _ => matrix_injective_restriction_singular_value_le B f g
      (leadingSingularIndex hOld j) (leadingSingularIndex hNew j) rfl)

theorem matrix_injective_restriction_retained_log_le {r a m b k : ℕ}
    (B : Matrix (Fin b) (Fin k) ℂ) (f : Fin a ↪ Fin b) (g : Fin m ↪ Fin k)
    (hOld : r ≤ a) (hNew : r ≤ b)
    (hProd : 0 < leadingRowSingularProduct (B.submatrix f g) hOld) :
    leadingRowLogPrefix B hNew ≤ leadingRowLogPrefix (B.submatrix f g) hOld := by
  have hBound := matrix_injective_restriction_retained_product_le B f g hOld hNew
  have hNewProd := hProd.trans_le hBound
  rw [leading_row_log_prefix_eq_neg_log_product B hNew hNewProd.ne',
    leading_row_log_prefix_eq_neg_log_product (B.submatrix f g) hOld hProd.ne']
  exact neg_le_neg (Real.log_le_log hProd hBound)

end CircularLaw
