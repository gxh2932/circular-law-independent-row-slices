import CircularLaw.RectangularSingularScaling
import CircularLaw.ColumnAdditionLogIncrement

/-!
# Degree scaling of the actual insertion products and log prefixes

Scaling the old matrix and inserted vector scales the actual inserted
matrix. Products scale even when singular values vanish. Logarithmic
corrections require every retained singular value to be nonzero.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem hybrid_inserted_rows_smul {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (x : EuclideanSpace ℂ (Fin m)) (c : ℂ) :
    hybridInsertedRows (c • A) (c • x) = c • hybridInsertedRows A x := by
  ext i j
  cases i <;> simp [hybridInsertedRows, hybridCandidateRow, Matrix.fromRows,
    PiLp.smul_apply, smul_eq_mul]

theorem hybrid_inserted_columns_smul {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (c : ℂ) :
    hybridInsertedColumns (c • A) (c • x) = c • hybridInsertedColumns A x := by
  ext i j
  cases j <;> simp [hybridInsertedColumns, hybridCandidateColumn, Matrix.fromCols,
    PiLp.smul_apply, smul_eq_mul]

theorem leading_row_singular_product_smul {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (c : ℂ) :
    leadingRowSingularProduct (c • A) h = ‖c‖ ^ r * leadingRowSingularProduct A h := by
  simp only [leadingRowSingularProduct, ordered_matrix_singular_smul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem inserted_leading_singular_product_smul {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) (c : ℂ) :
    insertedLeadingSingularProduct (c • A) h (c • x) =
      ‖c‖ ^ (r + 1) * insertedLeadingSingularProduct A h x := by
  simp only [insertedLeadingSingularProduct, hybrid_inserted_rows_smul,
    ordered_matrix_singular_smul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem inserted_column_leading_singular_product_smul {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r + 1 ≤ n) (x : EuclideanSpace ℂ (Fin n)) (c : ℂ) :
    insertedColumnLeadingSingularProduct (c • A) h (c • x) =
      ‖c‖ ^ (r + 1) * insertedColumnLeadingSingularProduct A h x := by
  simp only [insertedColumnLeadingSingularProduct, hybrid_inserted_columns_smul,
    ordered_matrix_singular_smul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem leading_row_singular_product_degree_normalization_pos_iff {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) {d : ℝ} (hd : 0 < d) :
    0 < leadingRowSingularProduct (degreeNormalizingScalar d • A) h ↔
      0 < leadingRowSingularProduct A h := by
  rw [leading_row_singular_product_smul]
  exact mul_pos_iff_of_pos_left (pow_pos (norm_pos_iff.mpr (degree_normalizing_scalar_ne_zero hd)) r)

theorem inserted_leading_singular_product_degree_normalization_pos_iff {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    {d : ℝ} (hd : 0 < d) :
    0 < insertedLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ↔
      0 < insertedLeadingSingularProduct A h x := by
  rw [inserted_leading_singular_product_smul]
  exact mul_pos_iff_of_pos_left (pow_pos (norm_pos_iff.mpr (degree_normalizing_scalar_ne_zero hd)) (r + 1))

theorem inserted_column_singular_product_degree_normalization_pos_iff {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r + 1 ≤ n) (x : EuclideanSpace ℂ (Fin n))
    {d : ℝ} (hd : 0 < d) :
    0 < insertedColumnLeadingSingularProduct (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x) ↔
      0 < insertedColumnLeadingSingularProduct A h x := by
  rw [inserted_column_leading_singular_product_smul]
  exact mul_pos_iff_of_pos_left (pow_pos (norm_pos_iff.mpr (degree_normalizing_scalar_ne_zero hd)) (r + 1))

theorem matrix_singular_log_sum_degree_normalization
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    (A : Matrix ι τ ℂ) {q : ℕ} (J : Fin q → Fin (Fintype.card ι))
    {d : ℝ} (hd : 0 < d) (hFactors : ∀ j, orderedMatrixSingularValues A (J j) ≠ 0) :
    (∑ j, -Real.log (orderedMatrixSingularValues (degreeNormalizingScalar d • A) (J j))) =
      (∑ j, -Real.log (orderedMatrixSingularValues A (J j))) + (q : ℝ) * Real.log (Real.sqrt d) := by
  calc
    _ = ∑ j, (-Real.log (orderedMatrixSingularValues A (J j)) + Real.log (Real.sqrt d)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ordered_matrix_singular_degree_normalization A hd,
        Real.log_div (hFactors j) (Real.sqrt_pos.mpr hd).ne']
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

def degreeNormalizedLeadingLogPrefix {r n m : ℕ} (d : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) : ℝ :=
  leadingRowLogPrefix (degreeNormalizingScalar d • A) h

def degreeNormalizedInsertedRowLogPrefix {r n m : ℕ} (d : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m)) : ℝ :=
  insertedLeadingLogPrefix (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x)

def degreeNormalizedInsertedColumnLogPrefix {r n m : ℕ} (d : ℝ)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r + 1 ≤ n) (x : EuclideanSpace ℂ (Fin n)) : ℝ :=
  insertedColumnLeadingLogPrefix (degreeNormalizingScalar d • A) h (degreeNormalizingScalar d • x)

theorem leading_row_log_prefix_degree_normalization {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) {d : ℝ} (hd : 0 < d)
    (hProd : leadingRowSingularProduct A h ≠ 0) :
    degreeNormalizedLeadingLogPrefix d A h = leadingRowLogPrefix A h +
      (r : ℝ) * Real.log (Real.sqrt d) := by
  apply matrix_singular_log_sum_degree_normalization A (leadingSingularIndex h) hd
  intro j
  exact Finset.prod_ne_zero_iff.mp hProd j (Finset.mem_univ j)

theorem inserted_row_log_prefix_degree_normalization {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) (x : EuclideanSpace ℂ (Fin m))
    {d : ℝ} (hd : 0 < d) (hProd : insertedLeadingSingularProduct A h x ≠ 0) :
    degreeNormalizedInsertedRowLogPrefix d A h x = insertedLeadingLogPrefix A h x +
      ((r + 1 : ℕ) : ℝ) * Real.log (Real.sqrt d) := by
  unfold degreeNormalizedInsertedRowLogPrefix insertedLeadingLogPrefix
  rw [hybrid_inserted_rows_smul]
  apply matrix_singular_log_sum_degree_normalization (hybridInsertedRows A x)
    (insertedLeadingSingularIndex h) hd
  intro j
  exact Finset.prod_ne_zero_iff.mp hProd j (Finset.mem_univ j)

theorem inserted_column_log_prefix_degree_normalization {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r + 1 ≤ n) (x : EuclideanSpace ℂ (Fin n))
    {d : ℝ} (hd : 0 < d) (hProd : insertedColumnLeadingSingularProduct A h x ≠ 0) :
    degreeNormalizedInsertedColumnLogPrefix d A h x = insertedColumnLeadingLogPrefix A h x +
      ((r + 1 : ℕ) : ℝ) * Real.log (Real.sqrt d) := by
  unfold degreeNormalizedInsertedColumnLogPrefix insertedColumnLeadingLogPrefix
  rw [hybrid_inserted_columns_smul]
  apply matrix_singular_log_sum_degree_normalization (hybridInsertedColumns A x)
    (leadingSingularIndex h) hd
  intro j
  exact Finset.prod_ne_zero_iff.mp hProd j (Finset.mem_univ j)

end CircularLaw
