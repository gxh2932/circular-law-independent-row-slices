import CircularLaw.IntermediateIndexBounds

/-!
# Singular values of the literal square shifted row-slice matrix

Ordered singular values are the square roots of the decreasing eigenvalues
of `A A*`. The actual retained row Gram is a principal submatrix of this
square product, so the surviving-row bound applies to the full matrix.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped ComplexOrder

namespace CircularLaw

def orderedSquareSingularValues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩)

theorem orderedSquareSingularValues_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    0 ≤ orderedSquareSingularValues A j := Real.sqrt_nonneg _

theorem orderedSquareGram_eigenvalue_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (j : Fin (Fintype.card (Fin n))) :
    0 ≤ (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ j := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := (Matrix.posSemidef_self_mul_conjTranspose A).eigenvalues_nonneg (e j)
  change 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ (e.symm (e j)) at h
  simpa only [Equiv.symm_apply_apply] using h

theorem orderedSquareSingularValues_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    orderedSquareSingularValues A j ^ 2 =
      (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀
        ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ :=
  Real.sq_sqrt (orderedSquareGram_eigenvalue_nonneg A _)

theorem orderedSquareSingularValues_antitone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Antitone (orderedSquareSingularValues A) := by
  intro i j hij
  exact Real.sqrt_le_sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀_antitone hij)

def fullShiftedSliceMatrix {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d) :
    Matrix (Fin n) (Fin n) ℂ := sliceMatrix rows - ζ • (1 : Matrix (Fin n) (Fin n) ℂ)

theorem fullShiftedSliceMatrix_apply {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d) (i j : Fin n) :
    fullShiftedSliceMatrix ζ rows i j = rowEntry (rows i) j - ζ * (if i = j then 1 else 0) := by
  simp only [fullShiftedSliceMatrix, Matrix.sub_apply, sliceMatrix, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]

theorem fullShiftedSliceMatrix_principal_rowGram {n d : ℕ} (H : Finset (Fin n))
    (ζ : ℂ) (rows : RowSliceMatrix n d) :
    (fullShiftedSliceMatrix ζ rows * (fullShiftedSliceMatrix ζ rows).conjTranspose).submatrix
      (fun i : H => i.val) (fun i : H => i.val) = Matrix.gram ℂ (retainedConjugateRow H ζ rows) := by
  rw [retainedRowGram_eq_matrix_product]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    fullShiftedSliceMatrix_apply, retainedShiftedMatrix]

theorem retained_singular_value_le_square {n d : ℕ} (H : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : Fin (Fintype.card H)) (j : Fin n)
    (hIndex : i.val = j.val) :
    retainedRowSingularValues H ζ rows i ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j := by
  apply Real.sqrt_le_sqrt
  have h := hermitian_principal_eigenvalues_le
    (fullShiftedSliceMatrix ζ rows * (fullShiftedSliceMatrix ζ rows).conjTranspose)
    (Matrix.isHermitian_mul_conjTranspose_self (fullShiftedSliceMatrix ζ rows))
    ⟨fun i : H => i.val, Subtype.val_injective⟩ i
    ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩ hIndex
  have hGram : (fullShiftedSliceMatrix ζ rows * (fullShiftedSliceMatrix ζ rows).conjTranspose).submatrix
      (⟨fun i : H => i.val, Subtype.val_injective⟩ : H ↪ Fin n)
      (⟨fun i : H => i.val, Subtype.val_injective⟩ : H ↪ Fin n) =
        Matrix.gram ℂ (retainedConjugateRow H ζ rows) :=
    fullShiftedSliceMatrix_principal_rowGram H ζ rows
  simpa only [hGram] using h

theorem surviving_rows_square_singular_value_degree_bound {n d : ℕ}
    (H : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d)
    {r : ℝ} (hr : 0 < r) (hDistance : ∀ i ∈ H, r ≤ leaveOneOutRowDistance H ζ rows i)
    (i : Fin (Fintype.card H)) (j : Fin n) (hIndex : i.val = j.val)
    (hd : 0 < d) (hTail : Fintype.card H ≤ (Fintype.card H - i.val) * d ^ 2) :
    r / d ≤ orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) j :=
  (surviving_rows_singular_value_degree_bound H ζ rows hr hDistance i hd hTail).trans
    (retained_singular_value_le_square H ζ rows i j hIndex)

end CircularLaw
