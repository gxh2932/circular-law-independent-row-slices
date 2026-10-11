import CircularLaw.InsertedRowSingularVolume

/-!
# Compression onto the leading left singular directions

The spectral basis is reindexed using the same equivalence as mathlib's
sorted eigenvalues. Thus the selected rows are the first r singular
directions even when the finite-type equivalence permutes coordinates.
Their Gram determinant is exactly the squared leading singular product.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

def leadingSingularIndex {r n : ℕ} (h : r ≤ n) (j : Fin r) :
    Fin (Fintype.card (Fin n)) :=
  ⟨j.val, by simpa only [Fintype.card_fin] using lt_of_lt_of_le j.isLt h⟩

def leadingRowEigenIndex {r n : ℕ} (h : r ≤ n) : Fin r ↪ Fin n where
  toFun j := (Fintype.equivOfCardEq (Fintype.card_fin _) :
    Fin (Fintype.card (Fin n)) ≃ Fin n) (leadingSingularIndex h j)
  inj' := by
    intro i j hij
    have hij' := (Fintype.equivOfCardEq (Fintype.card_fin _) :
      Fin (Fintype.card (Fin n)) ≃ Fin n).injective hij
    exact Fin.ext (congrArg (fun k : Fin (Fintype.card (Fin n)) => k.val) hij')

def leadingRowCompression {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    Matrix (Fin r) (Fin n) ℂ :=
  matrixRowRestriction
    (Matrix.isHermitian_mul_conjTranspose_self A).eigenvectorUnitary.val.conjTranspose
    (leadingRowEigenIndex h)

def leadingCompressedRows {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    Matrix (Fin r) (Fin m) ℂ := leadingRowCompression A h * A

def leadingRowSingularProduct {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) : ℝ :=
  ∏ j : Fin r, orderedMatrixSingularValues A (leadingSingularIndex h j)

theorem leading_row_eigenvalues {r n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (h : r ≤ n) (j : Fin r) :
    (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues (leadingRowEigenIndex h j) =
      (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀ (leadingSingularIndex h j) := by
  simp only [Matrix.IsHermitian.eigenvalues, leadingRowEigenIndex, Function.Embedding.coeFn_mk,
    Equiv.symm_apply_apply]

theorem leading_row_compression_coisometry {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    leadingRowCompression A h * (leadingRowCompression A h).conjTranspose = 1 := by
  let U := (Matrix.isHermitian_mul_conjTranspose_self A).eigenvectorUnitary
  have hU : U.val.conjTranspose * U.val = 1 := Unitary.coe_star_mul_self U
  rw [leadingRowCompression, matrixRowRestriction_gram, Matrix.conjTranspose_conjTranspose, hU]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply, (leadingRowEigenIndex h).injective.eq_iff]

theorem leading_compressed_rows_gram {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    leadingCompressedRows A h * (leadingCompressedRows A h).conjTranspose =
      Matrix.diagonal (fun j : Fin r =>
        Complex.ofReal ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues₀
          (leadingSingularIndex h j))) := by
  let H := Matrix.isHermitian_mul_conjTranspose_self A
  let U := H.eigenvectorUnitary
  have hDiag : (U.val.conjTranspose * A) * (U.val.conjTranspose * A).conjTranspose =
      Matrix.diagonal (RCLike.ofReal ∘ H.eigenvalues) := by
    have hs := H.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hs
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hs
  have hRows : leadingCompressedRows A h =
      matrixRowRestriction (U.val.conjTranspose * A) (leadingRowEigenIndex h) := rfl
  rw [hRows, matrixRowRestriction_gram, hDiag]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply,
    (leadingRowEigenIndex h).injective.eq_iff, Function.comp_apply]
  split_ifs with hij
  · exact congrArg Complex.ofReal (leading_row_eigenvalues A h i)
  · rfl

theorem leading_compressed_rows_gram_det {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    (leadingCompressedRows A h * (leadingCompressedRows A h).conjTranspose).det.re =
      leadingRowSingularProduct A h ^ 2 := by
  rw [leading_compressed_rows_gram, Matrix.det_diagonal]
  simp only [← Complex.ofReal_prod, Complex.ofReal_re, leadingRowSingularProduct,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  exact (ordered_matrix_singular_values_sq A (leadingSingularIndex h j)).symm

theorem leading_row_singular_product_nonneg {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n) :
    0 ≤ leadingRowSingularProduct A h :=
  Finset.prod_nonneg (fun _ _ => ordered_matrix_singular_values_nonneg _ _)

theorem leading_compressed_rows_gram_invertible {r n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hProd : leadingRowSingularProduct A h ≠ 0) :
    IsUnit (leadingCompressedRows A h * (leadingCompressedRows A h).conjTranspose).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hZero
  have hRe := congrArg Complex.re hZero
  rw [leading_compressed_rows_gram_det] at hRe
  exact (pow_ne_zero 2 hProd) hRe

end CircularLaw
