import CircularLaw.RowKernelProjection
import CircularLaw.HybridSchurDeterminant

/-!
# Exact base-times-height identity for inserting a row

For a full-row-rank matrix K, the new row Gram determinant is the old
Gram determinant times the squared norm of the actual projection of the
new adjoint row onto ker K. This is the unregularized volume identity
used in SSS25 Lemma 7.2.
-/

noncomputable section
open Classical
open scoped Matrix InnerProductSpace

namespace CircularLaw

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def rowAdjointVector (x : EuclideanSpace ℂ τ) : EuclideanSpace ℂ τ :=
  (hybridCandidateRow x).conjTranspose.toEuclideanLin ((EuclideanSpace.basisFun Unit ℂ) ())

omit [Fintype τ] [DecidableEq τ] in
theorem row_adjoint_vector_apply (x : EuclideanSpace ℂ τ) (j : τ) :
    rowAdjointVector x j = star (x j) := by
  simp [rowAdjointVector, hybridCandidateRow, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.conjTranspose_apply, EuclideanSpace.basisFun_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq τ] in
theorem inserted_row_gram_blocks (K : Matrix ι τ ℂ) (x : EuclideanSpace ℂ τ) :
    hybridInsertedRows K x * (hybridInsertedRows K x).conjTranspose =
      Matrix.fromBlocks
        (hybridCandidateRow x * (hybridCandidateRow x).conjTranspose)
        (hybridCandidateRow x * K.conjTranspose) (K * (hybridCandidateRow x).conjTranspose)
        (K * K.conjTranspose) := by
  rw [hybridInsertedRows, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul_fromCols]

theorem candidate_row_kernel_projection_scalar (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (x : EuclideanSpace ℂ τ) :
    (hybridCandidateRow x * rowKernelProjectionMatrix K * (hybridCandidateRow x).conjTranspose) () () =
      Complex.ofReal (‖(rowKernelProjectionMatrix K).toEuclideanLin (rowAdjointVector x)‖ ^ 2) := by
  let X := hybridCandidateRow x
  let P := rowKernelProjectionMatrix K
  have hP : P.IsHermitian := row_kernel_projection_matrix_hermitian K
  have hSquare : (X * P) * (X * P).conjTranspose = X * P * X.conjTranspose := by
    rw [Matrix.conjTranspose_mul, hP.eq]
    calc
      _ = X * (P * P) * X.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [row_kernel_projection_matrix_idempotent K hGram]
  have hQuad := matrix_row_gram_quadratic_eq_adjoint_norm (X * P)
    ((EuclideanSpace.basisFun Unit ℂ) ())
  rw [matrix_inner_standard_basis, hSquare] at hQuad
  have hReal : ((X * P * X.conjTranspose) () ()).re =
      ‖P.toEuclideanLin (rowAdjointVector x)‖ ^ 2 := by
    simpa only [Complex.conj_re, Matrix.conjTranspose_mul, hP.eq, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply, rowAdjointVector, X] using hQuad
  have hHerm : (X * P * X.conjTranspose).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose X hP
  have hIm : ((X * P * X.conjTranspose) () ()).im = 0 := by
    have h := congrArg (fun A : Matrix Unit Unit ℂ => (A () ()).im) hHerm.eq
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext
  · exact hReal
  · simpa only [Complex.ofReal_im] using hIm

theorem inserted_row_gram_det_kernel_projection (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (x : EuclideanSpace ℂ τ) :
    (hybridInsertedRows K x * (hybridInsertedRows K x).conjTranspose).det =
      (K * K.conjTranspose).det *
        Complex.ofReal (‖(LinearMap.ker K.toEuclideanLin).starProjection (rowAdjointVector x)‖ ^ 2) := by
  letI := ((K * K.conjTranspose).isUnit_iff_isUnit_det.mpr hGram).invertible
  rw [inserted_row_gram_blocks, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hSchur : hybridCandidateRow x * (hybridCandidateRow x).conjTranspose -
      (hybridCandidateRow x * K.conjTranspose) * (K * K.conjTranspose)⁻¹ *
        (K * (hybridCandidateRow x).conjTranspose) =
      hybridCandidateRow x * rowKernelProjectionMatrix K * (hybridCandidateRow x).conjTranspose := by
    simp only [rowKernelProjectionMatrix, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.mul_assoc]
  rw [hSchur, Matrix.det_unique (n := Unit), candidate_row_kernel_projection_scalar K hGram x,
    row_kernel_projection_matrix_eq_orthogonal_projection K hGram]

theorem inserted_row_gram_det_real_kernel_projection (K : Matrix ι τ ℂ)
    (hGram : IsUnit (K * K.conjTranspose).det) (x : EuclideanSpace ℂ τ) :
    (hybridInsertedRows K x * (hybridInsertedRows K x).conjTranspose).det.re =
      (K * K.conjTranspose).det.re *
        ‖(LinearMap.ker K.toEuclideanLin).starProjection (rowAdjointVector x)‖ ^ 2 := by
  rw [inserted_row_gram_det_kernel_projection K hGram x]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end CircularLaw
