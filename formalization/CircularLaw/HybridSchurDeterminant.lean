import CircularLaw.HybridComparisonTrace
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Literal Schur determinant factorization when inserting one row

The row acts bilinearly, so its quadratic comparison matrix is the
entrywise conjugate of the ridge comparison. Both the block Gram and
the scalar Schur factor are identified with actual matrix expressions.
-/

noncomputable section
open Classical
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def hybridCandidateRow (v : EuclideanSpace ℂ n) : Matrix Unit n ℂ := fun _ j => v j

def hybridInsertedRows (K : Matrix m n ℂ) (v : EuclideanSpace ℂ n) : Matrix (Unit ⊕ m) n ℂ :=
  Matrix.fromRows (hybridCandidateRow v) K

omit [Fintype m] [DecidableEq n] in
theorem hybridInsertedRows_ridge_blocks (K : Matrix m n ℂ) (v : EuclideanSpace ℂ n) (η : ℝ) :
    hybridRowRidgeGram (hybridInsertedRows K v) η =
      Matrix.fromBlocks
        (hybridCandidateRow v * (hybridCandidateRow v)ᴴ + (η ^ 2) • 1)
        (hybridCandidateRow v * Kᴴ) (K * (hybridCandidateRow v)ᴴ) (hybridRowRidgeGram K η) := by
  rw [hybridRowRidgeGram, hybridInsertedRows, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  simp only [smul_zero, add_zero, hybridRowRidgeGram]

omit [DecidableEq n] in
theorem hybridCandidateRow_quadratic_transpose (P : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    (hybridCandidateRow v * P * (hybridCandidateRow v)ᴴ) () () =
      star v.ofLp ⬝ᵥ Pᵀ.mulVec v.ofLp := by
  simp only [Matrix.mul_apply, hybridCandidateRow, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hybridCandidateRow_quadratic_conjugate (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η)
    (v : EuclideanSpace ℂ n) :
    (hybridCandidateRow v * hybridComparisonMatrix K η * (hybridCandidateRow v)ᴴ) () () =
      (matrixEuclideanQuadratic (hybridConjugateComparisonMatrix K η) v : ℂ) := by
  rw [hybridCandidateRow_quadratic_transpose,
    ← hybridConjugateComparisonMatrix_eq_transpose K hη]
  have hNonneg := (hybridConjugateComparisonMatrix_positive_contraction K hη).1.dotProduct_mulVec_nonneg v.ofLp
  rw [matrixEuclideanQuadratic_eq_dotProduct]
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp hNonneg).2.symm

theorem hybridInsertedRows_schur_determinant (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η)
    (v : EuclideanSpace ℂ n) :
    (hybridRowRidgeGram (hybridInsertedRows K v) η).det =
      (hybridRowRidgeGram K η).det *
        ((η ^ 2 + matrixEuclideanQuadratic (hybridConjugateComparisonMatrix K η) v : ℝ) : ℂ) := by
  letI := (hybridRowRidgeGram_posDef K hη).isUnit.invertible
  rw [hybridInsertedRows_ridge_blocks, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hSchur : hybridCandidateRow v * (hybridCandidateRow v)ᴴ + (η ^ 2) • 1 -
      (hybridCandidateRow v * Kᴴ) * (hybridRowRidgeGram K η)⁻¹ * (K * (hybridCandidateRow v)ᴴ) =
      (η ^ 2) • 1 + hybridCandidateRow v * hybridComparisonMatrix K η * (hybridCandidateRow v)ᴴ := by
    simp only [hybridComparisonMatrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [hSchur, Matrix.det_unique (n := Unit), Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    if_pos rfl, hybridCandidateRow_quadratic_conjugate K hη v]
  simp

end CircularLaw
