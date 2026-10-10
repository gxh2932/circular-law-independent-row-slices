import CircularLaw.HybridSchurDeterminant
import CircularLaw.RegularizedDistanceGeometry

/-!
# Schur factors give the literal hybrid logarithmic increment

The ridge determinant is positive and real. Splitting its logarithm
cancels the common other-row factor, leaving exactly the logarithms
of the two regularized distances from the manuscript.
-/

noncomputable section
open Classical
open scoped Matrix MatrixOrder ComplexOrder

namespace CircularLaw

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def regularizedRowPotential (H : Matrix m n ℂ) (η : ℝ) : ℝ :=
  (1 / 2) * Real.log (hybridRowRidgeGram H η).det.re

omit [DecidableEq n] in
theorem hybridRowRidgeGram_det_re_pos (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    0 < (hybridRowRidgeGram K η).det.re := by
  have h := (hybridRowRidgeGram_posDef K hη).det_pos
  exact (RCLike.pos_iff.mp h).1

theorem hybridInsertedRows_schur_determinant_re (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η)
    (v : EuclideanSpace ℂ n) :
    (hybridRowRidgeGram (hybridInsertedRows K v) η).det.re =
      (hybridRowRidgeGram K η).det.re *
        (η ^ 2 + matrixEuclideanQuadratic (hybridConjugateComparisonMatrix K η) v) := by
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    congrArg Complex.re (hybridInsertedRows_schur_determinant K hη v)

theorem regularizedRowPotential_inserted (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η)
    (v : EuclideanSpace ℂ n) :
    regularizedRowPotential (hybridInsertedRows K v) η = regularizedRowPotential K η +
      Real.log (Real.sqrt (η ^ 2 + matrixEuclideanQuadratic (hybridConjugateComparisonMatrix K η) v)) := by
  have hDet := hybridRowRidgeGram_det_re_pos K hη
  have hQuadratic := matrixEuclideanQuadratic_nonneg
    (hybridConjugateComparisonMatrix_positive_contraction K hη).1 v
  have hScalar : 0 < η ^ 2 + matrixEuclideanQuadratic (hybridConjugateComparisonMatrix K η) v :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) hQuadratic
  rw [regularizedRowPotential, hybridInsertedRows_schur_determinant_re K hη v,
    Real.log_mul hDet.ne' hScalar.ne', Real.log_sqrt hScalar.le, regularizedRowPotential]
  ring

theorem regularizedRowPotential_hybrid_increment (K : Matrix m n ℂ) {η : ℝ} (hη : 0 < η)
    (u x y : EuclideanSpace ℂ n) :
    regularizedRowPotential (hybridInsertedRows K (x + u)) η -
        regularizedRowPotential (hybridInsertedRows K (y + u)) η =
      Real.log (regularizedDistance (hybridConjugateComparisonMatrix K η) η u x) -
        Real.log (regularizedDistance (hybridConjugateComparisonMatrix K η) η u y) := by
  rw [regularizedRowPotential_inserted K hη (x + u), regularizedRowPotential_inserted K hη (y + u)]
  dsimp [regularizedDistance]
  ring

end CircularLaw
