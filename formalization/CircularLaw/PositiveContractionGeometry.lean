import CircularLaw.SpectralRayleighBounds
import Mathlib.Analysis.Matrix.Order

/-!
# Positive-contraction quadratic forms and square roots

Section 8 uses Hermitian matrices with `0 <= P <= I`. The matrix-order
hypotheses are represented by positivity of `P` and `I-P`. Their literal
Euclidean quadratic forms are nonnegative and bounded by the squared
norm. Functional-calculus square roots identify those forms with actual
norm squares. The square root therefore contracts Euclidean distances.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsPositiveMatrixContraction (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ (1 - P).PosSemidef

def matrixEuclideanQuadratic (P : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : ℝ :=
  (⟪P.toEuclideanLin v, v⟫_ℂ).re

theorem matrixEuclideanQuadratic_eq_dotProduct (P : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic P v = (star v.ofLp ⬝ᵥ P.mulVec v.ofLp).re := by
  unfold matrixEuclideanQuadratic
  change RCLike.re (⟪P.toEuclideanLin v, v⟫_ℂ) = _
  rw [inner_re_symm, PiLp.inner_apply]
  change (∑ i, (P.mulVec v.ofLp) i * star (v i)).re = _
  simp only [dotProduct, Pi.star_apply, mul_comm]

theorem matrixEuclideanQuadratic_nonneg {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (v : EuclideanSpace ℂ ι) : 0 ≤ matrixEuclideanQuadratic P v := by
  rw [matrixEuclideanQuadratic_eq_dotProduct]
  exact hP.re_dotProduct_nonneg _

theorem matrixEuclideanQuadratic_sum_entries (P : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic P v = ∑ i, ∑ j, (star (v i) * P i j * v j).re := by
  rw [matrixEuclideanQuadratic_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, Pi.star_apply, mul_assoc]

theorem matrixEuclideanQuadratic_sub (P Q : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic (P - Q) v = matrixEuclideanQuadratic P v - matrixEuclideanQuadratic Q v := by
  simp only [matrixEuclideanQuadratic, Matrix.toEuclideanLin, map_sub,
    LinearMap.sub_apply, inner_sub_left, Complex.sub_re]

theorem matrixEuclideanQuadratic_one (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic 1 v = ‖v‖ ^ 2 := by
  simp only [matrixEuclideanQuadratic, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem positiveContraction_quadratic_le_norm_sq {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic P v ≤ ‖v‖ ^ 2 := by
  have h := matrixEuclideanQuadratic_nonneg hP.2 v
  rw [matrixEuclideanQuadratic_sub, matrixEuclideanQuadratic_one] at h
  linarith

theorem positiveContraction_square_le {P : Matrix ι ι ℂ} (hP : IsPositiveMatrixContraction P) :
    (P - P * P).PosSemidef := by
  have hCommute : Commute P (1 - P) := by
    change P * (1 - P) = (1 - P) * P
    simp only [mul_sub, sub_mul, mul_one, one_mul]
  have hProduct : 0 ≤ P * (1 - P) :=
    (commute_iff_mul_nonneg hP.1.nonneg hP.2.nonneg).mp hCommute
  simpa only [mul_sub, mul_one] using Matrix.nonneg_iff_posSemidef.mp hProduct

theorem positiveContraction_squared_quadratic_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (v : EuclideanSpace ℂ ι) :
    matrixEuclideanQuadratic (P * P) v ≤ matrixEuclideanQuadratic P v := by
  have h := matrixEuclideanQuadratic_nonneg (positiveContraction_square_le hP) v
  rw [matrixEuclideanQuadratic_sub] at h
  linarith

theorem positiveContraction_trace_nonneg {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) : 0 ≤ P.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => (Complex.nonneg_iff.mp (hP.1.diag_nonneg (i := i))).1)

theorem positiveContraction_trace_square_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) : (P * P).trace.re ≤ P.trace.re := by
  rw [Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (Complex.nonneg_iff.mp ((positiveContraction_square_le hP).diag_nonneg (i := i))).1
  simp only [Matrix.sub_apply, Complex.sub_re] at h
  change ((P * P) i i).re ≤ (P i i).re
  linarith

theorem matrix_squareRoot_norm_sq {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (v : EuclideanSpace ℂ ι) :
    ‖(CFC.sqrt P).toEuclideanLin v‖ ^ 2 = matrixEuclideanQuadratic P v := by
  have hRoot := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  have hSymm := Matrix.isHermitian_iff_isSymmetric.mp hRoot
  have hSquare : (CFC.sqrt P).toEuclideanLin ((CFC.sqrt P).toEuclideanLin v) = P.toEuclideanLin v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  rw [matrixEuclideanQuadratic, ← hSquare, hSymm]
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem positiveContraction_squareRoot_norm_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (v : EuclideanSpace ℂ ι) :
    ‖(CFC.sqrt P).toEuclideanLin v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [matrix_squareRoot_norm_sq hP.1]
  exact positiveContraction_quadratic_le_norm_sq hP v

theorem positiveContraction_squareRoot_dist_le {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (x y : EuclideanSpace ℂ ι) :
    dist ((CFC.sqrt P).toEuclideanLin x) ((CFC.sqrt P).toEuclideanLin y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact positiveContraction_squareRoot_norm_le hP (x - y)

end Matrices

end CircularLaw
