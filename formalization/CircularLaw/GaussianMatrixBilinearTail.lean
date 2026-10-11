import CircularLaw.GaussianLinearFormTails
import CircularLaw.GaussianSquareMatrixLaw

/-!
# Actual Gaussian matrix bilinear forms have Gaussian tails

The Euclidean matrix operator keeps the ordinary matrix-vector action.
Its Hermitian bilinear form is a linear form in the independent matrix
entries, with coefficient energy exactly `norm(u)^2*norm(v)^2`.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators InnerProductSpace Matrix

namespace CircularLaw

def complexMatrixOperator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  A.toEuclideanLin.toContinuousLinearMap

theorem complex_matrix_operator_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    complexMatrixOperator A v i = ∑ j, A i j * v j := rfl

def gaussianMatrixBilinearCoefficients {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n)) : Fin n × Fin n → ℂ :=
  fun p => star (u p.1) * v p.2

theorem gaussian_matrix_bilinear_eq_linear_form {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n)) (x : GaussianSquareSample n) :
    ⟪u, complexMatrixOperator (gaussianSquareMatrix x) v⟫_ℂ =
      gaussianLinearForm (gaussianMatrixBilinearCoefficients u v) x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, gaussianLinearForm, Fintype.sum_prod_type,
    complex_matrix_operator_apply, gaussianSquareMatrix, gaussianMatrixBilinearCoefficients,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change x (i, j) * v j * star (u i) = star (u i) * v j * x (i, j)
  ring

theorem gaussian_matrix_bilinear_coefficient_energy {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n)) :
    (∑ p, ‖gaussianMatrixBilinearCoefficients u v p‖ ^ 2) = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [gaussianMatrixBilinearCoefficients, Fintype.sum_prod_type, norm_mul, norm_star, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]

theorem gaussian_matrix_bilinear_radial_tail {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ ≤ 2) (hv : ‖v‖ ≤ 2)
    {r : ℝ} (hr : 0 < r) :
    (gaussianSquareMatrixLaw n).real
      {x | r ≤ ‖⟪u, complexMatrixOperator (gaussianSquareMatrix x) v⟫_ℂ‖} ≤
        Real.exp (-(r / 4) ^ 2) := by
  have hU : ‖u‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg u]
  have hV : ‖v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg v]
  have hEnergy : (∑ p, ‖gaussianMatrixBilinearCoefficients u v p‖ ^ 2) ≤ (4 : ℝ) ^ 2 := by
    rw [gaussian_matrix_bilinear_coefficient_energy]
    nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖, mul_le_mul hU hV (sq_nonneg ‖v‖) (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [gaussian_matrix_bilinear_eq_linear_form]
  exact gaussian_linear_form_radial_tail_bound _ (by norm_num) hEnergy hr

end CircularLaw
