import CircularLaw.GaussianPolynomialSquareMoments
import CircularLaw.GaussianSquareMatrixLaw
import CircularLaw.SquareSingularTraceMoments

/-!
# Exact finite polynomial formulas for every shifted Gaussian trace moment

The symbolic matrix evaluates entrywise to the actual normalized shifted
Gaussian matrix. A separate conjugate-variable matrix evaluates to its
actual adjoint. Evaluation commutes with their Gram product, every power
and the trace. All finite moment and centered-square expectations are
therefore the checked Gaussian polynomial functional, with no weak limit
or distinct-entry hypothesis assumed.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

def gaussianSymbolicShiftedMatrix (n : ℕ) (z : ℂ) :
    Matrix (Fin n) (Fin n) (GaussianPolynomial (Fin n × Fin n)) := fun i j =>
  MvPolynomial.C ((Real.sqrt (n : ℝ) : ℂ)⁻¹) * MvPolynomial.X (false, (i, j)) -
    if i = j then MvPolynomial.C z else 0

def gaussianSymbolicShiftedAdjoint (n : ℕ) (z : ℂ) :
    Matrix (Fin n) (Fin n) (GaussianPolynomial (Fin n × Fin n)) := fun i j =>
  MvPolynomial.C (star ((Real.sqrt (n : ℝ) : ℂ)⁻¹)) * MvPolynomial.X (true, (j, i)) -
    if i = j then MvPolynomial.C (star z) else 0

def gaussianTraceMomentPolynomial (n : ℕ) (z : ℂ) (k : ℕ) :
    GaussianPolynomial (Fin n × Fin n) :=
  ((gaussianSymbolicShiftedMatrix n z * gaussianSymbolicShiftedAdjoint n z) ^ k).trace

theorem gaussian_symbolic_shifted_matrix_evaluation {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) :
    (gaussianSymbolicShiftedMatrix n z).map (MvPolynomial.eval (gaussianPolynomialVariables x)) =
      normalizedShiftedGaussianMatrix z x := by
  ext i j
  by_cases hij : i = j <;>
    simp [gaussianSymbolicShiftedMatrix, Matrix.map_apply, gaussianPolynomialVariables,
      normalized_shifted_gaussian_matrix_entry, hij]

theorem gaussian_symbolic_shifted_adjoint_evaluation {n : ℕ} (z : ℂ)
    (x : GaussianSquareSample n) :
    (gaussianSymbolicShiftedAdjoint n z).map (MvPolynomial.eval (gaussianPolynomialVariables x)) =
      (normalizedShiftedGaussianMatrix z x).conjTranspose := by
  ext i j
  by_cases hij : i = j <;>
    simp [gaussianSymbolicShiftedAdjoint, Matrix.map_apply, gaussianPolynomialVariables,
      Matrix.conjTranspose_apply, normalized_shifted_gaussian_matrix_entry, hij, eq_comm]

theorem gaussian_trace_moment_polynomial_evaluation {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    gaussianPolynomialEvaluation (gaussianTraceMomentPolynomial n z k) x =
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace := by
  unfold gaussianPolynomialEvaluation gaussianTraceMomentPolynomial
  rw [AddMonoidHom.map_trace, Matrix.map_pow, Matrix.map_mul,
    gaussian_symbolic_shifted_matrix_evaluation, gaussian_symbolic_shifted_adjoint_evaluation]

theorem gaussian_shifted_gram_trace_pow_integrable (n : ℕ) (z : ℂ) (k : ℕ) :
    Integrable (fun x => ((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace) (gaussianSquareMatrixLaw n) := by
  have hEq : gaussianPolynomialEvaluation (gaussianTraceMomentPolynomial n z k) =
      fun x => ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace :=
    funext (gaussian_trace_moment_polynomial_evaluation z k)
  rw [← hEq]
  exact gaussian_polynomial_evaluation_integrable _

theorem gaussian_shifted_gram_trace_pow_integral (n : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, ((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace
      ∂gaussianSquareMatrixLaw n) = gaussianPolynomialMean (gaussianTraceMomentPolynomial n z k) := by
  simp only [← gaussian_trace_moment_polynomial_evaluation]
  exact gaussian_polynomial_evaluation_integral _

theorem gaussian_shifted_gram_trace_norm_power_integrable (n : ℕ) (z : ℂ) (k r : ℕ) :
    Integrable (fun x => ‖((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace‖ ^ r)
      (gaussianSquareMatrixLaw n) := by
  simp only [← gaussian_trace_moment_polynomial_evaluation]
  exact gaussian_polynomial_norm_power_integrable _ _

theorem gaussian_shifted_singular_even_moment_trace {n : ℕ} (z : ℂ) (k : ℕ)
    (x : GaussianSquareSample n) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x) =
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace.re / n :=
  square_singular_measure_even_moment _ _

theorem gaussian_shifted_singular_even_moment_integrable (n : ℕ) (z : ℂ) (k : ℕ) :
    Integrable (fun x => ∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x)
      (gaussianSquareMatrixLaw n) := by
  simp only [gaussian_shifted_singular_even_moment_trace]
  exact ((gaussian_shifted_gram_trace_pow_integrable n z k).re).div_const _

theorem gaussian_shifted_singular_even_moment_integral (n : ℕ) (z : ℂ) (k : ℕ) :
    (∫ x, (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianSingularMeasure z x)
      ∂gaussianSquareMatrixLaw n) =
      (gaussianPolynomialMean (gaussianTraceMomentPolynomial n z k)).re / n := by
  simp only [gaussian_shifted_singular_even_moment_trace]
  rw [integral_div]
  change (∫ x, RCLike.re ((normalizedShiftedGaussianMatrix z x *
    (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace
    ∂gaussianSquareMatrixLaw n) / n = _
  rw [integral_re (gaussian_shifted_gram_trace_pow_integrable n z k),
    gaussian_shifted_gram_trace_pow_integral]
  rfl

theorem gaussian_shifted_trace_centered_square_integrable (n : ℕ) (z m : ℂ) (k : ℕ) :
    Integrable (fun x => ‖((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace - m‖ ^ 2)
      (gaussianSquareMatrixLaw n) := by
  have hEval (x : GaussianSquareSample n) :
      gaussianPolynomialEvaluation (gaussianTraceMomentPolynomial n z k - MvPolynomial.C m) x =
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace - m := by
    change MvPolynomial.eval _ (_ - _) = _
    rw [map_sub, MvPolynomial.eval_C]
    rw [← gaussian_trace_moment_polynomial_evaluation z k x]
    rfl
  simp only [← hEval]
  exact gaussian_polynomial_norm_power_integrable _ 2

theorem gaussian_shifted_trace_centered_square_integral (n : ℕ) (z m : ℂ) (k : ℕ) :
    (∫ x, ‖((normalizedShiftedGaussianMatrix z x *
      (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace - m‖ ^ 2
      ∂gaussianSquareMatrixLaw n) =
      (gaussianPolynomialMean ((gaussianTraceMomentPolynomial n z k - MvPolynomial.C m) *
        gaussianPolynomialStarHom (gaussianTraceMomentPolynomial n z k - MvPolynomial.C m))).re := by
  have hEval (x : GaussianSquareSample n) :
      gaussianPolynomialEvaluation (gaussianTraceMomentPolynomial n z k - MvPolynomial.C m) x =
      ((normalizedShiftedGaussianMatrix z x *
        (normalizedShiftedGaussianMatrix z x).conjTranspose) ^ k).trace - m := by
    change MvPolynomial.eval _ (_ - _) = _
    rw [map_sub, MvPolynomial.eval_C]
    rw [← gaussian_trace_moment_polynomial_evaluation z k x]
    rfl
  simp only [← hEval]
  exact gaussian_polynomial_norm_square_integral _

end CircularLaw
