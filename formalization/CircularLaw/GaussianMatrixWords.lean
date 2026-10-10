import CircularLaw.GaussianPolynomialImbalance
import CircularLaw.GaussianSquareMatrixLaw

/-!
# Arbitrary Gaussian matrix words and imbalance cancellation

A Boolean word specifies direct matrices and actual adjoints in their
noncommuting order. Its symbolic trace is homogeneous at the difference
between the two counts. Evaluation gives the actual matrix product, so
every unbalanced word trace has integrable, exactly zero expectation.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

def gaussianRawSymbolicMatrix (n : ℕ) (b : Bool) :
    Matrix (Fin n) (Fin n) (GaussianPolynomial (Fin n × Fin n)) := fun i j =>
  if b then MvPolynomial.X (true, (j, i)) else MvPolynomial.X (false, (i, j))

def gaussianSymbolicMatrixWord (n : ℕ) (w : List Bool) :
    Matrix (Fin n) (Fin n) (GaussianPolynomial (Fin n × Fin n)) :=
  (w.map (gaussianRawSymbolicMatrix n)).prod

def gaussianMatrixWord {n : ℕ} (w : List Bool) (x : GaussianSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (w.map (fun b => if b then (gaussianSquareMatrix x).conjTranspose else gaussianSquareMatrix x)).prod

def gaussianMatrixWordImbalance (w : List Bool) : ℤ :=
  (w.map (fun b => if b then (-1 : ℤ) else 1)).sum

theorem gaussian_matrix_word_imbalance_counts (w : List Bool) :
    gaussianMatrixWordImbalance w = (w.count false : ℤ) - w.count true := by
  induction w with
  | nil => simp [gaussianMatrixWordImbalance]
  | cons b w ih =>
    simp only [gaussianMatrixWordImbalance] at ih
    cases b <;> simp [gaussianMatrixWordImbalance, ih] <;> ring

theorem gaussian_raw_symbolic_entry_homogeneous (n : ℕ) (b : Bool) (i j : Fin n) :
    (gaussianRawSymbolicMatrix n b i j).IsWeightedHomogeneous gaussianImbalanceWeight
      (if b then (-1 : ℤ) else 1) := by
  cases b
  · simpa only [gaussianRawSymbolicMatrix, gaussianImbalanceWeight] using
      MvPolynomial.isWeightedHomogeneous_X ℂ gaussianImbalanceWeight (false, (i, j))
  · simpa only [gaussianRawSymbolicMatrix, gaussianImbalanceWeight] using
      MvPolynomial.isWeightedHomogeneous_X ℂ gaussianImbalanceWeight (true, (j, i))

theorem gaussian_symbolic_matrix_product_homogeneous {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (GaussianPolynomial (Fin n × Fin n))) (m r : ℤ)
    (hA : ∀ i j, (A i j).IsWeightedHomogeneous gaussianImbalanceWeight m)
    (hB : ∀ i j, (B i j).IsWeightedHomogeneous gaussianImbalanceWeight r) (i j : Fin n) :
    ((A * B) i j).IsWeightedHomogeneous gaussianImbalanceWeight (m + r) := by
  rw [Matrix.mul_apply]
  exact MvPolynomial.IsWeightedHomogeneous.sum Finset.univ (fun k => A i k * B k j)
    (m + r) (fun k _ => (hA i k).mul (hB k j))

theorem gaussian_symbolic_word_entry_homogeneous (n : ℕ) (w : List Bool) (i j : Fin n) :
    (gaussianSymbolicMatrixWord n w i j).IsWeightedHomogeneous gaussianImbalanceWeight
      (gaussianMatrixWordImbalance w) := by
  induction w generalizing i j with
  | nil =>
    simp only [gaussianSymbolicMatrixWord, List.map_nil, List.prod_nil,
      gaussianMatrixWordImbalance, List.sum_nil]
    by_cases hij : i = j
    · simp only [Matrix.one_apply, if_pos hij]
      exact MvPolynomial.isWeightedHomogeneous_one ℂ gaussianImbalanceWeight
    · simp only [Matrix.one_apply, if_neg hij]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ gaussianImbalanceWeight 0
  | cons b w ih =>
    change ((gaussianRawSymbolicMatrix n b * gaussianSymbolicMatrixWord n w) i j).IsWeightedHomogeneous
      gaussianImbalanceWeight
        ((if b then (-1 : ℤ) else 1) + gaussianMatrixWordImbalance w)
    exact gaussian_symbolic_matrix_product_homogeneous _ _ _ _
      (gaussian_raw_symbolic_entry_homogeneous n b) ih i j

theorem gaussian_symbolic_word_trace_homogeneous (n : ℕ) (w : List Bool) :
    (gaussianSymbolicMatrixWord n w).trace.IsWeightedHomogeneous gaussianImbalanceWeight
      (gaussianMatrixWordImbalance w) := by
  simp only [Matrix.trace, Matrix.diag]
  exact MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ _
    (fun i _ => gaussian_symbolic_word_entry_homogeneous n w i i)

theorem gaussian_raw_symbolic_matrix_evaluation {n : ℕ} (b : Bool) (x : GaussianSquareSample n) :
    (gaussianRawSymbolicMatrix n b).map (MvPolynomial.eval (gaussianPolynomialVariables x)) =
      if b then (gaussianSquareMatrix x).conjTranspose else gaussianSquareMatrix x := by
  cases b <;> ext i j <;>
    simp [gaussianRawSymbolicMatrix, Matrix.map_apply, gaussianPolynomialVariables,
      gaussianSquareMatrix, Matrix.conjTranspose_apply]

theorem gaussian_symbolic_matrix_word_evaluation {n : ℕ} (w : List Bool)
    (x : GaussianSquareSample n) :
    (gaussianSymbolicMatrixWord n w).map (MvPolynomial.eval (gaussianPolynomialVariables x)) =
      gaussianMatrixWord w x := by
  induction w with
  | nil => simp [gaussianSymbolicMatrixWord, gaussianMatrixWord]
  | cons b w ih =>
    change ((gaussianRawSymbolicMatrix n b * gaussianSymbolicMatrixWord n w).map _) =
      (if b then (gaussianSquareMatrix x).conjTranspose else gaussianSquareMatrix x) *
        gaussianMatrixWord w x
    rw [Matrix.map_mul, gaussian_raw_symbolic_matrix_evaluation, ih]

theorem gaussian_symbolic_word_trace_evaluation {n : ℕ} (w : List Bool)
    (x : GaussianSquareSample n) :
    gaussianPolynomialEvaluation (gaussianSymbolicMatrixWord n w).trace x =
      (gaussianMatrixWord w x).trace := by
  unfold gaussianPolynomialEvaluation
  rw [AddMonoidHom.map_trace, gaussian_symbolic_matrix_word_evaluation]

theorem gaussian_matrix_word_trace_integrable (n : ℕ) (w : List Bool) :
    Integrable (fun x => (gaussianMatrixWord w x).trace) (gaussianSquareMatrixLaw n) := by
  have hEq : gaussianPolynomialEvaluation (gaussianSymbolicMatrixWord n w).trace =
      fun x => (gaussianMatrixWord w x).trace :=
    funext (gaussian_symbolic_word_trace_evaluation w)
  rw [← hEq]
  exact gaussian_polynomial_evaluation_integrable _

theorem gaussian_matrix_word_trace_integral (n : ℕ) (w : List Bool) :
    (∫ x, (gaussianMatrixWord w x).trace ∂gaussianSquareMatrixLaw n) =
      gaussianPolynomialMean (gaussianSymbolicMatrixWord n w).trace := by
  simp only [← gaussian_symbolic_word_trace_evaluation]
  exact gaussian_polynomial_evaluation_integral _

theorem gaussian_matrix_word_trace_integral_zero (n : ℕ) (w : List Bool)
    (hw : gaussianMatrixWordImbalance w ≠ 0) :
    (∫ x, (gaussianMatrixWord w x).trace ∂gaussianSquareMatrixLaw n) = 0 := by
  rw [gaussian_matrix_word_trace_integral]
  exact gaussian_homogeneous_polynomial_mean_zero _
    (gaussian_symbolic_word_trace_homogeneous n w) hw

theorem gaussian_matrix_word_trace_count_mismatch_zero (n : ℕ) (w : List Bool)
    (hw : w.count false ≠ w.count true) :
    (∫ x, (gaussianMatrixWord w x).trace ∂gaussianSquareMatrixLaw n) = 0 := by
  apply gaussian_matrix_word_trace_integral_zero n w
  rw [gaussian_matrix_word_imbalance_counts]
  intro h
  apply hw
  exact_mod_cast (sub_eq_zero.mp h)

end CircularLaw
