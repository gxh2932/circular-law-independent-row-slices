import CircularLaw.SquareSliceSingularValues
import CircularLaw.NonnegativeEmpiricalMeasure

/-!
# Second moment of the actual square singular-value measure

The ordered singular values of `A A*` have sum of squares equal to the
literal entrywise Hilbert--Schmidt energy. Thus the empirical measure in
hermitization has exactly that energy divided by the dimension.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

def squareMatrixEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem squareMatrixEnergy_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ squareMatrixEnergy A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem squareGram_trace_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A * A.conjTranspose).trace.re = squareMatrixEnergy A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, squareMatrixEnergy]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

theorem square_singular_values_sum_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ j, orderedSquareSingularValues A j ^ 2) = squareMatrixEnergy A := by
  let hA := Matrix.isHermitian_mul_conjTranspose_self A
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hTrace : (A * A.conjTranspose).trace.re =
      ∑ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j := by
    rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [Matrix.IsHermitian.eigenvalues]
    exact (e.symm.sum_comp hA.eigenvalues₀)
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin _).symm
  calc
    _ = ∑ j : Fin n, hA.eigenvalues₀ (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact orderedSquareSingularValues_sq A j
    _ = ∑ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j := c.sum_comp _
    _ = squareMatrixEnergy A := hTrace.symm.trans (squareGram_trace_real A)

def squareSingularValuesNNReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ≥0 :=
  fun j => ⟨orderedSquareSingularValues A j, orderedSquareSingularValues_nonneg A j⟩

def squareSingularMeasure {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Measure ℝ≥0 :=
  empiricalNonnegativeMeasure (squareSingularValuesNNReal A)

theorem squareSingularMeasure_probability {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : IsProbabilityMeasure (squareSingularMeasure A) :=
  empiricalNonnegativeMeasure_probability hn _

theorem squareSingularMeasure_second_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∫ t, (t : ℝ) ^ 2 ∂squareSingularMeasure A) = squareMatrixEnergy A / n := by
  rw [squareSingularMeasure, empiricalNonnegativeMeasure_integral]
  simp only [empiricalNonnegativeMean, finiteMean, Fintype.card_fin,
    squareSingularValuesNNReal, NNReal.coe_mk]
  rw [square_singular_values_sum_sq]

theorem squareSingularMeasure_second_moment_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ ∫ t, (t : ℝ) ^ 2 ∂squareSingularMeasure A := by
  rw [squareSingularMeasure_second_moment]
  exact div_nonneg (squareMatrixEnergy_nonneg A) (Nat.cast_nonneg _)

end CircularLaw
