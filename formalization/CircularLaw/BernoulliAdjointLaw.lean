import CircularLaw.BernoulliSquareMatrixLaw

/-!
# Adjoint invariance of the actual Bernoulli square law

Swapping the two entry indices preserves the product law. Since every
entry is real, its sample matrix is exactly the adjoint of the original
matrix. Arbitrary matrix events therefore have the same probability.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def bernoulliSquareTransposeSample {N : ℕ} (x : BernoulliSquareSample N) :
    BernoulliSquareSample N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => Bool) (Equiv.prodComm _ _) x

theorem bernoulli_square_transpose_sample_apply {N : ℕ}
    (x : BernoulliSquareSample N) (i j : Fin N) :
    bernoulliSquareTransposeSample x (i, j) = x (j, i) := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Bool) (Equiv.prodComm _ _) x (j, i)

theorem bernoulli_square_transpose_sample_involutive {N : ℕ} :
    Function.Involutive (@bernoulliSquareTransposeSample N) := by
  intro x
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [bernoulli_square_transpose_sample_apply]

theorem bernoulli_square_transpose_measure_preserving (N : ℕ)
    (p : ℝ≥0) (hp : p ≤ 1) :
    MeasurePreserving (@bernoulliSquareTransposeSample N)
      (bernoulliSquareMatrixLaw N p hp) (bernoulliSquareMatrixLaw N p hp) :=
  measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => bernoulliCoordinateLaw p hp)
    (Equiv.prodComm _ _)

theorem bernoulli_square_transpose_matrix_eq_adjoint {N : ℕ}
    (x : BernoulliSquareSample N) :
    bernoulliSquareMatrix (bernoulliSquareTransposeSample x) = (bernoulliSquareMatrix x)ᴴ := by
  ext i j
  simp only [bernoulliSquareMatrix, Matrix.conjTranspose_apply,
    bernoulli_square_transpose_sample_apply]
  cases x (j, i) <;> simp

theorem bernoulli_square_adjoint_event_probability {N : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (E : Matrix (Fin N) (Fin N) ℂ → Prop) :
    (bernoulliSquareMatrixLaw N p hp).real {x | E ((bernoulliSquareMatrix x)ᴴ)} =
      (bernoulliSquareMatrixLaw N p hp).real {x | E (bernoulliSquareMatrix x)} := by
  have hEvent : {x : BernoulliSquareSample N | E ((bernoulliSquareMatrix x)ᴴ)} =
      bernoulliSquareTransposeSample ⁻¹' {x | E (bernoulliSquareMatrix x)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, bernoulli_square_transpose_matrix_eq_adjoint]
  rw [hEvent]
  have hMeas : MeasurableSet {x : BernoulliSquareSample N | E (bernoulliSquareMatrix x)} :=
    (Set.to_countable _).measurableSet
  exact congrArg ENNReal.toReal ((bernoulli_square_transpose_measure_preserving N p hp).measure_preimage
    hMeas.nullMeasurableSet)

theorem sparse_bernoulli_adjoint_event_probability {N d : ℕ}
    (E : Matrix (Fin N) (Fin N) ℂ → Prop) :
    (sparseBernoulliMatrixLaw N d).real {x | E ((bernoulliSquareMatrix x)ᴴ)} =
      (sparseBernoulliMatrixLaw N d).real {x | E (bernoulliSquareMatrix x)} :=
  bernoulli_square_adjoint_event_probability _ _ E

end CircularLaw
