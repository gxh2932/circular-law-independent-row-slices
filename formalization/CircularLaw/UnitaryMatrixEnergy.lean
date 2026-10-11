import CircularLaw.SquareSingularSecondMoment

/-!
# Unitary changes of coordinates preserve the actual matrix energy

Both the characteristic polynomial and the literal entrywise
Hilbert--Schmidt energy are unchanged by unitary conjugation.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem unitary_conjugate_charpoly {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    (U.conjTranspose * A * U).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem unitary_conjugate_gram {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    (U.conjTranspose * A * U) * (U.conjTranspose * A * U).conjTranspose =
      U.conjTranspose * (A * A.conjTranspose) * U := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = U.conjTranspose * A * (U * U.conjTranspose) * A.conjTranspose * U := by
      noncomm_ring
    _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem unitary_conjugate_energy {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    squareMatrixEnergy (U.conjTranspose * A * U) = squareMatrixEnergy A := by
  rw [← squareGram_trace_real, ← squareGram_trace_real A, unitary_conjugate_gram A U hU]
  congr 1
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

end CircularLaw
