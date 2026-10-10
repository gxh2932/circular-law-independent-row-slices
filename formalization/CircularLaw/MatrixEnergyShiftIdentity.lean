import CircularLaw.GaussianCoordinateMoments

/-!
# Exact energy of a shifted matrix

The cross term is the real part of the actual matrix trace. This identity
keeps the diagonal term and its dimension factor exactly, rather than
bounding the shift by a triangle inequality.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem square_matrix_energy_shift_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) :
    squareMatrixEnergy (A - z • 1) =
      squareMatrixEnergy A + (n : ℝ) * ‖z‖ ^ 2 - 2 * (A.trace * star z).re := by
  have hEntry (i j : Fin n) : ‖(A - z • 1) i j‖ ^ 2 =
      ‖A i j‖ ^ 2 + if i = j then ‖z‖ ^ 2 - 2 * (A i j * star z).re else 0 := by
    by_cases hij : i = j
    · simp [Matrix.sub_apply, Matrix.smul_apply, hij, complex_norm_sub_square_identity]
      ring
    · simp [Matrix.sub_apply, Matrix.smul_apply, hij]
  have hTrace : (∑ i, (A i i * star z).re) = (A.trace * star z).re := by
    simp only [Matrix.trace, Matrix.diag, Finset.sum_mul, Complex.re_sum]
  calc
    _ = squareMatrixEnergy A + ∑ i, (‖z‖ ^ 2 - 2 * (A i i * star z).re) := by
      simp only [squareMatrixEnergy, hEntry, Finset.sum_add_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hTrace]
      ring

end CircularLaw
