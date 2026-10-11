import CircularLaw.GaussianSingularMoments

/-!
# Exact fourth trace identity for a scalar matrix shift

The Gram-square trace is expanded without commuting matrix factors.
Only cyclicity of the trace identifies the two orders of each cross term.
The resulting identity keeps all unbalanced direct/adjoint words.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem hermitian_trace_pow_eq_ofReal_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ((A ^ k).trace.re : ℂ) := by
  rw [hermitian_trace_pow_eq_sum A hA k]
  simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_sum]

theorem square_gram_trace_eq_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A * A.conjTranspose).trace = (squareMatrixEnergy A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    squareMatrixEnergy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa using complex_balanced_power_eq_norm_power (A i j) 1

theorem square_gram_trace_pow_smul_complex {n : ℕ} (c : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (((c • A) * (c • A).conjTranspose) ^ k).trace =
      (‖c‖ ^ (2 * k) : ℝ) * ((A * A.conjTranspose) ^ k).trace := by
  have hGram : (c • A) * (c • A).conjTranspose =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (A * A.conjTranspose) := by
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    simpa using complex_balanced_power_eq_norm_power c 1
  rw [hGram, smul_pow, Matrix.trace_smul, smul_eq_mul]
  simp only [← Complex.ofReal_pow, pow_mul]

theorem matrix_trace_sum_four_square {n : ℕ} (X Y Z W : Matrix (Fin n) (Fin n) ℂ) :
    ((X + Y + Z + W) ^ 2).trace =
      (X ^ 2).trace + (Y ^ 2).trace + (Z ^ 2).trace + (W ^ 2).trace +
      2 * (X * Y).trace + 2 * (X * Z).trace + 2 * (X * W).trace +
      2 * (Y * Z).trace + 2 * (Y * W).trace + 2 * (Z * W).trace := by
  simp only [pow_two, add_mul, mul_add, Matrix.trace_add]
  rw [Matrix.trace_mul_comm Y X, Matrix.trace_mul_comm Z X, Matrix.trace_mul_comm W X,
    Matrix.trace_mul_comm Z Y, Matrix.trace_mul_comm W Y, Matrix.trace_mul_comm W Z]
  ring

theorem square_gram_shift_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (A - z • 1) * (A - z • 1).conjTranspose =
      A * A.conjTranspose + (-star z) • A + (-z) • A.conjTranspose +
        (z * star z) • 1 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul,
    Matrix.one_mul, Matrix.mul_one, neg_smul]
  rw [mul_comm (star z) z]
  abel

theorem square_gram_shift_trace_square {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (((A - z • 1) * (A - z • 1).conjTranspose) ^ 2).trace =
      ((A * A.conjTranspose) ^ 2).trace +
      star z ^ 2 * (A ^ 2).trace + z ^ 2 * (A.conjTranspose ^ 2).trace +
      (z * star z) ^ 2 * n -
      2 * star z * ((A * A.conjTranspose) * A).trace -
      2 * z * ((A * A.conjTranspose) * A.conjTranspose).trace +
      4 * (z * star z) * (A * A.conjTranspose).trace -
      2 * (z * star z) * star z * A.trace -
      2 * (z * star z) * z * A.conjTranspose.trace := by
  rw [square_gram_shift_identity, matrix_trace_sum_four_square]
  simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.mul_one, one_pow, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one,
    Fintype.card_fin]
  ring

end CircularLaw
