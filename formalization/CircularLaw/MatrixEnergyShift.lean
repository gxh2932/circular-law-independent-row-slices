import CircularLaw.SquareSingularSecondMoment

/-!
# Hilbert--Schmidt energy under normalization and a spectral shift

The scalar and diagonal formulas are literal entrywise matrix identities.
They apply to the uncentered Bernoulli comparator from Section 9.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix

namespace CircularLaw

theorem squareMatrixEnergy_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    squareMatrixEnergy (c • A) = ‖c‖ ^ 2 * squareMatrixEnergy A := by
  simp only [squareMatrixEnergy, Matrix.smul_apply, norm_smul, mul_pow,
    Finset.mul_sum]

theorem squareMatrixEnergy_one (n : ℕ) :
    squareMatrixEnergy (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  have hEntry (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 =
      if i = j then (1 : ℝ) else 0 := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp [squareMatrixEnergy, hEntry]

theorem complex_norm_sub_sq_le (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hTriangle := norm_sub_le a b
  have hSquare := (sq_le_sq₀ (norm_nonneg (a - b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr hTriangle
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem squareMatrixEnergy_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    squareMatrixEnergy (A - B) ≤ 2 * squareMatrixEnergy A + 2 * squareMatrixEnergy B := by
  calc
    _ ≤ ∑ i, ∑ j, (2 * ‖A i j‖ ^ 2 + 2 * ‖B i j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact complex_norm_sub_sq_le _ _
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, squareMatrixEnergy]

theorem squareMatrixEnergy_shift_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    squareMatrixEnergy (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤
      2 * squareMatrixEnergy A + 2 * n * ‖z‖ ^ 2 := by
  have h := squareMatrixEnergy_sub_le A (z • (1 : Matrix (Fin n) (Fin n) ℂ))
  rw [squareMatrixEnergy_smul, squareMatrixEnergy_one] at h
  nlinarith

theorem squareMatrixEnergy_sqrt_normalization {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    squareMatrixEnergy ((Real.sqrt (d : ℝ) : ℂ)⁻¹ • A) = squareMatrixEnergy A / d := by
  rw [squareMatrixEnergy_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  exact inv_mul_eq_div _ _

end CircularLaw
