import CircularLaw.SquareLogPrefixComparison

/-!
# The determinant and the literal ordered singular values

The product of the ordered singular values is exactly the absolute
determinant. Consequently a zero singular value is equivalent to a zero
determinant, and on the nonsingular event the logarithmic determinant
equals the sum of the singular-value logarithms.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

theorem squareGram_det_real_eq_singular_product_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (A * A.conjTranspose).det.re = (∏ j, orderedSquareSingularValues A j) ^ 2 := by
  let hA := Matrix.isHermitian_mul_conjTranspose_self A
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hDet : (A * A.conjTranspose).det.re =
      ∏ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j := by
    rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    simp only [Matrix.IsHermitian.eigenvalues]
    exact (e.symm.prod_comp hA.eigenvalues₀)
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin _).symm
  rw [hDet, ← c.prod_comp]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  exact (orderedSquareSingularValues_sq A j).symm

theorem square_singular_values_product_eq_norm_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∏ j, orderedSquareSingularValues A j) = ‖A.det‖ := by
  have hGram : (A * A.conjTranspose).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  have hSq := squareGram_det_real_eq_singular_product_sq A
  have hNonneg : 0 ≤ ∏ j, orderedSquareSingularValues A j :=
    Finset.prod_nonneg (fun j _ => orderedSquareSingularValues_nonneg A j)
  have hNorm := norm_nonneg A.det
  nlinarith

theorem square_singular_has_zero_iff_det_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    empiricalHasZero (squareSingularValuesNNReal A) ↔ A.det = 0 := by
  rw [← norm_eq_zero, ← square_singular_values_product_eq_norm_det]
  simp only [empiricalHasZero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, congrArg (fun t : ℝ≥0 => (t : ℝ)) hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, NNReal.eq hj⟩

theorem square_singular_values_pos_of_det_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hDet : A.det ≠ 0) :
    ∀ j, 0 < orderedSquareSingularValues A j := by
  intro j
  have hZero := (square_singular_has_zero_iff_det_zero A).not.mpr hDet
  have hPos : 0 < squareSingularValuesNNReal A j :=
    lt_of_le_of_ne (zero_le _) (fun h => hZero ⟨j, h.symm⟩)
  exact_mod_cast hPos

theorem square_log_norm_det_eq_singular_log_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hDet : A.det ≠ 0) :
    Real.log ‖A.det‖ = ∑ j, Real.log (orderedSquareSingularValues A j) := by
  rw [← square_singular_values_product_eq_norm_det]
  exact Real.log_prod (fun j _ => (square_singular_values_pos_of_det_ne_zero A hDet j).ne')

theorem square_negative_log_mean_eq_log_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hDet : A.det ≠ 0) :
    squareNegativeLogMean A = -(Real.log ‖A.det‖ / n) := by
  rw [squareNegativeLogMean, square_log_norm_det_eq_singular_log_sum A hDet, neg_div]

end CircularLaw
