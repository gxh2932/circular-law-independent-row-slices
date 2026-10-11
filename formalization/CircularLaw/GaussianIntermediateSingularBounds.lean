import CircularLaw.GaussianRectangularDistances
import CircularLaw.GaussianRowRestriction
import CircularLaw.ComplexRowDistanceScaling
import CircularLaw.SingularValueCounting

/-!
# Actual intermediate Gaussian singular-value bounds

The negative second moment and row interlacing turn common row distances
into lower bounds for each retained position of the square matrix.
Exact row marginals and scaling give a uniform probability bound for the
actual independent-entry Gaussian law and every deterministic shift.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem rectangular_singular_square_bound_of_row_distances {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℂ) {a : ℝ} (ha : 0 < a)
    (hDistance : ∀ i, a ≤ finiteRowDistance (complexConjugateRows A) i ^ 2) (j : Fin k) :
    a * ((k - j.val : ℕ) : ℝ) / k ≤ orderedRectangularSingularValues A j ^ 2 := by
  have hPos (i : Fin k) : 0 < finiteRowDistance (complexConjugateRows A) i := by
    nlinarith [hDistance i, finite_row_distance_nonneg (complexConjugateRows A) i]
  have hMoment := rectangular_negative_second_moment_sq_bound A ha hDistance
  have h := antitone_inverse_moment_square_bound (orderedRectangularSingularValues A)
    (orderedRectangularSingularValues_antitone A)
    (rectangular_singular_values_pos_of_row_distances A hPos) (Real.sqrt_pos.mpr ha)
    (by simpa only [Real.sq_sqrt ha.le] using hMoment) j
  simpa only [Real.sq_sqrt ha.le] using h

theorem square_singular_square_bound_of_restricted_row_distances {k n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (f : Fin k ↪ Fin n) {a : ℝ} (ha : 0 < a)
    (hDistance : ∀ i, a ≤ finiteRowDistance (complexConjugateRows (matrixRowRestriction A f)) i ^ 2)
    (i : Fin k) (j : Fin n) (hIndex : i.val = j.val) :
    a * ((k - i.val : ℕ) : ℝ) / k ≤ orderedSquareSingularValues A j ^ 2 :=
  (rectangular_singular_square_bound_of_row_distances _ ha hDistance i).trans
    (pow_le_pow_left₀ (orderedRectangularSingularValues_nonneg _ i)
      (row_restriction_singular_value_le A f i j hIndex) 2)

theorem gaussian_scaled_shifted_square_intermediate_tail {m n : ℕ} (hmn : m < n)
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (c • (gaussianSquareMatrix x + B))
          (Fin.castLE (Nat.succ_le_of_lt hmn) j) ^ 2 <
            ‖c‖ ^ 2 * (n - m : ℕ) * ((m + 1 - j.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ))} ≤
      (m + 1 : ℕ) * (1 / 2 : ℝ) ^ (n - m) := by
  let f : Fin (m + 1) ↪ Fin n := Fin.castLEEmb (Nat.succ_le_of_lt hmn)
  let B' := matrixRowRestriction B f
  let select : GaussianSquareSample n → GaussianRowsSample (m + 1) n := fun x i j => x (f i, j)
  let bad : Set (GaussianRowsSample (m + 1) n) :=
    {y | ∃ i, finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B' y)) i ^ 2 ≤
      (n - m : ℕ) / (8 : ℝ)}
  have hSelect : Measurable select :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => measurable_pi_apply (f i, j)))
  have hMap := map_measureReal_apply (μ := gaussianSquareMatrixLaw n) hSelect
    (gaussian_conjugate_row_distances_bad_measurable B' ((n - m : ℕ) / (8 : ℝ)))
  rw [gaussian_square_row_restriction_law f] at hMap
  apply (measureReal_mono (μ := gaussianSquareMatrixLaw n) (s₂ := select ⁻¹' bad) ?_).trans
    (hMap.symm.trans_le (gaussian_conjugate_row_distances_lower_eighth_tail B' hmn))
  rintro x ⟨j, hj⟩
  by_contra hBad
  have hCodim : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hNorm : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  have hRawDistance (i : Fin (m + 1)) : (n - m : ℕ) / (8 : ℝ) ≤
      finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B' (select x))) i ^ 2 :=
    (lt_of_not_ge (fun hi => hBad ⟨i, hi⟩)).le
  have hRowMatrix : matrixRowRestriction (c • (gaussianSquareMatrix x + B)) f =
      c • gaussianShiftedRowMatrix B' (select x) := by
    ext i l
    rfl
  have hScaledDistance (i : Fin (m + 1)) : ‖c‖ ^ 2 * ((n - m : ℕ) / (8 : ℝ)) ≤
      finiteRowDistance (complexConjugateRows
        (matrixRowRestriction (c • (gaussianSquareMatrix x + B)) f)) i ^ 2 := by
    rw [hRowMatrix, complex_conjugate_row_distance_smul _ hc, mul_pow]
    exact mul_le_mul_of_nonneg_left (hRawDistance i) hNorm.le
  have hBound := square_singular_square_bound_of_restricted_row_distances
    (c • (gaussianSquareMatrix x + B)) f (mul_pos hNorm (by positivity)) hScaledDistance
      j (Fin.castLE (Nat.succ_le_of_lt hmn) j) rfl
  have hThreshold : ‖c‖ ^ 2 * ((n - m : ℕ) / (8 : ℝ)) * ((m + 1 - j.val : ℕ) : ℝ) / (m + 1 : ℕ) =
      ‖c‖ ^ 2 * (n - m : ℕ) * ((m + 1 - j.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ)) := by ring
  rw [hThreshold] at hBound
  exact not_lt_of_ge hBound hj

theorem normalized_shifted_gaussian_matrix_eq_scaled_raw {n : ℕ} (hn : 0 < n)
    (z : ℂ) (x : GaussianSquareSample n) :
    normalizedShiftedGaussianMatrix z x = (Real.sqrt (n : ℝ) : ℂ)⁻¹ •
      (gaussianSquareMatrix x + (-((Real.sqrt (n : ℝ) : ℂ) * z)) • 1) := by
  have hRoot : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  rw [smul_add, smul_smul, mul_neg, ← mul_assoc, inv_mul_cancel₀ hRoot, one_mul,
    neg_smul, ← sub_eq_add_neg]
  rfl

theorem gaussian_normalized_shift_intermediate_tail {m n : ℕ} (hmn : m < n) (z : ℂ) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x)
          (Fin.castLE (Nat.succ_le_of_lt hmn) j) ^ 2 <
            (n - m : ℕ) * ((m + 1 - j.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ) * n)} ≤
      (m + 1 : ℕ) * (1 / 2 : ℝ) ^ (n - m) := by
  have hn : 0 < n := (Nat.zero_le m).trans_lt hmn
  have hScale : (Real.sqrt (n : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne')
  have h := gaussian_scaled_shifted_square_intermediate_tail hmn
    ((-((Real.sqrt (n : ℝ) : ℂ) * z)) • 1) (Real.sqrt (n : ℝ) : ℂ)⁻¹ hScale
  have hThreshold (j : Fin (m + 1)) :
      1 / (n : ℝ) * (n - m : ℕ) * ((m + 1 - j.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ)) =
        (n - m : ℕ) * ((m + 1 - j.val : ℕ) : ℝ) / (8 * (m + 1 : ℕ) * n) := by ring
  simpa only [inverse_sqrt_dimension_norm_sq, hThreshold,
    ← normalized_shifted_gaussian_matrix_eq_scaled_raw hn z] using h

end CircularLaw
