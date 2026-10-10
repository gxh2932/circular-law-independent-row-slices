import CircularLaw.GaussianSmallDistanceTails
import CircularLaw.GaussianIntermediateSingularBounds

/-!
# A polynomial lower bound for actual shifted Gaussian singular values

Arbitrary small-ball thresholds pass through the negative second moment
and row restriction. At every deterministic shift the event that any
normalized singular value is below n^(-2) has probability at most e/n.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_scaled_shifted_square_small_tail {m n : ℕ} (hmn : m < n)
    (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) {u : ℝ} (hu : 0 < u) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (c • (gaussianSquareMatrix x + B))
          (Fin.castLE (Nat.succ_le_of_lt hmn) j) ^ 2 <
            ‖c‖ ^ 2 * u * ((m + 1 - j.val : ℕ) : ℝ) / (m + 1 : ℕ)} ≤
      (m + 1 : ℕ) * (Real.exp 1 * u) := by
  let f : Fin (m + 1) ↪ Fin n := Fin.castLEEmb (Nat.succ_le_of_lt hmn)
  let B' := matrixRowRestriction B f
  let select : GaussianSquareSample n → GaussianRowsSample (m + 1) n := fun x i j => x (f i, j)
  let bad : Set (GaussianRowsSample (m + 1) n) :=
    {y | ∃ i, finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B' y)) i ^ 2 ≤ u}
  have hSelect : Measurable select :=
    measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => measurable_pi_apply (f i, j)))
  have hMap := map_measureReal_apply (μ := gaussianSquareMatrixLaw n) hSelect
    (gaussian_conjugate_row_distances_bad_measurable B' u)
  rw [gaussian_square_row_restriction_law f] at hMap
  apply (measureReal_mono (μ := gaussianSquareMatrixLaw n) (s₂ := select ⁻¹' bad) ?_).trans
    (hMap.symm.trans_le (gaussian_conjugate_row_distances_linear_tail B' hmn hu))
  rintro x ⟨j, hj⟩
  by_contra hBad
  have hNorm : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  have hRawDistance (i : Fin (m + 1)) : u ≤
      finiteRowDistance (complexConjugateRows (gaussianShiftedRowMatrix B' (select x))) i ^ 2 :=
    (lt_of_not_ge (fun hi => hBad ⟨i, hi⟩)).le
  have hRowMatrix : matrixRowRestriction (c • (gaussianSquareMatrix x + B)) f =
      c • gaussianShiftedRowMatrix B' (select x) := by
    ext i l
    rfl
  have hScaledDistance (i : Fin (m + 1)) : ‖c‖ ^ 2 * u ≤
      finiteRowDistance (complexConjugateRows
        (matrixRowRestriction (c • (gaussianSquareMatrix x + B)) f)) i ^ 2 := by
    rw [hRowMatrix, complex_conjugate_row_distance_smul _ hc, mul_pow]
    exact mul_le_mul_of_nonneg_left (hRawDistance i) hNorm.le
  exact not_lt_of_ge (square_singular_square_bound_of_restricted_row_distances
    (c • (gaussianSquareMatrix x + B)) f (mul_pos hNorm hu) hScaledDistance
      j (Fin.castLE (Nat.succ_le_of_lt hmn) j) rfl) hj

theorem gaussian_normalized_shift_small_tail {m n : ℕ} (hmn : m < n) (z : ℂ)
    {u : ℝ} (hu : 0 < u) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x)
          (Fin.castLE (Nat.succ_le_of_lt hmn) j) ^ 2 <
            u * ((m + 1 - j.val : ℕ) : ℝ) / ((m + 1 : ℕ) * n)} ≤
      (m + 1 : ℕ) * (Real.exp 1 * u) := by
  have hn : 0 < n := (Nat.zero_le m).trans_lt hmn
  have hScale : (Real.sqrt (n : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne')
  have h := gaussian_scaled_shifted_square_small_tail hmn
    ((-((Real.sqrt (n : ℝ) : ℂ) * z)) • 1) (Real.sqrt (n : ℝ) : ℂ)⁻¹ hScale hu
  have hThreshold (j : Fin (m + 1)) :
      (1 / (n : ℝ)) * u * ((m + 1 - j.val : ℕ) : ℝ) / (m + 1 : ℕ) =
        u * ((m + 1 - j.val : ℕ) : ℝ) / ((m + 1 : ℕ) * n) := by ring
  simpa only [inverse_sqrt_dimension_norm_sq, hThreshold,
    ← normalized_shifted_gaussian_matrix_eq_scaled_raw hn z] using h

theorem gaussian_normalized_shift_smallest_tail {n : ℕ} (hn : 0 < n) (z : ℂ)
    {t : ℝ} (ht : 0 < t) :
    (gaussianSquareMatrixLaw n).real
      {x | ∃ j : Fin n, orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < t} ≤
        Real.exp 1 * (n : ℝ) ^ 3 * t ^ 2 := by
  cases n with
  | zero => omega
  | succ m =>
    have hnR : (0 : ℝ) < m + 1 := by positivity
    have h := gaussian_normalized_shift_small_tail (Nat.lt_succ_self m) z
      (u := (m + 1 : ℝ) ^ 2 * t ^ 2) (by positivity)
    have hThreshold (j : Fin (m + 1)) :
        (m + 1 : ℝ) ^ 2 * t ^ 2 * ((m + 1 - j.val : ℕ) : ℝ) /
          ((m + 1 : ℝ) * (m + 1 : ℝ)) = t ^ 2 * (m + 1 - j.val : ℕ) := by
      field_simp
    have hSubset :
      {x : GaussianSquareSample (m + 1) | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j < t} ⊆
      {x | ∃ j : Fin (m + 1),
        orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j ^ 2 <
          t ^ 2 * (m + 1 - j.val : ℕ)} := by
      rintro x ⟨j, hj⟩
      have hRank : (1 : ℝ) ≤ (m + 1 - j.val : ℕ) := by
        exact_mod_cast (by have hjn := j.isLt; omega : 1 ≤ m + 1 - j.val)
      exact ⟨j, ((sq_lt_sq₀ (orderedSquareSingularValues_nonneg _ _) ht.le).mpr hj).trans_le
        (by nlinarith)⟩
    apply (measureReal_mono (μ := gaussianSquareMatrixLaw (m + 1)) hSubset).trans
    simpa only [Fin.castLE_refl, Nat.cast_add, Nat.cast_one, Nat.cast_succ, hThreshold,
      show (m + 1 : ℝ) * (Real.exp 1 * ((m + 1 : ℝ) ^ 2 * t ^ 2)) =
        Real.exp 1 * (m + 1 : ℝ) ^ 3 * t ^ 2 by ring] using h

def gaussianSmallestPolynomialBad (z : ℂ) (n : ℕ) : Set (GaussianSquareSample n) :=
  {x | ∃ j : Fin n, orderedSquareSingularValues (normalizedShiftedGaussianMatrix z x) j <
    ((n : ℝ) ^ 2)⁻¹}

theorem gaussian_smallest_polynomial_probability_bound {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (gaussianSquareMatrixLaw n).real (gaussianSmallestPolynomialBad z n) ≤ Real.exp 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := gaussian_normalized_shift_smallest_tail hn z
    (inv_pos.mpr (sq_pos_of_pos hnR))
  convert h using 1
  field_simp

theorem gaussian_smallest_polynomial_bad_probability_tendsto (z : ℂ) :
    Tendsto (fun n => (gaussianSquareMatrixLaw n).real (gaussianSmallestPolynomialBad z n))
      atTop (𝓝 0) := by
  have hBound : Tendsto (fun n : ℕ => Real.exp 1 / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
    (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact gaussian_smallest_polynomial_probability_bound hn z

end CircularLaw
