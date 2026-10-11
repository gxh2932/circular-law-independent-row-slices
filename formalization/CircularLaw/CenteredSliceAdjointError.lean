import CircularLaw.RestrictedNormTheorem
import CircularLaw.ComplexMatrixOperatorBounds
import CircularLaw.RowSliceFullAdjointSmallBall
import CircularLaw.ScalarMeanGrid

/-!
# Mean-corrected approximations for the actual shifted adjoint

The expected matrix contributes only through the coordinate sum. Removing
the mean of a rounding error therefore permits use of the checked centered
operator norm. Only the remaining scalar rounding error pays the full degree.
The statements apply to sparse, truncated, and ordinary coordinate grids.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def centeredSliceComplexMatrix {n d : ℕ} (rows : RowSliceMatrix n d) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => centeredRow (rows i) j

theorem centered_slice_complex_operator_eq {n d : ℕ} (rows : RowSliceMatrix n d) :
    complexMatrixOperator (centeredSliceComplexMatrix rows) =
      normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows) := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [complex_matrix_operator_apply, normComplexMatrixOperatorReal_apply,
    centeredRectangularSliceMatrixReal_coe, centeredSliceComplexMatrix]

theorem centered_slice_adjoint_apply {n d : ℕ} (rows : RowSliceMatrix n d)
    (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (centeredSliceComplexMatrix rows).conjTranspose.toEuclideanLin x j =
      (∑ i, rowEntry (rows i) j * x i) - (d : ℂ) / n * ∑ i, x i := by
  change (∑ i, star (centeredRow (rows i) j) * x i) = _
  simp [centeredRow, rowEntry, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

theorem shifted_slice_adjoint_zero_sum_bound {n d : ℕ} (rows : RowSliceMatrix n d)
    (ζ : ℂ) {B : ℝ}
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B)
    (x : EuclideanSpace ℂ (Fin n)) (hSum : ∑ i, x i = 0) :
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤
      (B + ‖ζ‖) * ‖x‖ := by
  have hAction : (fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x =
      (centeredSliceComplexMatrix rows).conjTranspose.toEuclideanLin x - star ζ • x := by
    ext j
    simp only [shifted_slice_adjoint_apply_eq_full_sum, centered_slice_adjoint_apply,
      hSum, mul_zero, sub_zero, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hBound := (complexMatrixOperator (centeredSliceComplexMatrix rows).conjTranspose).le_opNorm x
  rw [complex_matrix_operator_conjTranspose_norm, centered_slice_complex_operator_eq] at hBound
  change ‖(centeredSliceComplexMatrix rows).conjTranspose.toEuclideanLin x‖ ≤ _ at hBound
  rw [hAction]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, norm_star]
  calc
    _ ≤ B * ‖x‖ + ‖ζ‖ * ‖x‖ := add_le_add
      (hBound.trans (mul_le_mul_of_nonneg_right hNorm (norm_nonneg x))) le_rfl
    _ = _ := by ring

theorem euclidean_constant_norm {n : ℕ} (a : ℂ) :
    ‖(WithLp.toLp 2 (fun _ : Fin n => a) : EuclideanSpace ℂ (Fin n))‖ = Real.sqrt n * ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem shifted_slice_adjoint_constant_bound {n d : ℕ} (hn : 0 < n)
    (rows : RowSliceMatrix n d) (ζ a : ℂ) {B : ℝ}
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B) :
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun _ => a))‖ ≤ (B + d + ‖ζ‖) * Real.sqrt n * ‖a‖ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun _ => a)
  have hAction : (fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x =
      (centeredSliceComplexMatrix rows).conjTranspose.toEuclideanLin x + ((d : ℂ) - star ζ) • x := by
    ext j
    simp only [shifted_slice_adjoint_apply_eq_full_sum, centered_slice_adjoint_apply,
      x, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring_nf
    simp only [mul_comm]
  have hBound := (complexMatrixOperator (centeredSliceComplexMatrix rows).conjTranspose).le_opNorm x
  rw [complex_matrix_operator_conjTranspose_norm, centered_slice_complex_operator_eq] at hBound
  change ‖(centeredSliceComplexMatrix rows).conjTranspose.toEuclideanLin x‖ ≤ _ at hBound
  have hScalar : ‖(d : ℂ) - star ζ‖ ≤ (d : ℝ) + ‖ζ‖ := by
    simpa only [Complex.norm_natCast, norm_star] using norm_sub_le (d : ℂ) (star ζ)
  change ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ _
  rw [hAction]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  calc
    _ ≤ B * ‖x‖ + ((d : ℝ) + ‖ζ‖) * ‖x‖ := add_le_add
      (hBound.trans (mul_le_mul_of_nonneg_right hNorm (norm_nonneg x)))
      (mul_le_mul_of_nonneg_right hScalar (norm_nonneg x))
    _ = _ := by rw [show ‖x‖ = Real.sqrt n * ‖a‖ from euclidean_constant_norm a]; ring

def coordinateMean {n : ℕ} (v : Fin n → ℂ) : ℂ := (∑ i, v i) / (n : ℂ)

def meanCenteredVector {n : ℕ} (v : Fin n → ℂ) (i : Fin n) : ℂ := v i - coordinateMean v

theorem coordinateMean_norm_le {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ)
    {δ : ℝ} (hBound : ∀ i, ‖v i‖ ≤ δ) : ‖coordinateMean v‖ ≤ δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coordinateMean, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum (fun i _ => hBound i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem meanCenteredVector_sum {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    ∑ i, meanCenteredVector v i = 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [meanCenteredVector, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, coordinateMean]
  field_simp
  ring

theorem meanCenteredVector_euclidean_bound {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hBound : ∀ i, ‖v i‖ ≤ δ) :
    ‖(WithLp.toLp 2 (meanCenteredVector v) : EuclideanSpace ℂ (Fin n))‖ ≤ 2 * Real.sqrt n * δ := by
  have hMean := coordinateMean_norm_le hn v hBound
  have hCentered : ∀ i, ‖meanCenteredVector v i‖ ≤ 2 * δ := by
    intro i
    exact (norm_sub_le _ _).trans (by linarith [hBound i])
  simpa only [Fintype.card_fin, mul_comm, mul_left_comm, mul_assoc] using
    euclidean_norm_le_uniform (meanCenteredVector v) (by positivity : 0 ≤ 2 * δ) hCentered

theorem shifted_slice_adjoint_mean_corrected_error {n d : ℕ} (hn : 0 < n)
    (rows : RowSliceMatrix n d) (ζ : ℂ) {B δ ε : ℝ} (hδ : 0 ≤ δ)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ B)
    (x u : Fin n → ℂ) (c w : ℂ) (hBound : ∀ i, ‖x i - u i‖ ≤ δ)
    (hMean : ‖c + coordinateMean (fun i => x i - u i) - w‖ ≤ ε) :
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)))‖ ≤
      (B + ‖ζ‖) * (2 * Real.sqrt n * δ) +
        (B + d + ‖ζ‖) * Real.sqrt n * ε := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hNorm
  let v : Fin n → ℂ := fun i => x i - u i
  let a := c + coordinateMean v - w
  have hDecomp : (WithLp.toLp 2 (fun i => (x i + c) - (u i + w)) : EuclideanSpace ℂ (Fin n)) =
      WithLp.toLp 2 (meanCenteredVector v) + WithLp.toLp 2 (fun _ => a) := by
    ext i
    change (x i + c) - (u i + w) = (x i - u i - coordinateMean v) + (c + coordinateMean v - w)
    ring
  rw [hDecomp, map_add]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((shifted_slice_adjoint_zero_sum_bound rows ζ hNorm _ (meanCenteredVector_sum hn v)).trans
      (mul_le_mul_of_nonneg_left (meanCenteredVector_euclidean_bound hn v hδ hBound) (by positivity)))
    ((shifted_slice_adjoint_constant_bound hn rows ζ a hNorm).trans
      (mul_le_mul_of_nonneg_left hMean (by positivity)))

end CircularLaw
