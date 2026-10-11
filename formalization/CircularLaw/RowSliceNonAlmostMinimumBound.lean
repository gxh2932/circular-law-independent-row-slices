import CircularLaw.RowSliceScalarSmallBall
import CircularLaw.LeaveOneOutDistanceProbability

/-!
# Minimum-value reduction with the slice scalar estimate discharged

The fully proved fixed-degree slice small-ball estimate gives a uniform
inverse-square-root degree bound for every non-almost-constant vector.
The actual leave-one-out distance and smallest-singular-value reductions
therefore retain only the square and leave-one-out almost-constant
failure probabilities. These two probabilities are not asserted here.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem exp_negative_degree_le_inverse_sqrt {d : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) :
    Real.exp (-a * d) ≤ (1 / a) / Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot : Real.sqrt d ≤ d := Real.sqrt_le_iff.mpr ⟨hdR.le, by nlinarith⟩
  have hExp : a * (d : ℝ) ≤ Real.exp (a * d) := by
    linarith [Real.add_one_le_exp (a * d)]
  calc
    Real.exp (-a * d) = 1 / Real.exp (a * d) := by
      rw [show -a * (d : ℝ) = -(a * d) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / (a * d) := one_div_le_one_div_of_le (mul_pos ha hdR) hExp
    _ = (1 / a) / d := by ring
    _ ≤ (1 / a) / Real.sqrt d := div_le_div_of_nonneg_left
      (by positivity) (Real.sqrt_pos.mpr hdR) hRoot

def sliceSmallBallDegreeConstant (δ : ℝ) : ℝ :=
  2 * bernoulliScalarSmallBallConstant / Real.sqrt δ + 64 / δ ^ 2

theorem slice_small_ball_degree_constant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < sliceSmallBallDegreeConstant δ := by
  unfold sliceSmallBallDegreeConstant
  exact add_pos (div_pos (mul_pos (by norm_num) bernoulli_scalar_small_ball_constant_pos)
    (Real.sqrt_pos.mpr hδ)) (div_pos (by norm_num) (sq_pos_of_pos hδ))

theorem row_slice_nonalmost_small_ball_degree_bound {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : sourceNonAlmostConstant δ ρ x) :
    rowSliceDiskConcentration (d := d) (fun j => x j) (ρ / Real.sqrt n) ≤
      sliceSmallBallDegreeConstant δ / Real.sqrt d := by
  have hTail := exp_negative_degree_le_inverse_sqrt hd
    (show 0 < δ ^ 2 / 64 by positivity)
  have hTail' : Real.exp (-δ ^ 2 * (d : ℝ) / 64) ≤
      (64 / δ ^ 2) / Real.sqrt d := by
    convert hTail using 1 <;> congr 1 <;> ring
  apply (row_slice_nonalmost_scalar_small_ball hd hSize hδ hρ x hx).trans
  apply (add_le_add (le_refl _) hTail').trans_eq
  rw [Real.sqrt_mul hδ.le]
  unfold sliceSmallBallDegreeConstant
  ring

theorem shifted_slice_row_distance_probability_with_proved_small_ball {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (ζ : ℂ) (i : Fin n)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      finiteRowDistance (complexConjugateRows (fullShiftedSliceMatrix ζ rows)) i ≤
        ρ / Real.sqrt n) ≤
      sliceSmallBallDegreeConstant δ / Real.sqrt d +
        uniformProbability (fun rows : RowSliceMatrix n d =>
          sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) := by
  apply shifted_slice_row_distance_probability_le_source_components (by omega)
    ζ i δ ρ (ρ / Real.sqrt n)
    (div_nonneg (slice_small_ball_degree_constant_pos hδ).le (Real.sqrt_nonneg d))
  intro x _ hx
  exact row_slice_nonalmost_small_ball_degree_bound hd hSize hδ hρ x hx

theorem row_slice_smallest_probability_of_almost_constant_bounds {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (ζ : ℂ) {δ ρ η κ : ℝ}
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hρ : 0 < ρ)
    (hKernel : ∀ i : Fin n, uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceLeaveOneOutAlmostConstantKernelFailure ζ rows i δ ρ) ≤ η)
    (hAlmost : uniformProbability (fun rows : RowSliceMatrix n d =>
      sourceAlmostConstantAdjointFailure (fullShiftedSliceMatrix ζ rows) δ ρ
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤ κ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows)
        ((ρ / Real.sqrt n) * ρ / Real.sqrt n)) ≤
      κ + (sliceSmallBallDegreeConstant δ / Real.sqrt d + η) / δ := by
  apply row_slice_smallest_probability_of_source_components (by omega) (by omega) ζ
    hδ hδOne hρ (div_nonneg hρ.le (Real.sqrt_nonneg n))
    (div_nonneg (slice_small_ball_degree_constant_pos hδ).le (Real.sqrt_nonneg d))
    ?_ hKernel hAlmost
  intro x _ hx
  exact row_slice_nonalmost_small_ball_degree_bound hd hSize hδ hρ x hx

end CircularLaw
