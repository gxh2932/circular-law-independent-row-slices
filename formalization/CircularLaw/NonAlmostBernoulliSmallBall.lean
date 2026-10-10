import CircularLaw.InvertibilityDistanceGeometry
import CircularLaw.WeightedBernoulliSmallBall
import CircularLaw.BernoulliSliceMassBound

/-!
# Non-almost-constant Bernoulli scalar forms

The source coordinate-count condition supplies at least delta*n
coefficients above rho/sqrt(n). The proved weighted Bernoulli small-ball
estimate therefore gives C/sqrt(delta*n*p), uniformly in the center.
At the actual parameter p=d/n this is C/sqrt(delta*d). This probability
estimate is proved outright; it has no assumed concentration input.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem source_nonalmost_large_coordinates_nonempty {n : ℕ} (hn : 0 < n)
    {δ ρ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) :
    (Finset.univ.filter (fun i => ρ / Real.sqrt n < ‖x i‖)).Nonempty := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCount := source_nonalmost_large_coordinate_count δ ρ x hx
  apply Finset.card_pos.mp
  exact_mod_cast (mul_pos hδ hnR).trans_le hCount

theorem bernoulli_nonalmost_scalar_small_ball {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) (z : ℂ) :
    (bernoulliCubeLaw (Fin n) p hp).real {y |
      ‖(∑ i, weightedBernoulliValue (x i) (y i)) - z‖ ≤ ρ / Real.sqrt n} ≤
        bernoulliScalarSmallBallConstant / Real.sqrt (δ * n * p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRadius : 0 < ρ / Real.sqrt n := div_pos hρ (Real.sqrt_pos.mpr hnR)
  let S := Finset.univ.filter (fun i => ρ / Real.sqrt n < ‖x i‖)
  have hS : S.Nonempty := source_nonalmost_large_coordinates_nonempty hn hδ x hx
  have hCount : δ * n ≤ (S.card : ℝ) := source_nonalmost_large_coordinate_count δ ρ x hx
  have hBound := bernoulli_cube_linear_form_small_ball p hp hpPos hHalf
    (fun i => x i) S hS hRadius (fun i hi => (Finset.mem_filter.mp hi).2.le)
    (by linarith : (ρ / Real.sqrt n) / 2 ≤ ρ / Real.sqrt n) z
  simp only [div_self hRadius.ne', mul_one] at hBound
  have hRoot : Real.sqrt (δ * n * p) ≤ Real.sqrt ((S.card : ℝ) * p) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCount p.coe_nonneg)
  exact hBound.trans (div_le_div_of_nonneg_left bernoulli_scalar_small_ball_constant_pos.le
    (Real.sqrt_pos.mpr (mul_pos (mul_pos hδ hnR) hpPos)) hRoot)

theorem row_bernoulli_nonalmost_scalar_small_ball {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) (hHalf : (rowBernoulliParameter n d : ℝ) ≤ 1 / 2)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) (z : ℂ) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one hn hdn)).real {y |
        ‖(∑ i, weightedBernoulliValue (x i) (y i)) - z‖ ≤ ρ / Real.sqrt n} ≤
          bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : (rowBernoulliParameter n d : ℝ) = (d : ℝ) / n := by
    simp only [rowBernoulliParameter, NNReal.coe_div, NNReal.coe_natCast]
  have hpPos : 0 < (rowBernoulliParameter n d : ℝ) := by rw [hp]; exact div_pos hdR hnR
  have h := bernoulli_nonalmost_scalar_small_ball hn (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one hn hdn) hpPos hHalf hδ hρ x hx z
  have hScale : δ * n * (rowBernoulliParameter n d : ℝ) = δ * d := by
    rw [hp]
    field_simp [hnR.ne']
  simpa only [hScale] using h

theorem row_bernoulli_nonalmost_small_ball_half_degree {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hDegree : 2 * d ≤ n)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) (z : ℂ) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one hn (by omega))).real {y |
        ‖(∑ i, weightedBernoulliValue (x i) (y i)) - z‖ ≤ ρ / Real.sqrt n} ≤
          bernoulliScalarSmallBallConstant / Real.sqrt (δ * d) := by
  apply row_bernoulli_nonalmost_scalar_small_ball hn hd (by omega) ?_ hδ hρ x hx z
  rw [rowBernoulliParameter_coe]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
  have hDegreeR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hDegree
  linarith

end CircularLaw
