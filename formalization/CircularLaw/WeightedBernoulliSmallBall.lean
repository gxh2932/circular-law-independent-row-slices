import CircularLaw.WeightedBernoulliSymmetrization

/-!
# Scalar anti-concentration for the actual Bernoulli row law

For 0<p<=1/2, k coefficients with modulus at least rho yield a uniform
complex small-ball bound C*(r/rho)/sqrt(k*p), at every radius r>=rho/2.
The estimate applies to the literal product Bernoulli law and arbitrary
complex coefficients and centers. No projection probability is assumed.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliScalarSmallBallConstant : ℝ := 48 * Real.exp 1 / Real.pi

theorem bernoulli_scalar_small_ball_constant_pos : 0 < bernoulliScalarSmallBallConstant := by
  unfold bernoulliScalarSmallBallConstant
  positivity

theorem weighted_bernoulli_truncated_moment_nonneg (p : ℝ≥0) (hp : p ≤ 1)
    (a : ℂ) (ρ : ℝ) : 0 ≤ truncatedSymmetrizedMoment (weightedBernoulliLaw p hp a) ρ :=
  integral_nonneg (fun _ => truncatedNormSq_nonneg _ _)

theorem weighted_bernoulli_sum_truncated_moment_lower {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) (a : ι → ℂ) (S : Finset ι)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hLarge : ∀ i ∈ S, ρ ≤ ‖a i‖) :
    (S.card : ℝ) * p * ρ ^ 2 ≤
      ∑ i, truncatedSymmetrizedMoment (weightedBernoulliLaw p hp (a i)) ρ := by
  have hFactor : (p : ℝ) ≤ 2 * p * (1 - (p : ℝ)) := by
    nlinarith [p.coe_nonneg]
  calc
    _ = ∑ _i ∈ S, (p : ℝ) * ρ ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ S, truncatedSymmetrizedMoment (weightedBernoulliLaw p hp (a i)) ρ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [weighted_bernoulli_symmetrized_truncated_moment p hp (a i) hρ (hLarge i hi)]
      exact mul_le_mul_of_nonneg_right hFactor (sq_nonneg ρ)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => weighted_bernoulli_truncated_moment_nonneg p hp (a i) ρ)

theorem weighted_bernoulli_product_sum_small_ball {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ρ r : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ i ∈ S, ρ ≤ ‖a i‖) (hr : ρ / 2 ≤ r) (z : ℂ) :
    (productSumLaw (fun i => weightedBernoulliLaw p hp (a i))).real (Metric.closedBall z r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((S.card : ℝ) * p) := by
  have hK : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hKP : 0 < (S.card : ℝ) * p := mul_pos hK hpPos
  have hRhoHalf : 0 < ρ / 2 := by positivity
  have hrNonneg : 0 ≤ r := hRhoHalf.le.trans hr
  have hLower := weighted_bernoulli_sum_truncated_moment_lower p hp hHalf a S hRhoHalf.le (by
    intro i hi
    exact (by linarith : ρ / 2 ≤ ρ).trans (hLarge i hi))
  let M := ∑ i, truncatedSymmetrizedMoment (weightedBernoulliLaw p hp (a i)) (ρ / 2)
  have hM : 0 < M := (mul_pos hKP (sq_pos_of_pos hRhoHalf)).trans_le hLower
  have hSqrt : (ρ / 2) * Real.sqrt ((S.card : ℝ) * p) ≤ Real.sqrt M := by
    have hRoot := Real.sqrt_le_sqrt hLower
    rw [Real.sqrt_mul hKP.le, Real.sqrt_sq hRhoHalf.le] at hRoot
    simpa only [mul_comm] using hRoot
  have hBall := product_sum_small_ball_le_truncated_moment
    (fun i => weightedBernoulliLaw p hp (a i)) hRhoHalf hr hM z
  have hCompare := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ (24 * Real.exp 1 / Real.pi) * r)
    (mul_pos hRhoHalf (Real.sqrt_pos.mpr hKP)) hSqrt
  calc
    _ ≤ (24 * Real.exp 1 / Real.pi) * r / ((ρ / 2) * Real.sqrt ((S.card : ℝ) * p)) :=
      hBall.trans hCompare
    _ = _ := by
      unfold bernoulliScalarSmallBallConstant
      field_simp
      ring

theorem bernoulli_cube_linear_form_small_ball {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ρ r : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ i ∈ S, ρ ≤ ‖a i‖) (hr : ρ / 2 ≤ r) (z : ℂ) :
    (bernoulliCubeLaw ι p hp).real {x | ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ r} ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((S.card : ℝ) * p) := by
  have hBound := weighted_bernoulli_product_sum_small_ball p hp hpPos hHalf a S hS hρ hLarge hr z
  rw [weighted_bernoulli_sum_law,
    map_measureReal_apply (measurable_of_countable _) measurableSet_closedBall] at hBound
  exact hBound

end CircularLaw
