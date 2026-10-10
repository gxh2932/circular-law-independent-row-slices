import CircularLaw.WeightedBernoulliSmallBall
import CircularLaw.MeasureModel

/-!
# Fair Boolean choices and their scalar small-ball bound

The actual Bernoulli law with parameter one half equals uniform counting
on Boolean tuples. This transports the proved weighted Bernoulli bound
to the fair choices used in the paired slice representation.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_half_coordinate_law :
    bernoulliCoordinateLaw (1 / 2) (by norm_num) = finiteUniformMeasure Bool := by
  apply Measure.ext_of_singleton
  intro b
  rw [bernoulliCoordinateLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    finiteUniformMeasure_singleton]
  cases b <;> norm_num [PMF.bernoulli_apply]

theorem bernoulli_half_cube_law {ι : Type*} [Fintype ι] [DecidableEq ι] :
    bernoulliCubeLaw ι (1 / 2) (by norm_num) = finiteUniformMeasure (ι → Bool) := by
  simp only [bernoulliCubeLaw, bernoulli_half_coordinate_law]
  exact finiteUniformMeasure_pi.symm

theorem fair_boolean_linear_form_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ρ r : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ i ∈ S, ρ ≤ ‖a i‖) (hr : ρ / 2 ≤ r) (z : ℂ) :
    uniformProbability (fun x : ι → Bool =>
      ‖(∑ i, weightedBernoulliValue (a i) (x i)) - z‖ ≤ r) ≤
        bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((S.card : ℝ) / 2) := by
  have h := bernoulli_cube_linear_form_small_ball (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) a S hS hρ hLarge hr z
  rw [bernoulli_half_cube_law, finiteUniformMeasure_real] at h
  have hHalf : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hHalf] at h
  simpa only [div_eq_mul_inv, one_mul] using h

end CircularLaw
