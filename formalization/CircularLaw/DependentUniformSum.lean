import CircularLaw.SingletonBlockFiber
import CircularLaw.FiniteConditioning

/-!
# Actual independent sums over different finite sample spaces

The uniform law of a finite Cartesian product is the product of its
component uniform laws. Marginal identification transfers Esseen to
counting probabilities for these actual sums, with the sharper one-half
bound from any individual summand.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem finiteUniformDependentSumLaw_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)]
    (Y : ∀ i, β i → ℂ) :
    productSumLaw (fun i => (finiteUniformMeasure (β i)).map (Y i)) =
      (finiteUniformMeasure (∀ i, β i)).map (fun x => ∑ i, Y i (x i)) := by
  classical
  let μ := finiteUniformMeasure (∀ i, β i)
  let X := fun i (x : ∀ i, β i) => Y i (x i)
  have hX : ∀ i, Measurable (X i) := fun _ => measurable_of_finite _
  have hInd : iIndepFun X μ := by
    dsimp only [μ, X]
    rw [finiteUniformMeasure_pi]
    exact iIndepFun_pi (fun i => (measurable_of_finite (Y i)).aemeasurable)
  have hLaw (i : ι) : μ.map (X i) = (finiteUniformMeasure (β i)).map (Y i) := by
    have h := (measurePreserving_eval (fun i => finiteUniformMeasure (β i)) i).map_eq
    rw [← finiteUniformMeasure_pi] at h
    rw [← h, Measure.map_map (measurable_of_finite (Y i)) (measurable_pi_apply i)]
    rfl
  have h := productSumLaw_eq_independent_sum μ X hX hInd
  simpa only [hLaw, μ, X] using h

theorem uniform_dependent_sum_probability_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)]
    (Y : ∀ i, β i → ℂ) (z : ℂ) (r : ℝ) :
    uniformProbability (fun x : ∀ i, β i => ‖(∑ i, Y i (x i)) - z‖ ≤ r) =
      (productSumLaw (fun i => (finiteUniformMeasure (β i)).map (Y i))).real
        (Metric.closedBall z r) := by
  rw [finiteUniformDependentSumLaw_eq, measureReal_def,
    Measure.map_apply (measurable_of_finite _) measurableSet_closedBall]
  simpa only [Metric.closedBall, dist_eq_norm, Set.preimage_setOf_eq] using
    (finiteUniformMeasure_real (fun x : ∀ i, β i => ‖(∑ i, Y i (x i)) - z‖ ≤ r)).symm

theorem uniform_dependent_sum_half_deficit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)]
    (Y : ∀ i, β i → ℂ) (hm : 1 ≤ Fintype.card ι) {r : ℝ} (hr : 0 < r)
    (hAtom : ∀ i z, uniformProbability (fun x : β i => ‖Y i x - z‖ ≤ r) ≤ 1 / 2) (z : ℂ) :
    uniformProbability (fun x : ∀ i, β i => ‖(∑ i, Y i (x i)) - z‖ ≤ r) ≤
      min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) / Real.sqrt (Fintype.card ι : ℝ)) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  apply le_min
  · exact uniformProbability_pi_sum_small_ball Y (Classical.arbitrary ι) (hAtom _) z
  · haveI : ∀ i, IsProbabilityMeasure ((finiteUniformMeasure (β i)).map (Y i)) :=
      fun i => Measure.isProbabilityMeasure_map (measurable_of_finite (Y i)).aemeasurable
    rw [uniform_dependent_sum_probability_eq]
    have h := half_deficit_product_sum_small_ball
      (fun i => (finiteUniformMeasure (β i)).map (Y i)) hm hr le_rfl
      (fun i => uniform_law_concentration_le (Y i) r (1 / 2) (by norm_num) (hAtom i)) z
    simpa only [div_self hr.ne', mul_one] using h

end CircularLaw
