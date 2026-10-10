import CircularLaw.BernoulliCubeLaw
import CircularLaw.EsseenConcentration

/-!
# Exact symmetrized moments of weighted Bernoulli variables

These are the actual two-atom complex laws. The truncated second moment
of their independent difference is exactly 2*p*(1-p)*rho^2 whenever the
nonzero atom has norm at least rho. This supplies the scalar Bernoulli
anti-concentration input for the projection argument.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators Convolution NNReal

namespace CircularLaw

def weightedBernoulliValue (a : ℂ) (b : Bool) : ℂ := cond b a 0

def weightedBernoulliLaw (p : ℝ≥0) (hp : p ≤ 1) (a : ℂ) : Measure ℂ :=
  (bernoulliCoordinateLaw p hp).map (weightedBernoulliValue a)

instance weightedBernoulliLaw_probability (p : ℝ≥0) (hp : p ≤ 1) (a : ℂ) :
    IsProbabilityMeasure (weightedBernoulliLaw p hp a) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem weighted_bernoulli_law_integral (p : ℝ≥0) (hp : p ≤ 1) (a : ℂ)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂weightedBernoulliLaw p hp a) = (1 - (p : ℝ)) * f 0 + p * f a := by
  rw [weightedBernoulliLaw, integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable,
    bernoulliCoordinateLaw_integral]
  rfl

theorem weighted_bernoulli_symmetrized_truncated_moment (p : ℝ≥0) (hp : p ≤ 1)
    (a : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (ha : ρ ≤ ‖a‖) :
    truncatedSymmetrizedMoment (weightedBernoulliLaw p hp a) ρ = 2 * p * (1 - (p : ℝ)) * ρ ^ 2 := by
  let μ := weightedBernoulliLaw p hp a
  have hInner (x : ℂ) : (∫ y, truncatedNormSq ρ (x + y) ∂μ.map (fun y => -y)) =
      (1 - (p : ℝ)) * truncatedNormSq ρ x + p * truncatedNormSq ρ (x - a) := by
    rw [integral_map measurable_neg.aemeasurable (by unfold truncatedNormSq; fun_prop)]
    rw [weighted_bernoulli_law_integral p hp a _ (by unfold truncatedNormSq; fun_prop)]
    simp only [neg_zero, add_zero, ← sub_eq_add_neg]
  rw [truncatedSymmetrizedMoment, symmetrizedLaw,
    integral_conv (truncatedNormSq_integrable _ hρ)]
  change (∫ x, (∫ y, truncatedNormSq ρ (x + y) ∂μ.map (fun y => -y)) ∂μ) = _
  simp only [hInner]
  rw [weighted_bernoulli_law_integral p hp a _ (by unfold truncatedNormSq; fun_prop)]
  simp only [truncatedNormSq, norm_zero, min_eq_left hρ, zero_pow (by decide : 2 ≠ 0),
    zero_sub, norm_neg, min_eq_right ha, sub_self, mul_zero, zero_add, add_zero]
  ring

theorem weighted_bernoulli_sum_law {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (a : ι → ℂ) :
    productSumLaw (fun i => weightedBernoulliLaw p hp (a i)) =
      (bernoulliCubeLaw ι p hp).map (fun x => ∑ i, weightedBernoulliValue (a i) (x i)) := by
  let X := fun i : ι => fun x : ι → Bool => weightedBernoulliValue (a i) (x i)
  have hX : ∀ i, Measurable (X i) := fun _ => measurable_of_countable _
  have hInd : iIndepFun X (bernoulliCubeLaw ι p hp) :=
    iIndepFun_pi (fun i => (measurable_of_countable (weightedBernoulliValue (a i))).aemeasurable)
  have hMarg (i : ι) : (bernoulliCubeLaw ι p hp).map (X i) = weightedBernoulliLaw p hp (a i) := by
    calc
      _ = ((Measure.pi (fun _ : ι => bernoulliCoordinateLaw p hp)).map
          (fun x : ι → Bool => x i)).map (weightedBernoulliValue (a i)) :=
        (Measure.map_map (μ := Measure.pi (fun _ : ι => bernoulliCoordinateLaw p hp))
          (measurable_of_countable (weightedBernoulliValue (a i))) (measurable_pi_apply i)).symm
      _ = _ := by
        rw [(measurePreserving_eval (fun _ : ι => bernoulliCoordinateLaw p hp) i).map_eq]
        rfl
  simpa only [hMarg] using productSumLaw_eq_independent_sum (bernoulliCubeLaw ι p hp) X hX hInd

end CircularLaw
