import CircularLaw.FiniteProductEventUpperTail
import CircularLaw.IndependentLowerTail

/-!
# Lower tails for events under arbitrary finite product laws

The event probabilities are those of the actual coordinate measures.
The four-fifths estimate uses the same witness rate as the slice proof.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_product_event_lower_laplace_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, α i → Prop) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    (Measure.pi μ).real {x | (coordinateEventCount E x : ℝ) < u} ≤
      Real.exp ((Real.exp (-t) - 1) * (∑ i, (μ i).real {a | E i a}) + t * u) := by
  have hMark := finite_measure_event_markov (Measure.pi μ)
    (fun x => (coordinateEventCount E x : ℝ) < u)
    (fun x => Real.exp (-t * coordinateEventCount E x)) (Real.exp_pos (-t * u))
    (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hx.le (neg_nonpos.mpr ht)))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (finite_product_event_laplace_bound μ E (-t))
    (Real.exp_pos (-t * u)).le).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

theorem finite_product_event_lower_tail_four_fifths {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, α i → Prop) (T : ℝ)
    (hMean : (4 / 5 : ℝ) * T ≤ ∑ i, (μ i).real {a | E i a}) :
    (Measure.pi μ).real {x | (coordinateEventCount E x : ℝ) < T / 2} ≤
      Real.exp (-uniqueWitnessRate * T) := by
  have h := finite_product_event_lower_laplace_tail μ E
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)).le (T / 2)
  have hExp : Real.exp (-Real.log (4 / 3)) = (3 / 4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  rw [hExp] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold uniqueWitnessRate
  linarith

end CircularLaw
