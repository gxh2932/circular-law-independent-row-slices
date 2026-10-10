import CircularLaw.IndependentUpperTail
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Upper tails for events under finite product probability laws

The factors may have arbitrary finite probability laws. This supplies
the row-event count estimate for the actual Bernoulli row law.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_measure_event_markov {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Ω → Prop) (f : Ω → ℝ)
    {a : ℝ} (ha : 0 < a) (hNonneg : ∀ ω, 0 ≤ f ω)
    (hLarge : ∀ ω, E ω → a ≤ f ω) :
    μ.real {ω | E ω} ≤ (∫ ω, f ω ∂μ) / a := by
  have hSubset : {ω | E ω} ⊆ {ω | a ≤ f ω} := hLarge
  have hMark := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hNonneg)
    (Integrable.of_finite : Integrable f μ) a
  have hBound := (mul_le_mul_of_nonneg_left
    (measureReal_mono hSubset (h₂ := by finiteness)) ha.le).trans hMark
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hBound)

theorem finite_probability_indicator_mean {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω → Prop) :
    (∫ ω, (if E ω then (1 : ℝ) else 0) ∂μ) = μ.real {ω | E ω} := by
  have hIndicator : (fun ω => if E ω then (1 : ℝ) else 0) =
      ({ω | E ω}).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [hIndicator]
  exact integral_indicator_one ((Set.to_countable _).measurableSet)

theorem finite_product_event_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, α i → Prop) (t : ℝ) :
    (∫ x, Real.exp (t * coordinateEventCount E x) ∂Measure.pi μ) =
      ∏ i, (1 + (μ i).real {a | E i a} * (Real.exp t - 1)) := by
  have hProduct (x : ∀ i, α i) :
      Real.exp (t * coordinateEventCount E x) =
        ∏ i, (1 + (if E i (x i) then (1 : ℝ) else 0) * (Real.exp t - 1)) := by
    rw [coordinateEventCount_cast, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : E i (x i) <;> simp [hi]
  simp_rw [hProduct]
  rw [integral_fintype_prod_eq_prod
    (fun i (a : α i) => 1 + (if E i a then (1 : ℝ) else 0) * (Real.exp t - 1))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const, probReal_univ, one_smul, integral_mul_const,
    finite_probability_indicator_mean]

theorem finite_product_event_laplace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, α i → Prop) (t : ℝ) :
    (∫ x, Real.exp (t * coordinateEventCount E x) ∂Measure.pi μ) ≤
      Real.exp ((Real.exp t - 1) * ∑ i, (μ i).real {a | E i a}) := by
  rw [finite_product_event_laplace]
  calc
    _ ≤ ∏ i, Real.exp ((μ i).real {a | E i a} * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hp : (μ i).real {a | E i a} ≤ 1 := measureReal_le_one
        have hProbNonneg : 0 ≤ (μ i).real {a | E i a} := measureReal_nonneg
        have hNonneg := mul_nonneg hProbNonneg (Real.exp_pos t).le
        nlinarith
      · intro i _
        linarith [Real.add_one_le_exp ((μ i).real {a | E i a} * (Real.exp t - 1))]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem finite_product_many_events_sixteenth {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, α i → Prop) (hSmall : ∀ i, (μ i).real {a | E i a} ≤ 1 / 16) :
    (Measure.pi μ).real {x | (Fintype.card ι : ℝ) / 8 < coordinateEventCount E x} ≤
      Real.exp (-rowLoadRate * Fintype.card ι) := by
  let t := Real.log 2
  let u := (Fintype.card ι : ℝ) / 8
  have ht : 0 ≤ t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hMark := finite_measure_event_markov (Measure.pi μ)
    (fun x => u < (coordinateEventCount E x : ℝ))
    (fun x => Real.exp (t * coordinateEventCount E x)) (Real.exp_pos (t * u))
    (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le ht))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (finite_product_event_laplace_bound μ E t)
    (Real.exp_pos (t * u)).le).trans
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hSum : (∑ i, (μ i).real {a | E i a}) ≤ (Fintype.card ι : ℝ) / 16 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hSmall i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv,
      mul_one, one_mul] using h
  dsimp only [t, u]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  unfold rowLoadRate
  linarith

end CircularLaw
