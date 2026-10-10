import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Averaging an independent fresh block after a finite exposure

For a finite product experiment, conditioning a function of the exposed
past and an independent fresh block fixes the past and averages only the
fresh block. In particular, a pointwise fresh-block probability bound on
a past-measurable good event gives the conditional probability needed by
the exposure drift argument.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem finite_independent_fresh_conditional_expectation
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hIndep : IndepFun X Y μ) (f : α → β → ℝ) :
    μ[(fun ω => f (X ω) (Y ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => ∫ y, f (X ω) y ∂μ.map Y := by
  let s : α → Set Ω := fun a => X ⁻¹' {a}
  let g : α → Ω → ℝ := fun a ω => f a (Y ω)
  have hFresh : ∀ a, μ[g a | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] fun _ => ∫ y, f a y ∂μ.map Y := by
    intro a
    have hStrong : StronglyMeasurable[(MeasurableSpace.comap Y inferInstance)] (g a) :=
      (measurable_of_countable (f a)).stronglyMeasurable.comp_measurable
        (comap_measurable Y)
    have h := condExp_indep_eq hY.comap_le hX.comap_le hStrong
      ((IndepFun_iff_Indep Y X μ).mp hIndep.symm)
    have hIntegral := integral_map (μ := μ) hY.aemeasurable
      (measurable_of_countable (f a)).aestronglyMeasurable
    exact h.trans (ae_of_all μ (fun _ => hIntegral.symm))
  have hEach : ∀ a,
      μ[(s a).indicator (g a) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
        (s a).indicator (fun _ => ∫ y, f a y ∂μ.map Y) := by
    intro a
    have hSet : MeasurableSet[(MeasurableSpace.comap X inferInstance)] (s a) :=
      (measurableSet_singleton a).preimage (comap_measurable X)
    apply (condExp_indicator Integrable.of_finite hSet).trans
    filter_upwards [hFresh a] with ω hω
    by_cases hMem : ω ∈ s a <;> simp [hMem, hω]
  have hPartition : (fun ω => f (X ω) (Y ω)) = ∑ a, (s a).indicator (g a) := by
    ext ω
    simp [s, g, Set.indicator]
  calc
    μ[(fun ω => f (X ω) (Y ω)) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
        μ[∑ a, (s a).indicator (g a) | (MeasurableSpace.comap X inferInstance)] := by rw [hPartition]
    _ =ᵐ[μ] ∑ a, μ[(s a).indicator (g a) | (MeasurableSpace.comap X inferInstance)] :=
      condExp_finset_sum (fun _ _ => Integrable.of_finite) (MeasurableSpace.comap X inferInstance)
    _ =ᵐ[μ] fun ω => ∫ y, f (X ω) y ∂μ.map Y := by
      filter_upwards [ae_all_iff.mpr hEach] with ω hω
      simp only [Finset.sum_apply]
      simp_rw [hω]
      simp [s, Set.indicator]

theorem finite_independent_fresh_conditional_probability
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hIndep : IndepFun X Y μ) (B : α → β → Prop) :
    μ[({ω | B (X ω) (Y ω)}).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ]
        fun ω => (μ.map Y).real {y | B (X ω) y} := by
  have h := finite_independent_fresh_conditional_expectation μ X Y hX hY hIndep
    (fun a => ({y | B a y}).indicator (fun _ => (1 : ℝ)))
  have hIndicator : (fun ω => ({y | B (X ω) y}).indicator (fun _ => (1 : ℝ)) (Y ω)) =
      ({ω | B (X ω) (Y ω)}).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp [Set.indicator]
  rw [hIndicator] at h
  apply h.trans
  apply ae_of_all
  intro ω
  exact integral_indicator_one ((Set.to_countable _).measurableSet)

theorem finite_independent_fresh_conditional_probability_le_on_past
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hIndep : IndepFun X Y μ) (B : α → β → Prop) (G : α → Prop) {q : ℝ}
    (hBound : ∀ a, G a → (μ.map Y).real {y | B a y} ≤ q) :
    ∀ᵐ ω ∂μ, G (X ω) →
      (μ[({ω | B (X ω) (Y ω)}).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance]) ω ≤ q := by
  filter_upwards [finite_independent_fresh_conditional_probability μ X Y hX hY hIndep B]
    with ω hω hGood
  exact hω.le.trans (hBound (X ω) hGood)

end CircularLaw
