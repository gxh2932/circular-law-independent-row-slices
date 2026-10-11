import CircularLaw.BernoulliFreshConditionalExpectation

/-!
# Fresh-block probability bounds with an exceptional exposed block

A uniform fresh-block bound on the good exposed blocks gives an
unconditional bound after adding the probability of the exceptional blocks.
The Bernoulli version uses the actual coordinate-block law.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CircularLaw

theorem finite_independent_fresh_probability_le_with_bad_event
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hIndep : IndepFun X Y μ) (B : α → β → Prop) (G : α → Prop) {q : ℝ}
    (hq : 0 ≤ q) (hBound : ∀ a, G a → (μ.map Y).real {y | B a y} ≤ q) :
    μ.real {ω | B (X ω) (Y ω)} ≤ q + μ.real {ω | ¬G (X ω)} := by
  haveI : IsProbabilityMeasure (μ.map Y) := μ.isProbabilityMeasure_map hY.aemeasurable
  have hCond := finite_independent_fresh_conditional_probability μ X Y hX hY hIndep B
  have hAverage : μ.real {ω | B (X ω) (Y ω)} =
      ∫ ω, (μ.map Y).real {y | B (X ω) y} ∂μ :=
    (integral_condExp_indicator hX ((Set.to_countable _).measurableSet)).symm.trans
      (integral_congr_ae hCond)
  rw [hAverage]
  calc
    (∫ ω, (μ.map Y).real {y | B (X ω) y} ∂μ) ≤
        ∫ ω, q + ({ω | ¬G (X ω)}).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro ω
      by_cases hGood : G (X ω)
      · simpa [hGood] using hBound (X ω) hGood
      · simp only [Set.indicator_of_mem (show ω ∈ {ω | ¬G (X ω)} from hGood)]
        exact measureReal_le_one.trans (by linarith)
    _ = q + μ.real {ω | ¬G (X ω)} := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const, probReal_univ, one_smul]
      congr 1
      exact integral_indicator_one ((Set.to_countable _).measurableSet)

theorem bernoulli_disjoint_fresh_probability_le_with_bad_event
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (p : ℝ≥0) (hp : p ≤ 1) (e : α ↪ ι) (f : β ↪ ι)
    (hDisjoint : ∀ a b, e a ≠ f b) (B : (α → Bool) → (β → Bool) → Prop)
    (G : (α → Bool) → Prop) {q : ℝ} (hq : 0 ≤ q)
    (hBound : ∀ a, G a → (bernoulliCubeLaw β p hp).real {y | B a y} ≤ q) :
    (bernoulliCubeLaw ι p hp).real
        {x | B (fun a => x (e a)) (fun b => x (f b))} ≤
      q + (bernoulliCubeLaw ι p hp).real {x | ¬G (fun a => x (e a))} := by
  apply finite_independent_fresh_probability_le_with_bad_event
    (bernoulliCubeLaw ι p hp) (fun x a => x (e a)) (fun x b => x (f b))
    (measurable_of_countable _) (measurable_of_countable _)
    (bernoulli_cube_disjoint_blocks_independent p hp e f hDisjoint) B G hq
  simpa only [bernoulli_cube_law_restrict p hp f] using hBound

end CircularLaw
