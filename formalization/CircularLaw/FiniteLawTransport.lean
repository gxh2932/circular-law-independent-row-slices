import CircularLaw.RegularizedDistanceConcentration

/-!
# Finite laws on arbitrary probability spaces

Exact marginal law identities transport integrals, integrability and
event probabilities. The source space need not be finite.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

theorem finite_law_integral_comp {μ : Measure Ω} {ν : Measure α} [IsFiniteMeasure ν]
    {X : Ω → α} (hX : Measurable X) (hLaw : μ.map X = ν) (f : α → ℝ) :
    (∫ ω, f (X ω) ∂μ) = ∫ x, f x ∂ν := by
  rw [← hLaw]
  exact (integral_map hX.aemeasurable (measurable_of_countable f).aestronglyMeasurable).symm

theorem finite_law_integrable_comp {μ : Measure Ω} {ν : Measure α} [IsFiniteMeasure ν]
    {X : Ω → α} (hX : Measurable X) (hLaw : μ.map X = ν) (f : α → ℝ) :
    Integrable (fun ω => f (X ω)) μ :=
  (show MeasurePreserving X μ ν from ⟨hX, hLaw⟩).integrable_comp_of_integrable Integrable.of_finite

theorem finite_law_event_real {μ : Measure Ω} {ν : Measure α} [IsFiniteMeasure ν]
    {X : Ω → α} (hX : Measurable X) (hLaw : μ.map X = ν) (event : α → Prop) :
    μ.real {ω | event (X ω)} = ν.real {x | event x} := by
  rw [← hLaw, map_measureReal_apply hX (Set.toFinite _).measurableSet]
  rfl

end CircularLaw
