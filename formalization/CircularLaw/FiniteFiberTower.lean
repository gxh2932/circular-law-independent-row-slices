import CircularLaw.FiniteFiberMean

/-!
# Pointwise tower identities on finite uniform fibres

Every point of a nonempty finite uniform space has positive mass.
Consequently the checked conditional-expectation tower yields literal
pointwise identities for the fibre means used by injection exposure.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem finite_uniform_ae_iff {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P : Ω → Prop) :
    (∀ᵐ x ∂finiteUniformMeasure Ω, P x) ↔ ∀ x, P x := by
  have hScalar : ENNReal.ofReal (1 / (Fintype.card Ω : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [finiteUniformMeasure, Measure.ae_ennreal_smul_measure_iff hScalar, Measure.ae_count_iff]

theorem finiteFiberMean_sub {Ω α : Type*} [Fintype Ω] (s : Ω → α)
    (f g : Ω → ℝ) (a : α) :
    finiteFiberMean s (fun x => f x - g x) a =
      finiteFiberMean s f a - finiteFiberMean s g a := finiteMean_sub _ _

theorem finiteFiberMean_constant_on_reference {Ω α : Type*} [Fintype Ω]
    (s : Ω → α) (f : Ω → ℝ) (x : Ω)
    (hConst : ∀ y, s y = s x → f y = f x) : finiteFiberMean s f (s x) = f x := by
  haveI := finiteFiberMean_reference_nonempty s x
  have h : (fun y : {y // s y = s x} => f y.val) = (fun _ => f x) := by
    funext y
    exact hConst y.val y.property
  unfold finiteFiberMean
  rw [h, finiteMean_const]

theorem finiteFiberMean_tower {Ω α β : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Fintype β] [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (s : Ω → α) (g : α → β) (f : Ω → ℝ) (x : Ω) :
    finiteFiberMean (fun y => g (s y)) (fun y => finiteFiberMean s f (s y)) (g (s x)) =
      finiteFiberMean (fun y => g (s y)) f (g (s x)) := by
  have hFine : MeasurableSpace.comap s inferInstance ≤ mΩ :=
    (measurable_of_countable s).comap_le
  have hLe : MeasurableSpace.comap (fun y => g (s y)) inferInstance ≤
      MeasurableSpace.comap s inferInstance := by
    intro E hE
    obtain ⟨T, hT, hEq⟩ := MeasurableSpace.measurableSet_comap.mp hE
    exact MeasurableSpace.measurableSet_comap.mpr
      ⟨g ⁻¹' T, (measurable_of_countable g) hT, hEq⟩
  have hFineMean := finite_uniform_statistic_conditional_mean s f
  have hCoarseMean := finite_uniform_statistic_conditional_mean (fun y => g (s y)) f
  have hCoarseFine := finite_uniform_statistic_conditional_mean (fun y => g (s y))
    (fun y => finiteFiberMean s f (s y))
  have hCongr := condExp_congr_ae (m := MeasurableSpace.comap (fun y => g (s y)) inferInstance)
    hFineMean
  have hTower := condExp_condExp_of_le (μ := finiteUniformMeasure Ω) (f := f) hLe hFine
  have hAll := hCoarseFine.symm.trans (hCongr.symm.trans (hTower.trans hCoarseMean))
  exact (finite_uniform_ae_iff _).mp hAll x

end CircularLaw
