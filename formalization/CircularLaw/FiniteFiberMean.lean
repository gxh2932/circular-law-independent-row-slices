import CircularLaw.FiniteConditioning
import CircularLaw.MeasureModel
import Mathlib.Probability.ConditionalExpectation

/-!
# Exact finite conditional means

The mean on a statistic fibre retains its literal uniform counting law,
including empty fibres. Weighted averaging gives the defining conditional
expectation identity, used for exposure martingales.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def finiteFiberMean {Ω α : Type*} [Fintype Ω] (s : Ω → α) (f : Ω → ℝ) (a : α) : ℝ :=
  finiteMean (fun x : {x // s x = a} => f x.val)

theorem finiteMean_fiberMean {Ω α : Type*} [Fintype Ω] [Fintype α]
    (s : Ω → α) (f : Ω → ℝ) :
    finiteMean (fun x => finiteFiberMean s f (s x)) = finiteMean f := by
  rw [finiteMean_part_mass s]
  exact (finiteMean_disintegrate s f).symm

theorem finiteMean_fiberMean_weighted {Ω α : Type*} [Fintype Ω] [Fintype α]
    (s : Ω → α) (f : Ω → ℝ) (w : α → ℝ) :
    finiteMean (fun x => w (s x) * finiteFiberMean s f (s x)) =
      finiteMean (fun x => w (s x) * f x) := by
  rw [finiteMean_part_mass s (fun a => w a * finiteFiberMean s f a),
    finiteMean_disintegrate s (fun x => w (s x) * f x)]
  apply Finset.sum_congr rfl
  intro a _
  have h : (fun x : {x // s x = a} => w (s x.val) * f x.val) =
      (fun x => w a * f x.val) := by
    funext x
    rw [x.property]
  rw [h, finiteMean_const_mul]
  rfl

theorem finiteFiberMean_reference_nonempty {Ω α : Type*} [Fintype Ω]
    (s : Ω → α) (x : Ω) : Nonempty {y // s y = s x} := ⟨⟨x, rfl⟩⟩

theorem abs_finiteMean_sub_of_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ) {K : ℝ}
    (h : ∀ x, |f x - g (e x)| ≤ K) : |finiteMean f - finiteMean g| ≤ K := by
  calc
    _ = |finiteMean (fun x => f x - g (e x))| := by
      rw [finiteMean_sub, finiteMean_reindex]
    _ ≤ finiteMean (fun x => |f x - g (e x)|) := abs_finiteMean_le _
    _ ≤ finiteMean (fun _ : α => K) := finiteMean_mono h
    _ = _ := finiteMean_const K

theorem finiteFiberMean_range_bound {Ω α : Type*} [Fintype Ω] (s : Ω → α)
    (f : Ω → ℝ) (x : Ω) {a b : ℝ}
    (hRange : ∀ y, s y = s x → f y ∈ Set.Icc a b) :
    finiteFiberMean s f (s x) ∈ Set.Icc a b := by
  haveI := finiteFiberMean_reference_nonempty s x
  constructor
  · calc
      _ = finiteMean (fun _ : {y // s y = s x} => a) := (finiteMean_const a).symm
      _ ≤ _ := finiteMean_mono (fun y => (hRange y.val y.property).1)
  · calc
      _ ≤ finiteMean (fun _ : {y // s y = s x} => b) :=
        finiteMean_mono (fun y => (hRange y.val y.property).2)
      _ = _ := finiteMean_const b

theorem finite_uniform_statistic_conditional_mean {Ω α : Type*}
    [Fintype Ω] [Fintype α] [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] (s : Ω → α) (f : Ω → ℝ) :
    (finiteUniformMeasure Ω)[f | MeasurableSpace.comap s inferInstance] =ᵐ[finiteUniformMeasure Ω]
      fun x => finiteFiberMean s f (s x) := by
  have hm : MeasurableSpace.comap s inferInstance ≤ mΩ := (measurable_of_countable s).comap_le
  apply (ae_eq_condExp_of_forall_setIntegral_eq (μ := finiteUniformMeasure Ω) (f := f)
    (g := fun x => finiteFiberMean s f (s x)) hm Integrable.of_finite
    (fun _ _ _ => Integrable.of_finite.integrableOn) ?_ ?_).symm
  · intro E hE _
    obtain ⟨T, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hE
    rw [← integral_indicator (hm _ hE), ← integral_indicator (hm _ hE),
      integral_finiteUniformMeasure, integral_finiteUniformMeasure]
    have hLeft : (s ⁻¹' T).indicator (fun x => finiteFiberMean s f (s x)) =
        (fun x => (if s x ∈ T then (1 : ℝ) else 0) * finiteFiberMean s f (s x)) := by
      ext x
      simp [Set.indicator]
    have hRight : (s ⁻¹' T).indicator f =
        (fun x => (if s x ∈ T then (1 : ℝ) else 0) * f x) := by
      ext x
      simp [Set.indicator]
    rw [hLeft, hRight]
    exact finiteMean_fiberMean_weighted s f (fun a => if a ∈ T then 1 else 0)
  · exact ((measurable_of_countable (finiteFiberMean s f)).comp
      (comap_measurable s)).aestronglyMeasurable

end CircularLaw
