import CircularLaw.Moments
import CircularLaw.Tensorization

/-!
# The finite counting model as a probability measure

The main theorem uses finite uniform event probabilities. This file connects
that law to mathlib measures, integrals, product measures and independence,
so probabilistic lemmas apply to the same model.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CircularLaw

def finiteUniformMeasure (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  ENNReal.ofReal (1 / (Fintype.card α : ℝ)) • Measure.count

instance finiteUniformMeasure_finite (α : Type*) [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : IsFiniteMeasure (finiteUniformMeasure α) := by
  constructor
  rw [finiteUniformMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top Measure.count _)

theorem finiteUniformMeasure_apply {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (event : α → Prop) :
    finiteUniformMeasure α {x | event x} = ENNReal.ofReal (uniformProbability event) := by
  classical
  have hcount : Measure.count {x | event x} = (Nat.card {x // event x} : ℝ≥0∞) := by
    rw [Measure.count_apply_finite _ (Set.toFinite _)]
    congr 1
    exact (Set.ncard_eq_toFinset_card {x | event x}).symm
  rw [finiteUniformMeasure, Measure.smul_apply, smul_eq_mul, hcount,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [uniformProbability, Nat.card_eq_fintype_card, div_eq_mul_inv, one_mul]
  ring

theorem finiteUniformMeasure_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (event : α → Prop) :
    (finiteUniformMeasure α).real {x | event x} = uniformProbability event := by
  rw [measureReal_def, finiteUniformMeasure_apply,
    ENNReal.toReal_ofReal (uniformProbability_nonneg event)]

instance finiteUniformMeasure_probability (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    IsProbabilityMeasure (finiteUniformMeasure α) := by
  constructor
  simpa only [Set.setOf_true, uniformProbability_true, ENNReal.ofReal_one] using
    finiteUniformMeasure_apply (fun _ : α => True)

theorem integral_finiteUniformMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ x, f x ∂finiteUniformMeasure α) = finiteMean f := by
  rw [finiteUniformMeasure, integral_smul_measure, integral_count,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [finiteMean, smul_eq_mul, div_eq_mul_inv]
  ring

theorem finiteUniformMeasure_singleton {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (x : α) :
    finiteUniformMeasure α {x} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [finiteUniformMeasure, Measure.smul_apply, Measure.count_singleton, smul_eq_mul,
    mul_one, one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]

/-- Uniform counting on complete tuples is exactly the independent product
of uniform counting on the component spaces. -/
theorem finiteUniformMeasure_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] :
    finiteUniformMeasure (∀ i, α i) = Measure.pi (fun i => finiteUniformMeasure (α i)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [finiteUniformMeasure_singleton, Measure.pi_singleton]
  simp only [finiteUniformMeasure_singleton, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))

instance rowSliceMeasurableSpace (n d : ℕ) : MeasurableSpace (RowSlice n d) := ⊤

instance rowSliceMeasurableSingletonClass (n d : ℕ) :
    MeasurableSingletonClass (RowSlice n d) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def rowSliceLaw (n d : ℕ) : Measure (RowSlice n d) := finiteUniformMeasure (RowSlice n d)

def rowSliceMatrixLaw (n d : ℕ) : Measure (RowSliceMatrix n d) :=
  finiteUniformMeasure (RowSliceMatrix n d)

theorem rowSliceLaw_probability {n d : ℕ} (hdn : d ≤ n) :
    IsProbabilityMeasure (rowSliceLaw n d) := by
  haveI := rowSlice_nonempty hdn
  unfold rowSliceLaw
  infer_instance

theorem rowSliceMatrixLaw_probability {n d : ℕ} (hdn : d ≤ n) :
    IsProbabilityMeasure (rowSliceMatrixLaw n d) := by
  haveI := rowSlice_nonempty hdn
  unfold rowSliceMatrixLaw
  infer_instance

theorem rowSliceLaw_apply (n d : ℕ) (event : RowSlice n d → Prop) :
    rowSliceLaw n d {x | event x} = ENNReal.ofReal (uniformProbability event) :=
  finiteUniformMeasure_apply event

theorem rowSliceMatrixLaw_apply (n d : ℕ) (event : RowSliceMatrix n d → Prop) :
    rowSliceMatrixLaw n d {x | event x} = ENNReal.ofReal (uniformProbability event) :=
  finiteUniformMeasure_apply event

theorem rowSliceMatrixLaw_eq_pi {n d : ℕ} (hdn : d ≤ n) :
    rowSliceMatrixLaw n d = Measure.pi (fun _ : Fin n => rowSliceLaw n d) := by
  haveI := rowSlice_nonempty hdn
  exact finiteUniformMeasure_pi

theorem independent_rowSliceLaw {n d : ℕ} (hdn : d ≤ n) :
    iIndepFun (fun i : Fin n => fun s : RowSliceMatrix n d => s i)
      (rowSliceMatrixLaw n d) := by
  haveI := rowSliceLaw_probability hdn
  rw [rowSliceMatrixLaw_eq_pi hdn]
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem rowSliceLaw_marginal {n d : ℕ} (hdn : d ≤ n) (i : Fin n) :
    (rowSliceMatrixLaw n d).map (fun s => s i) = rowSliceLaw n d := by
  haveI := rowSliceLaw_probability hdn
  rw [rowSliceMatrixLaw_eq_pi hdn]
  exact (measurePreserving_eval (fun _ : Fin n => rowSliceLaw n d) i).map_eq

theorem independent_row_observables {n d : ℕ} (hdn : d ≤ n)
    (f : Fin n → RowSlice n d → ℂ) :
    iIndepFun (fun i => fun s : RowSliceMatrix n d => f i (s i))
      (rowSliceMatrixLaw n d) := by
  haveI := rowSliceLaw_probability hdn
  rw [rowSliceMatrixLaw_eq_pi hdn]
  exact iIndepFun_pi (fun i => (measurable_of_countable (f i)).aemeasurable)

theorem row_observable_concentration {n d : ℕ} (hdn : d ≤ n)
    (i : Fin n) (f : RowSlice n d → ℂ) (r : ℝ) :
    levyConcentration (rowSliceMatrixLaw n d) (fun s => f (s i)) r =
      levyConcentration (rowSliceLaw n d) f r := by
  unfold levyConcentration
  congr 1
  funext z
  have h := congrArg (fun ν : Measure (RowSlice n d) => ν {s | ‖f s - z‖ ≤ r})
    (rowSliceLaw_marginal hdn i)
  dsimp only at h
  rwa [Measure.map_apply (measurable_pi_apply i)
    ((Set.toFinite {s | ‖f s - z‖ ≤ r}).measurableSet)] at h

/-- Tensorization for exactly the complete-support counting law used in the
main target, with a possibly different observable on each independent row. -/
theorem rowSlice_uniform_tensorization {n d : ℕ} (hdn : d ≤ n)
    (f : Fin n → RowSlice n d → ℂ) {t A τ : ℝ}
    (ht : 0 ≤ t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ i (σ : ℝ), 1 ≤ σ → levyConcentration (rowSliceLaw n d)
      (f i) (σ * t) ≤ ENNReal.ofReal (A * σ ^ 2)) (z : Fin n → ℂ) :
    uniformProbability (fun s : RowSliceMatrix n d =>
      (∑ i, ‖f i (s i) - z i‖ ^ 2) ≤ τ ^ 2 * t ^ 2 * n) ≤
      (4 * Real.exp 1 * A * τ ^ 2) ^ n := by
  haveI := rowSliceMatrixLaw_probability hdn
  rw [← finiteUniformMeasure_real]
  apply tensorization (rowSliceMatrixLaw n d) (fun i s => f i (s i))
    (fun i => measurable_of_countable _) (independent_row_observables hdn f) ht hA hτ
  intro i σ hσ
  rw [row_observable_concentration hdn]
  exact hsmall i σ hσ

theorem rowSliceLaw_mean {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    (∫ s, rowEntryReal s j ∂rowSliceLaw n d) = (d : ℝ) / n := by
  rw [rowSliceLaw, integral_finiteUniformMeasure]
  exact row_entry_mean hd hdn j

theorem rowSliceLaw_variance {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    (∫ s, (rowEntryReal s j - (d : ℝ) / n) ^ 2 ∂rowSliceLaw n d) =
      ((d : ℝ) / n) * (1 - (d : ℝ) / n) := by
  rw [rowSliceLaw, integral_finiteUniformMeasure]
  exact row_entry_variance hd hdn j

end CircularLaw
