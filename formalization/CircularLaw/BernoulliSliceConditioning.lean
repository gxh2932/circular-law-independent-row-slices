import CircularLaw.BernoulliSliceFibers
import Mathlib.Probability.ConditionalProbability

/-!
# The Bernoulli cube conditioned on its support size is the row-slice law

The exact finite probability identity holds for every cube event and
the actual row embedding. The uniform conditional law and the transfer
factor follow by dividing by the nonzero support-size probability.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

theorem finiteMeasure_event_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (event : α → Prop) :
    μ.real {x | event x} = ∑ x, if event x then μ.real {x} else 0 := by
  have hSet : ((Finset.univ.filter event : Finset α) : Set α) = {x | event x} := by
    ext x
    simp
  rw [← hSet, ← sum_measureReal_singleton, Finset.sum_filter]

def bernoulliSliceAtomWeight (n d : ℕ) (p : ℝ≥0) : ℝ :=
  (p : ℝ) ^ d * (1 - (p : ℝ)) ^ (n - d)

def bernoulliSliceMass (n d : ℕ) (p : ℝ≥0) : ℝ :=
  (n.choose d : ℝ) * bernoulliSliceAtomWeight n d p

theorem bernoulliCubeLaw_fiber_event (n d : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (event : (Fin n → Bool) → Prop) :
    (bernoulliCubeLaw (Fin n) p hp).real {x | bernoulliSupportSize x = d ∧ event x} =
      bernoulliSliceAtomWeight n d p * ∑ s : RowSlice n d, if event (rowSliceBoolRow s) then 1 else 0 := by
  rw [finiteMeasure_event_real]
  calc
    _ = ∑ x : Fin n → Bool, if bernoulliSupportSize x = d then
        bernoulliSliceAtomWeight n d p * (if event x then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hSize : bernoulliSupportSize x = d
      · by_cases hEvent : event x <;>
          simp [hSize, hEvent, bernoulliCubeLaw_singleton_real, bernoulliSliceAtomWeight]
      · simp [hSize]
    _ = _ := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype (p := fun x : Fin n → Bool => bernoulliSupportSize x = d)
        (Finset.univ.filter (fun x : Fin n → Bool => bernoulliSupportSize x = d))
        (fun x => by simp) (fun x => bernoulliSliceAtomWeight n d p * (if event x then 1 else 0))]
      rw [← (bernoulliSliceFiberEquiv n d).sum_comp]
      rw [Finset.mul_sum]
      rfl

theorem bernoulliCubeLaw_fiber_mass (n d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliCubeLaw (Fin n) p hp).real {x | bernoulliSupportSize x = d} = bernoulliSliceMass n d p := by
  have h := bernoulliCubeLaw_fiber_event n d p hp (fun _ => True)
  simpa only [and_true, if_true, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_rowSlice, mul_one, bernoulliSliceMass, mul_comm] using h

theorem bernoulliCubeLaw_fiber_event_probability {n d : ℕ} (hdn : d ≤ n)
    (p : ℝ≥0) (hp : p ≤ 1) (event : (Fin n → Bool) → Prop) :
    (bernoulliCubeLaw (Fin n) p hp).real {x | bernoulliSupportSize x = d ∧ event x} =
      bernoulliSliceMass n d p * uniformProbability (fun s : RowSlice n d => event (rowSliceBoolRow s)) := by
  have hCount : (Fintype.card {s : RowSlice n d // event (rowSliceBoolRow s)} : ℝ) =
      ∑ s : RowSlice n d, if event (rowSliceBoolRow s) then (1 : ℝ) else 0 := by
    rw [Fintype.card_subtype, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hCard : (n.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdn).ne'
  rw [bernoulliCubeLaw_fiber_event, uniformProbability, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, card_rowSlice, hCount, bernoulliSliceMass]
  field_simp

theorem bernoulliSlice_conditional_event {n d : ℕ} (hdn : d ≤ n)
    (p : ℝ≥0) (hp : p ≤ 1) (hMass : 0 < bernoulliSliceMass n d p)
    (event : (Fin n → Bool) → Prop) :
    ((bernoulliCubeLaw (Fin n) p hp)[|{x | bernoulliSupportSize x = d}]).real {x | event x} =
      uniformProbability (fun s : RowSlice n d => event (rowSliceBoolRow s)) := by
  rw [measureReal_def, cond_apply (Set.toFinite _).measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((bernoulliCubeLaw (Fin n) p hp).real {x | bernoulliSupportSize x = d})⁻¹ *
    (bernoulliCubeLaw (Fin n) p hp).real {x | bernoulliSupportSize x = d ∧ event x} = _
  rw [bernoulliCubeLaw_fiber_mass, bernoulliCubeLaw_fiber_event_probability hdn]
  field_simp

theorem bernoulliSlice_event_transfer {n d : ℕ} (hdn : d ≤ n)
    (p : ℝ≥0) (hp : p ≤ 1) (hMass : 0 < bernoulliSliceMass n d p)
    (event : (Fin n → Bool) → Prop) :
    uniformProbability (fun s : RowSlice n d => event (rowSliceBoolRow s)) ≤
      (bernoulliCubeLaw (Fin n) p hp).real {x | event x} / bernoulliSliceMass n d p := by
  apply (le_div_iff₀ hMass).mpr
  rw [mul_comm, ← bernoulliCubeLaw_fiber_event_probability hdn]
  exact measureReal_mono (by intro x hx; exact hx.2)

theorem bernoulliSlice_conditional_law {n d : ℕ} (hdn : d ≤ n)
    (p : ℝ≥0) (hp : p ≤ 1) (hMass : 0 < bernoulliSliceMass n d p) :
    (bernoulliCubeLaw (Fin n) p hp)[|{x | bernoulliSupportSize x = d}] =
      (rowSliceLaw n d).map rowSliceBoolRow := by
  have hFiberNeZero : bernoulliCubeLaw (Fin n) p hp {x | bernoulliSupportSize x = d} ≠ 0 := by
    intro hZero
    have h := bernoulliCubeLaw_fiber_mass n d p hp
    rw [measureReal_def, hZero, ENNReal.toReal_zero] at h
    linarith
  haveI : IsProbabilityMeasure ((bernoulliCubeLaw (Fin n) p hp)[|{x | bernoulliSupportSize x = d}]) :=
    cond_isProbabilityMeasure hFiberNeZero
  haveI := rowSliceLaw_probability hdn
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable rowSliceBoolRow) (measurableSet_singleton x)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((bernoulliCubeLaw (Fin n) p hp)[|{x | bernoulliSupportSize x = d}]).real {y | y = x} =
    (rowSliceLaw n d).real {s | rowSliceBoolRow s = x}
  rw [bernoulliSlice_conditional_event hdn p hp hMass, rowSliceLaw, finiteUniformMeasure_real]

end CircularLaw
