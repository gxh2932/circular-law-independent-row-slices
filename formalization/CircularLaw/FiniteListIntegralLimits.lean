import CircularLaw.GaussianAllWordMeans

/-!
# Integration and limits of finite lists with multiplicity

Lists retain repeated terms in a noncommuting word expansion. These
lemmas pass integrability, the actual integral and convergence through
such a finite sum without discarding duplicates.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem finite_list_sum_integrable {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List α) (f : α → Ω → ℂ)
    (hf : ∀ a ∈ L, Integrable (f a) μ) :
    Integrable (fun x => (L.map (fun a => f a x)).sum) μ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf a List.mem_cons_self).add (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

theorem finite_list_sum_integral {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List α) (f : α → Ω → ℂ)
    (hf : ∀ a ∈ L, Integrable (f a) μ) :
    (∫ x, (L.map (fun a => f a x)).sum ∂μ) = (L.map (fun a => ∫ x, f a x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL : ∀ b ∈ L, Integrable (f b) μ := fun b hb => hf b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf a List.mem_cons_self) (finite_list_sum_integrable μ L f hL), ih hL]

theorem finite_list_sum_tendsto {α I : Type*} (L : List α) (f : I → α → ℂ)
    (c : α → ℂ) (l : Filter I) (hf : ∀ a ∈ L, Tendsto (fun i => f i a) l (𝓝 (c a))) :
    Tendsto (fun i => (L.map (f i)).sum) l (𝓝 (L.map c).sum) := by
  induction L with
  | nil => simpa only [List.map_nil, List.sum_nil] using
      (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℂ)) l (𝓝 0))
  | cons a L ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf a List.mem_cons_self).add (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

end CircularLaw
