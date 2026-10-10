import CircularLaw.FiniteListIntegralLimits

/-!
# Actual second moments of finite weighted lists

The expansion retains all ordered term pairs and their multiplicities.
Product integrability justifies both finite integral passages. This is
used for scalar-shifted trace moments without assuming independence
between the different words.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem finite_complex_list_sum_square {α : Type*} (L : List α) (f : α → ℂ) :
    (L.map f).sum ^ 2 = (L.map (fun a => (L.map (fun b => f a * f b)).sum)).sum := by
  rw [pow_two, ← List.sum_map_mul_right L f (L.map f).sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  exact (List.sum_map_mul_left L f (f a)).symm

theorem finite_list_weighted_square_expansion {α : Type*} (L : List α)
    (c f : α → ℂ) :
    (L.map (fun a => c a * f a)).sum ^ 2 =
      (L.map (fun a => (L.map (fun b => (c a * c b) * (f a * f b))).sum)).sum := by
  rw [finite_complex_list_sum_square]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  ring

theorem finite_list_weighted_product_integrable {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : α → ℂ) (f : α → Ω → ℂ) (a b : α)
    (hf : Integrable (fun x => f a x * f b x) μ) :
    Integrable (fun x => (c a * f a x) * (c b * f b x)) μ := by
  have hEq : (fun x => (c a * f a x) * (c b * f b x)) =
      fun x => (c a * c b) * (f a x * f b x) := by funext x; ring
  rw [hEq]
  exact hf.const_mul _

theorem finite_list_weighted_square_integrable {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List α) (c : α → ℂ) (f : α → Ω → ℂ)
    (hf : ∀ a ∈ L, ∀ b ∈ L, Integrable (fun x => f a x * f b x) μ) :
    Integrable (fun x => (L.map (fun a => c a * f a x)).sum ^ 2) μ := by
  simp only [finite_list_weighted_square_expansion]
  apply finite_list_sum_integrable
  intro a ha
  apply finite_list_sum_integrable
  intro b hb
  exact (hf a ha b hb).const_mul _

theorem finite_list_weighted_square_integral {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List α) (c : α → ℂ) (f : α → Ω → ℂ)
    (hf : ∀ a ∈ L, ∀ b ∈ L, Integrable (fun x => f a x * f b x) μ) :
    (∫ x, (L.map (fun a => c a * f a x)).sum ^ 2 ∂μ) =
      (L.map (fun a => (L.map (fun b => (c a * c b) * (∫ x, f a x * f b x ∂μ))).sum)).sum := by
  simp only [finite_list_weighted_square_expansion]
  rw [finite_list_sum_integral]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [finite_list_sum_integral]
    · simp only [integral_const_mul]
    · intro b hb
      exact (hf a ha b hb).const_mul _
  · intro a ha
    exact finite_list_sum_integrable μ L _ (fun b hb => (hf a ha b hb).const_mul _)

end CircularLaw
