import CircularLaw.GaussianWickPairings

/-!
# Gaussian Wick formulas for arbitrary finite position types

Reindexing positions transports matching permutations by actual
conjugation of equivalences. Gaussian samples and entry labels are
unchanged. This allows several trace blocks to share one finite Wick
expansion, with every direct-to-conjugate matching retained.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def matchingPermutationCongr {α β ι : Type*} (e : α ≃ β) (u v : β → ι) :
    {σ : Equiv.Perm α // (u ∘ e) ∘ σ = v ∘ e} ≃
      {τ : Equiv.Perm β // u ∘ τ = v} :=
  Equiv.subtypeEquiv (Equiv.permCongr e) (fun σ => by
    constructor
    · intro h
      funext b
      simp only [Function.comp_apply, Equiv.permCongr_apply]
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (e.symm b)
    · intro h
      funext a
      have h' := congrFun h (e a)
      simpa only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply] using h')

theorem gaussian_entry_finite_pairing_integrable {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (u v : α → ι) :
    Integrable (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ a, star (x (v a)))
      (standardComplexGaussianProductLaw ι) := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hEq : (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ a, star (x (v a))) =
      fun x => (∏ j, x (u (e j))) * ∏ j, star (x (v (e j))) := by
    funext x
    rw [e.prod_comp (fun a => x (u a)), e.prod_comp (fun a => star (x (v a)))]
  rw [hEq]
  exact gaussian_entry_pairing_product_integrable (Fintype.card α) (u ∘ e) (v ∘ e)

theorem gaussian_entry_finite_pairing_integral {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (u v : α → ι) :
    (∫ x : ι → ℂ, (∏ a, x (u a)) * ∏ a, star (x (v a))
      ∂standardComplexGaussianProductLaw ι) =
      (Fintype.card {σ : Equiv.Perm α // u ∘ σ = v} : ℂ) := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hEq : (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ a, star (x (v a))) =
      fun x => (∏ j, x (u (e j))) * ∏ j, star (x (v (e j))) := by
    funext x
    rw [e.prod_comp (fun a => x (u a)), e.prod_comp (fun a => star (x (v a)))]
  rw [hEq, gaussian_entry_pairing_integral]
  exact_mod_cast Fintype.card_congr (matchingPermutationCongr e u v)

theorem gaussian_entry_finite_wick_pairings {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (u v : α → ι) :
    (∫ x : ι → ℂ, (∏ a, x (u a)) * ∏ a, star (x (v a))
      ∂standardComplexGaussianProductLaw ι) =
      ∑ σ : Equiv.Perm α, ∏ a, if u (σ a) = v a then (1 : ℂ) else 0 := by
  rw [gaussian_entry_finite_pairing_integral, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro σ _
  rw [finite_complex_indicator_product]
  simp only [funext_iff, Function.comp_apply]

end CircularLaw
