import CircularLaw.GaussianFinitePairings

/-!
# Wick pairings between two distinct finite position types

Direct and conjugate positions of a matrix word are different subtypes.
A bijection between them is the actual matching; no common numbering is
part of the formula. Transport from the existing permutation formula
retains every matching, including repeated entry labels.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def matchingBijectionsEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃ (α ≃ β) where
  toFun σ := σ.symm.trans e
  invFun τ := (τ.trans e.symm).symm
  left_inv σ := by ext a; simp
  right_inv τ := by ext a; simp

theorem gaussian_entry_bijection_integrable {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] (e : α ≃ β) (u : α → ι) (v : β → ι) :
    Integrable (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ b, star (x (v b)))
      (standardComplexGaussianProductLaw ι) := by
  have hEq : (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ b, star (x (v b))) =
      fun x => (∏ a, x (u a)) * ∏ a, star (x (v (e a))) := by
    funext x
    rw [e.prod_comp (fun b => star (x (v b)))]
  rw [hEq]
  exact gaussian_entry_finite_pairing_integrable u (v ∘ e)

theorem gaussian_entry_bijection_wick {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] (e : α ≃ β) (u : α → ι) (v : β → ι) :
    (∫ x : ι → ℂ, (∏ a, x (u a)) * ∏ b, star (x (v b))
      ∂standardComplexGaussianProductLaw ι) =
      ∑ τ : α ≃ β, ∏ a, if u a = v (τ a) then (1 : ℂ) else 0 := by
  have hEq : (fun x : ι → ℂ => (∏ a, x (u a)) * ∏ b, star (x (v b))) =
      fun x => (∏ a, x (u a)) * ∏ a, star (x (v (e a))) := by
    funext x
    rw [e.prod_comp (fun b => star (x (v b)))]
  rw [hEq, gaussian_entry_finite_wick_pairings]
  rw [← (matchingBijectionsEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  change (∏ a, if u (σ a) = v (e a) then (1 : ℂ) else 0) =
    ∏ a, if u a = v (e (σ.symm a)) then (1 : ℂ) else 0
  rw [← Equiv.prod_comp σ (fun a => if u a = v (e (σ.symm a)) then (1 : ℂ) else 0)]
  simp only [Equiv.symm_apply_apply]

end CircularLaw
