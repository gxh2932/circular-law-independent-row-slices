import CircularLaw.GaussianPairingCount

/-!
# Complex Gaussian Wick formula at every finite order

The expectation is the exact number of label-preserving bijections from
conjugate positions to direct positions, or equivalently a sum over all
permutations of products of Kronecker indicators. Coincident entry labels
retain every matching and give the required factorial multiplicities.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem gaussian_entry_pairing_product_integrable {ι : Type*} [Fintype ι]
    (k : ℕ) (u v : Fin k → ι) :
    Integrable (fun x : ι → ℂ => (∏ j, x (u j)) * ∏ j, star (x (v j)))
      (standardComplexGaussianProductLaw ι) := by
  have hWord : gaussianEntryWord (List.ofFn u) (List.ofFn v) =
      fun x => (∏ j, x (u j)) * ∏ j, star (x (v j)) := by
    funext x
    simp [gaussianEntryWord, List.map_ofFn, List.prod_ofFn]
  rw [← hWord]
  exact gaussian_entry_word_integrable (List.ofFn u) (List.ofFn v)

theorem gaussian_entry_pairing_integral {ι : Type*} [Fintype ι]
    (k : ℕ) (u v : Fin k → ι) :
    (∫ x : ι → ℂ, (∏ j, x (u j)) * ∏ j, star (x (v j))
      ∂standardComplexGaussianProductLaw ι) =
      (Fintype.card {e : Equiv.Perm (Fin k) // u ∘ e = v} : ℂ) := by
  have hWord (x : ι → ℂ) :
      (∏ j, x (u j)) * ∏ j, star (x (v j)) =
        gaussianEntryWord (List.ofFn u) (List.ofFn v) x := by
    simp [gaussianEntryWord, List.map_ofFn, List.prod_ofFn]
  simp only [hWord, gaussian_entry_word_integral, list_ofFn_count_eq_fiber_card]
  have hCount := function_matching_permutation_card u v
  simp only [Fintype.card_subtype] at hCount ⊢
  by_cases h : ∀ i, (Finset.univ.filter (fun j => u j = i)).card =
      (Finset.univ.filter (fun j => v j = i)).card
  · rw [if_pos h] at hCount ⊢
    rw [hCount, Nat.cast_prod]
  · rw [if_neg h] at hCount ⊢
    rw [hCount, Nat.cast_zero]

theorem finite_complex_indicator_product {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    (∏ a, if p a then (1 : ℂ) else 0) = if ∀ a, p a then 1 else 0 := by
  by_cases h : ∀ a, p a
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨a, ha⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

theorem gaussian_entry_wick_pairings {ι : Type*} [Fintype ι]
    (k : ℕ) (u v : Fin k → ι) :
    (∫ x : ι → ℂ, (∏ j, x (u j)) * ∏ j, star (x (v j))
      ∂standardComplexGaussianProductLaw ι) =
      ∑ e : Equiv.Perm (Fin k), ∏ j, if u (e j) = v j then (1 : ℂ) else 0 := by
  rw [gaussian_entry_pairing_integral, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  rw [finite_complex_indicator_product]
  simp only [funext_iff, Function.comp_apply]
  split_ifs <;> rfl

theorem gaussian_entry_pairing_integral_norm_bound {ι : Type*} [Fintype ι]
    (k : ℕ) (u v : Fin k → ι) :
    ‖∫ x : ι → ℂ, (∏ j, x (u j)) * ∏ j, star (x (v j))
      ∂standardComplexGaussianProductLaw ι‖ ≤ (k.factorial : ℝ) := by
  rw [gaussian_entry_pairing_integral, Complex.norm_natCast]
  have h := Fintype.card_subtype_le (fun e : Equiv.Perm (Fin k) => u ∘ e = v)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  exact_mod_cast h

end CircularLaw
