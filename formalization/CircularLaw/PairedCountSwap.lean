import CircularLaw.SeparatedPairMean

/-!
# A codomain swap changes the separated-pair count by at most two

The pair count is Lipschitz for changes to arbitrary coordinate samples.
For an injective sample, a transposition changes at most two coordinates,
so the literal statistic changes by at most two.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def pairedSeparatedCount {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (a : Fin d ⊕ Fin d → Fin n) : ℝ :=
  ∑ j, if ρ ≤ ‖y (a (Sum.inr j)) - y (a (Sum.inl j))‖ then (1 : ℝ) else 0

theorem paired_separated_count_eq_card {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (e : Fin d ⊕ Fin d ↪ Fin n) :
    pairedSeparatedCount y ρ e = ((pairedSeparatedCoordinates y ρ e).card : ℝ) :=
  (paired_separated_coordinates_cast_sum y ρ e).symm

theorem paired_separated_count_lipschitz {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (a b : Fin d ⊕ Fin d → Fin n) :
    |pairedSeparatedCount y ρ a - pairedSeparatedCount y ρ b| ≤
      ((Finset.univ.filter (fun j : Fin d ⊕ Fin d => a j ≠ b j)).card : ℝ) := by
  have hPoint (j : Fin d) :
      |(if ρ ≤ ‖y (a (Sum.inr j)) - y (a (Sum.inl j))‖ then (1 : ℝ) else 0) -
        (if ρ ≤ ‖y (b (Sum.inr j)) - y (b (Sum.inl j))‖ then (1 : ℝ) else 0)| ≤
      (if a (Sum.inl j) ≠ b (Sum.inl j) then (1 : ℝ) else 0) +
        (if a (Sum.inr j) ≠ b (Sum.inr j) then (1 : ℝ) else 0) := by
    have hOne : |(if ρ ≤ ‖y (a (Sum.inr j)) - y (a (Sum.inl j))‖ then (1 : ℝ) else 0) -
        (if ρ ≤ ‖y (b (Sum.inr j)) - y (b (Sum.inl j))‖ then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    by_cases hL : a (Sum.inl j) = b (Sum.inl j)
    · by_cases hR : a (Sum.inr j) = b (Sum.inr j)
      · simp only [hL, hR, sub_self, abs_zero, ne_eq, not_true_eq_false, if_false, add_zero]
        exact le_refl 0
      · simpa only [hL, ne_eq, not_true_eq_false, if_false, hR, not_false_eq_true, if_true,
          zero_add] using hOne
    · by_cases hR : a (Sum.inr j) = b (Sum.inr j)
      · simpa only [hL, ne_eq, not_false_eq_true, if_true, hR, not_true_eq_false, if_false,
          add_zero] using hOne
      · simp only [ne_eq, hL, hR, not_false_eq_true, if_true]
        linarith
  unfold pairedSeparatedCount
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(if ρ ≤ ‖y (a (Sum.inr j)) - y (a (Sum.inl j))‖ then (1 : ℝ) else 0) -
        (if ρ ≤ ‖y (b (Sum.inr j)) - y (b (Sum.inl j))‖ then (1 : ℝ) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin d, ((if a (Sum.inl j) ≠ b (Sum.inl j) then (1 : ℝ) else 0) +
        (if a (Sum.inr j) ≠ b (Sum.inr j) then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun j _ => hPoint j)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.card_filter, Fintype.sum_sum_type]
      push_cast
      rfl

theorem injection_swap_changed_coordinates_card_le_two {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ↪ β) (a b : β) :
    (Finset.univ.filter (fun j : α => e j ≠ Equiv.swap a b (e j))).card ≤ 2 := by
  let S := Finset.univ.filter (fun j : α => e j ≠ Equiv.swap a b (e j))
  have hSubset : S.map e ⊆ ({a, b} : Finset β) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hz
    have hNe : Equiv.swap a b (e j) ≠ e j := (Finset.mem_filter.mp hj).2.symm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      Equiv.eq_or_eq_of_swap_apply_ne_self hNe
  calc
    _ = (S.map e).card := (Finset.card_map _).symm
    _ ≤ ({a, b} : Finset β).card := Finset.card_le_card hSubset
    _ ≤ 2 := by
      by_cases h : a = b <;> simp [h]

theorem paired_separated_count_swap_bound {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (e : Fin d ⊕ Fin d ↪ Fin n) (a b : Fin n) :
    |pairedSeparatedCount y ρ e -
      pairedSeparatedCount y ρ (e.trans (Equiv.swap a b).toEmbedding)| ≤ 2 := by
  exact (paired_separated_count_lipschitz y ρ e (e.trans (Equiv.swap a b).toEmbedding)).trans
    (by exact_mod_cast injection_swap_changed_coordinates_card_le_two e a b)

end CircularLaw
