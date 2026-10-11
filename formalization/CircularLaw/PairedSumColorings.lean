import CircularLaw.PairedClosedWalk

/-!
# Separate paired walks have additive vertex-class counts

Their endpoint constraints act separately on the two position blocks.
Colorings are therefore exactly pairs of one-block colorings. Counting
binary colorings proves additivity of quotient-class counts, retaining
fixed vertices, loops and repeated equalities.
-/

noncomputable section
open Classical

namespace CircularLaw

def pairedSumColoringsEquiv {α β P Q V : Type*} (ρ : Equiv.Perm α) (τ : Equiv.Perm β)
    (p q : P → α) (r s : Q → β) :
    {f : α ⊕ β → V // ∀ a : P ⊕ Q,
      f (Sum.map p r a) = f ((Equiv.sumCongr ρ τ) (Sum.map q s a)) ∧
        f ((Equiv.sumCongr ρ τ) (Sum.map p r a)) = f (Sum.map q s a)} ≃
      {f : α → V // ∀ a, f (p a) = f (ρ (q a)) ∧ f (ρ (p a)) = f (q a)} ×
        {f : β → V // ∀ a, f (r a) = f (τ (s a)) ∧ f (τ (r a)) = f (s a)} where
  toFun f := (⟨fun a => f.val (Sum.inl a), fun a => f.property (Sum.inl a)⟩,
    ⟨fun a => f.val (Sum.inr a), fun a => f.property (Sum.inr a)⟩)
  invFun f := ⟨Sum.elim f.1.val f.2.val, by
    rintro (a | a)
    · exact f.1.property a
    · exact f.2.property a⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    cases a <;> rfl
  right_inv f := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem paired_walk_sum_class_count {α β P Q : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (p q : P → α) (r s : Q → β) :
    relationClassCount (pairedWalkRelation (Equiv.sumCongr ρ τ) (Sum.map p r) (Sum.map q s)) =
      relationClassCount (pairedWalkRelation ρ p q) + relationClassCount (pairedWalkRelation τ r s) := by
  have h := Nat.card_congr (pairedSumColoringsEquiv (V := Fin 2) ρ τ p q r s)
  have hL := paired_walk_coloring_card ρ p q 2
  have hR := paired_walk_coloring_card τ r s 2
  have hS := paired_walk_coloring_card (Equiv.sumCongr ρ τ) (Sum.map p r) (Sum.map q s) 2
  rw [← Nat.card_eq_fintype_card] at hL hR hS
  rw [Nat.card_prod, hL, hR, hS, ← pow_add] at h
  exact Nat.pow_right_injective (by omega : 1 < 2) h

theorem paired_walk_relation_reindex {α P Q : Type*} (e : P ≃ Q) (ρ : Equiv.Perm α)
    (p q : Q → α) :
    pairedWalkRelation ρ (p ∘ e) (q ∘ e) = pairedWalkRelation ρ p q := by
  funext v w
  apply propext
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, ?_⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ha

end CircularLaw
