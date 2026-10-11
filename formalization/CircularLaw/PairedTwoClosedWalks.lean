import CircularLaw.PairedClosedWalk
import CircularLaw.GaussianWordPairingCounts

/-!
# A pairing between two closed walks loses a free vertex class

The two walks may have different lengths and direct/adjoint patterns.
Within each successor orbit the quotient graph is reachable. A matched
pair crossing the walk blocks supplies a bridge, so the whole quotient
is connected and has at most `pairs+1` vertex classes rather than the
product normalization `pairs+2`.
-/

noncomputable section
open Classical

namespace CircularLaw

def permutationSumHom (α β : Type*) :
    Equiv.Perm α × Equiv.Perm β →* Equiv.Perm (α ⊕ β) where
  toFun σ := Equiv.sumCongr σ.1 σ.2
  map_one' := by ext a; cases a <;> rfl
  map_mul' := by intro σ τ; ext a; cases a <;> rfl

theorem sum_permutation_same_cycle_left {α β : Type*} (ρ : Equiv.Perm α) (τ : Equiv.Perm β)
    {a b : α} (h : ρ.SameCycle a b) :
    Equiv.Perm.SameCycle (Equiv.sumCongr ρ τ) (Sum.inl a) (Sum.inl b) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  change ((permutationSumHom α β (ρ, τ)) ^ m) (Sum.inl a) = Sum.inl b
  rw [← map_zpow]
  change Sum.inl ((ρ ^ m) a) = Sum.inl b
  rw [hm]

theorem sum_permutation_same_cycle_right {α β : Type*} (ρ : Equiv.Perm α) (τ : Equiv.Perm β)
    {a b : β} (h : τ.SameCycle a b) :
    Equiv.Perm.SameCycle (Equiv.sumCongr ρ τ) (Sum.inr a) (Sum.inr b) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  change ((permutationSumHom α β (ρ, τ)) ^ m) (Sum.inr a) = Sum.inr b
  rw [← map_zpow]
  change Sum.inr ((τ ^ m) a) = Sum.inr b
  rw [hm]

def sumWalkBlock {α β : Type*} : α ⊕ β → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

theorem paired_walk_pair_reachable {α P : Type*} (ρ : Equiv.Perm α)
    (p q : P → α) (a : P) :
    (pairedWalkGraph ρ p q).Reachable (pairedWalkClass ρ p q (p a))
      (pairedWalkClass ρ p q (q a)) := by
  rw [← paired_walk_class_end ρ p q a]
  exact finite_labeled_endpoints_reachable _ _ a

theorem paired_two_walk_graph_connected {α β P : Type*}
    (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (p q : P → α ⊕ β)
    (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v)
    (hLeft : ∀ a b, ρ.SameCycle a b) (hRight : ∀ a b, τ.SameCycle a b)
    (hCross : ∃ a, sumWalkBlock (p a) ≠ sumWalkBlock (q a)) :
    (pairedWalkGraph (Equiv.sumCongr ρ τ) p q).Connected := by
  let σ : Equiv.Perm (α ⊕ β) := Equiv.sumCongr ρ τ
  have hWithinLeft (a b : α) :
      (pairedWalkGraph σ p q).Reachable (pairedWalkClass σ p q (Sum.inl a))
        (pairedWalkClass σ p q (Sum.inl b)) :=
    paired_walk_graph_same_cycle_reachable σ p q hCover
      (sum_permutation_same_cycle_left ρ τ (hLeft a b))
  have hWithinRight (a b : β) :
      (pairedWalkGraph σ p q).Reachable (pairedWalkClass σ p q (Sum.inr a))
        (pairedWalkClass σ p q (Sum.inr b)) :=
    paired_walk_graph_same_cycle_reachable σ p q hCover
      (sum_permutation_same_cycle_right ρ τ (hRight a b))
  obtain ⟨a, hCross⟩ := hCross
  have hBridge := paired_walk_pair_reachable σ p q a
  have hAll (v : α ⊕ β) :
      (pairedWalkGraph σ p q).Reachable (pairedWalkClass σ p q (p a))
        (pairedWalkClass σ p q v) := by
    cases hp : p a with
    | inl u =>
      cases hq : q a with
      | inl t => exact False.elim (hCross (by simp only [hp, hq, sumWalkBlock]))
      | inr t =>
        rw [hp, hq] at hBridge
        cases v with
        | inl v => exact hWithinLeft u v
        | inr v => exact hBridge.trans (hWithinRight t v)
    | inr u =>
      cases hq : q a with
      | inl t =>
        rw [hp, hq] at hBridge
        cases v with
        | inl v => exact hBridge.trans (hWithinLeft t v)
        | inr v => exact hWithinRight u v
      | inr t => exact False.elim (hCross (by simp only [hp, hq, sumWalkBlock]))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨pairedWalkClass σ p q (p a), ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | h v => exact hAll v

theorem paired_two_walk_class_count_bound {α β P : Type*} [Fintype α] [Fintype β]
    [Fintype P] (ρ : Equiv.Perm α) (τ : Equiv.Perm β) (p q : P → α ⊕ β)
    (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v)
    (hLeft : ∀ a b, ρ.SameCycle a b) (hRight : ∀ a b, τ.SameCycle a b)
    (hCross : ∃ a, sumWalkBlock (p a) ≠ sumWalkBlock (q a)) :
    relationClassCount (pairedWalkRelation (Equiv.sumCongr ρ τ) p q) ≤ Fintype.card P + 1 := by
  exact finite_labeled_vertex_card_bound _ _
    (paired_two_walk_graph_connected ρ τ p q hCover hLeft hRight hCross)

theorem gaussian_two_word_cross_exponent_bound (k l : ℕ)
    (b : Fin (k + 1) ⊕ Fin (l + 1) → Bool) (e : GaussianWordPairing b)
    (hCross : ∃ a : GaussianDirectPositions b, sumWalkBlock a.val ≠ sumWalkBlock (e a).val) :
    gaussianWordVertexExponent b (Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))) e ≤
      Fintype.card (GaussianDirectPositions b) + 1 := by
  exact paired_two_walk_class_count_bound _ _ _ _
    (gaussian_word_pairing_covers_positions b e) (fin_rotate_same_cycle k)
    (fin_rotate_same_cycle l) hCross

end CircularLaw
